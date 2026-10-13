use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{MemAccessSize, Operand, Operation};

use crate::analysis::AnalysisCtx;
use crate::analysis_find::{EntryOf, FunctionFinder, entry_of_until};
use crate::util::{ControlExt, OperandExt, bumpvec_with_capacity, single_result_assign};

pub(crate) struct StatTxt<'e> {
    pub stat_txt_string_table: Option<Operand<'e>>,
    pub unit_map_name_overrides: Option<Operand<'e>>,
}

pub(crate) fn stat_txt<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> StatTxt<'e> {
    StatTxt {
        stat_txt_string_table: stat_txt_string_table(actx, functions),
        unit_map_name_overrides: unit_map_name_overrides(actx, functions),
    }
}

fn stat_txt_string_table<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<Operand<'e>> {
    // stat_txt is a StringTable object that is loaded from rez/stat_txt.json for the
    // current language when it is first needed:
    //  load_stat_txt_localization() {
    //      if (string_table_is_loaded(&stat_txt_string_table)) {
    //          return;
    //      }
    //      set_string_table_encoding_policy(&stat_txt_string_table, 0, 0);
    //      load_localization_files(
    //          &stat_txt_string_table,
    //          path_join("rez", "stat_txt.json"),
    //          "",
    //      );
    //  }
    //
    // The "stat_txt.json" string is also used by a function that loads the same file
    // to a table which only keeps the string keys, exiting with
    // "Couldn't open rez\stat_txt.json" if that fails. Functions that use the error
    // string are skipped.
    let binary = actx.binary;
    let funcs = functions.functions();
    let error_refs = functions.string_refs(actx, b"Couldn't open rez\\stat_txt.json\0");
    let error_uses = BumpVec::from_iter_in(error_refs.iter().map(|x| x.use_address), &actx.bump);
    let str_refs = functions.string_refs(actx, b"stat_txt.json\0");
    let mut result = None;
    for str_ref in &str_refs {
        let use_address = str_ref.use_address;
        let res = entry_of_until(binary, &funcs, use_address, |entry| {
            string_table_loaded_by_func(actx, entry, use_address, &error_uses)
        }).into_option();
        single_result_assign(res, &mut result);
    }
    result
}

/// Returns the constant that `entry` passes as `this` to several calls, at least one of
/// them made after `use_address`. Fails if `entry` contains any of `excluded_uses`.
fn string_table_loaded_by_func<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    entry: E::VirtualAddress,
    use_address: E::VirtualAddress,
    excluded_uses: &[E::VirtualAddress],
) -> EntryOf<Operand<'e>> {
    struct Analyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
        actx: &'a AnalysisCtx<'e, E>,
        use_address: E::VirtualAddress,
        excluded_uses: &'a [E::VirtualAddress],
        reached_use: bool,
        reached_excluded_use: bool,
        // (`this`, call count, used after use_address)
        this_constants: BumpVec<'acx, (u64, u32, bool)>,
    }

    impl<'a, 'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'a, 'acx, 'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            if ctrl.instruction_contains_address(self.use_address) {
                self.reached_use = true;
            }
            if self.excluded_uses.iter().any(|&x| ctrl.instruction_contains_address(x)) {
                self.reached_excluded_use = true;
            }
            if let Operation::Call(..) = *op {
                let this = ctrl.resolve_register(1);
                if let Some(c) = this.if_constant() {
                    if is_in_data(self.actx, c) {
                        match self.this_constants.iter_mut().find(|x| x.0 == c) {
                            Some(old) => {
                                old.1 += 1;
                                old.2 |= self.reached_use;
                            }
                            None => self.this_constants.push((c, 1, self.reached_use)),
                        }
                    }
                }
                let ctx = ctrl.ctx();
                ctrl.skip_call_preserve_esp();
                ctrl.set_register(0, ctx.new_undef());
            }
        }
    }

    let mut analyzer = Analyzer::<E> {
        actx,
        use_address,
        excluded_uses,
        reached_use: false,
        reached_excluded_use: false,
        this_constants: bumpvec_with_capacity(0x8, &actx.bump),
    };
    let mut analysis = FuncAnalysis::new(actx.binary, actx.ctx, entry);
    analysis.analyze(&mut analyzer);
    if !analyzer.reached_use {
        return EntryOf::Retry;
    }
    if analyzer.reached_excluded_use {
        return EntryOf::Stop;
    }
    let mut candidates = analyzer.this_constants.iter()
        .filter(|x| x.1 >= 2 && x.2);
    match (candidates.next(), candidates.next()) {
        (Some(&(c, ..)), None) => EntryOf::Ok(actx.ctx.constant(c)),
        _ => EntryOf::Stop,
    }
}

fn unit_map_name_overrides<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<Operand<'e>> {
    // get_unit_type_display_name(out, unit_type) {
    //      if (unit_type >= 0xe4) {
    //          return empty string;
    //      }
    //      string_id = unit_map_name_overrides[unit_type];
    //      if (string_id != 0) {
    //          return lookup_map_string(string_id);
    //      }
    //      key = unit_type == 0 ? "FIRST_UNIT_STRING" : "FIRST_UNIT_STRING-" + unit_type;
    //      return lookup_localized_stat_string(key);
    // }
    let binary = actx.binary;
    let funcs = functions.functions();
    let str_refs = functions.string_refs(actx, b"FIRST_UNIT_STRING-\0");
    let mut result = None;
    for str_ref in &str_refs {
        let use_address = str_ref.use_address;
        let res = entry_of_until(binary, &funcs, use_address, |entry| {
            u16_array_read_by_func(actx, entry, use_address)
        }).into_option();
        single_result_assign(res, &mut result);
    }
    result
}

/// Returns `c` if `entry` reads `Mem16[c + x * 2]`, with `c` in .data, as its only such
/// array read.
fn u16_array_read_by_func<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    entry: E::VirtualAddress,
    use_address: E::VirtualAddress,
) -> EntryOf<Operand<'e>> {
    struct Analyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
        actx: &'a AnalysisCtx<'e, E>,
        use_address: E::VirtualAddress,
        reached_use: bool,
        arrays: BumpVec<'acx, u64>,
    }

    impl<'a, 'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'a, 'acx, 'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            if ctrl.instruction_contains_address(self.use_address) {
                self.reached_use = true;
            }
            match *op {
                Operation::Move(_, value) => {
                    let value = ctrl.resolve(value);
                    for part in value.iter() {
                        let Some(mem) = part.if_memory() else { continue };
                        if mem.size != MemAccessSize::Mem16 {
                            continue;
                        }
                        let (base, offset) = mem.address();
                        let is_index = base.if_arithmetic_mul_const(2).is_some() ||
                            base.if_arithmetic_lsh_const(1).is_some();
                        if is_index && is_in_data(self.actx, offset) &&
                            !self.arrays.contains(&offset)
                        {
                            self.arrays.push(offset);
                        }
                    }
                }
                Operation::Call(..) => {
                    let ctx = ctrl.ctx();
                    ctrl.skip_call_preserve_esp();
                    ctrl.set_register(0, ctx.new_undef());
                }
                _ => (),
            }
        }
    }

    let mut analyzer = Analyzer::<E> {
        actx,
        use_address,
        reached_use: false,
        arrays: bumpvec_with_capacity(0x4, &actx.bump),
    };
    let mut analysis = FuncAnalysis::new(actx.binary, actx.ctx, entry);
    analysis.analyze(&mut analyzer);
    if !analyzer.reached_use {
        return EntryOf::Retry;
    }
    match *analyzer.arrays {
        [c] => EntryOf::Ok(actx.ctx.constant(c)),
        _ => EntryOf::Stop,
    }
}

fn is_in_data<'e, E: ExecutionState<'e>>(actx: &AnalysisCtx<'e, E>, value: u64) -> bool {
    let data = actx.binary_sections.data;
    let addr = E::VirtualAddress::from_u64(value);
    addr >= data.virtual_address && addr < data.virtual_address + data.virtual_size
}
