use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{DestOperand, MemAccessSize, Operand, Operation};

use crate::analysis::AnalysisCtx;
use crate::analysis_find::{EntryOf, FunctionFinder, entry_of_until};
use crate::util::{
    ControlExt, ExecStateExt, bumpvec_with_capacity, is_stack_address, single_result_assign,
};

pub(crate) struct GameSettings<'e, Va: VirtualAddress> {
    pub game_setting_groups: Option<Operand<'e>>,
    pub update_game_setting_int: Option<Va>,
    pub update_game_setting_bool: Option<Va>,
}

/// GameSettingValue kinds that the update functions store to their temporary value.
const SETTING_KIND_BOOL: u64 = 1;
const SETTING_KIND_INT: u64 = 2;

pub(crate) fn game_settings<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> GameSettings<'e, E::VirtualAddress> {
    // Settings are stored in game_setting_groups, a map of group name -> map of
    // setting name -> GameSetting. Each setting has a getter that looks it up once and
    // caches the pointer:
    //  get_key_scroll_setting() {
    //      static GameSetting *cached;
    //      if (cached == null) {
    //          map = get_speed_settings_section();
    //          setting = find_string_keyed_map_value(map, BwString("m_kscroll"));
    //          if (setting == null) {
    //              setting = insert_game_setting_into_map(map, "m_kscroll", ...)
    //          }
    //          cached = setting;
    //      }
    //      return cached;
    //  }
    //  get_speed_settings_section() {
    //      // Some builds use the return value of get_game_setting_groups(), others call it
    //      // only for its static initialization and use the constant directly.
    //      return get_or_create_game_setting_group(get_game_setting_groups(), "speed");
    //  }
    //
    // OptionsMenuPopup_handle_reset_to_defaults, one of the callers of
    // get_key_scroll_setting, uses the getters to write default values, which is where
    // the update functions are found from:
    //  value = 3;
    //  update_game_setting_int(get_key_scroll_setting(), &value, 1);
    //  ...
    //  bool_value = true;
    //  update_game_setting_bool(get_hardware_cursor_setting(), &bool_value, 1);
    let binary = actx.binary;
    let funcs = functions.functions();
    let mut result = GameSettings {
        game_setting_groups: None,
        update_game_setting_int: None,
        update_game_setting_bool: None,
    };
    let str_refs = functions.string_refs(actx, b"m_kscroll\0");
    let mut get_key_scroll_setting = None;
    for str_ref in &str_refs {
        let use_address = str_ref.use_address;
        let string_address = str_ref.string_address;
        let res = entry_of_until(binary, &funcs, use_address, |entry| {
            key_scroll_setting_groups(actx, entry, use_address, string_address)
        }).into_option_with_entry();
        if let Some((entry, groups)) = res {
            single_result_assign(Some(entry), &mut get_key_scroll_setting);
            single_result_assign(Some(groups), &mut result.game_setting_groups);
        }
    }
    let Some(get_key_scroll_setting) = get_key_scroll_setting else { return result };

    let bump = &actx.bump;
    let mut candidates = bumpvec_with_capacity(0x20, bump);
    let callers = functions.find_callers(actx, get_key_scroll_setting);
    for caller in callers {
        let _ = entry_of_until(binary, &funcs, caller, |entry| {
            setting_write_candidates(actx, entry, caller, get_key_scroll_setting, &mut candidates)
        });
    }
    for &(func, called_with_key_scroll) in candidates.iter() {
        match setting_write_kind(actx, func) {
            Some(SETTING_KIND_INT) if called_with_key_scroll => {
                single_result_assign(Some(func), &mut result.update_game_setting_int);
            }
            Some(SETTING_KIND_BOOL) => {
                single_result_assign(Some(func), &mut result.update_game_setting_bool);
            }
            _ => (),
        }
    }
    result
}

/// If `entry` is get_key_scroll_setting, returns game_setting_groups.
fn key_scroll_setting_groups<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    entry: E::VirtualAddress,
    use_address: E::VirtualAddress,
    string_address: E::VirtualAddress,
) -> EntryOf<Operand<'e>> {
    // get_key_scroll_setting passes the result of get_speed_settings_section as `this` to
    // find_string_keyed_map_value / insert_game_setting_into_map, along with a stack
    // pointer to BwString. Some builds instead pass `this` and the "m_kscroll" literal to
    // a function that does both.
    // Tag each call result with custom(call_index) to find the section getter.
    struct Analyzer<'acx, 'e, E: ExecutionState<'e>> {
        use_address: E::VirtualAddress,
        string_address: E::VirtualAddress,
        reached_use: bool,
        calls: BumpVec<'acx, E::VirtualAddress>,
        section_getters: BumpVec<'acx, E::VirtualAddress>,
    }

    impl<'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'acx, 'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            if ctrl.instruction_contains_address(self.use_address) {
                self.reached_use = true;
            }
            if let Operation::Call(dest) = *op {
                let Some(dest) = ctrl.resolve_va(dest) else { return };
                let this = ctrl.resolve_register(1);
                if let Some(idx) = this.if_custom() {
                    let arg1 = ctrl.resolve_arg_thiscall(0);
                    if is_stack_address(arg1) ||
                        arg1.if_constant() == Some(self.string_address.as_u64())
                    {
                        if let Some(&getter) = self.calls.get(idx as usize) {
                            if !self.section_getters.contains(&getter) {
                                self.section_getters.push(getter);
                            }
                        }
                    }
                }
                let ctx = ctrl.ctx();
                ctrl.skip_call_preserve_esp();
                ctrl.set_register(0, ctx.custom(self.calls.len() as u32));
                self.calls.push(dest);
            }
        }
    }

    let bump = &actx.bump;
    let mut analyzer = Analyzer::<E> {
        use_address,
        string_address,
        reached_use: false,
        calls: bumpvec_with_capacity(0x10, bump),
        section_getters: bumpvec_with_capacity(0x4, bump),
    };
    let mut analysis = FuncAnalysis::new(actx.binary, actx.ctx, entry);
    analysis.analyze(&mut analyzer);
    if !analyzer.reached_use {
        return EntryOf::Retry;
    }
    for &getter in analyzer.section_getters.iter() {
        if let Some(groups) = section_getter_groups(actx, getter) {
            return EntryOf::Ok(groups);
        }
    }
    EntryOf::Stop
}

/// Checks that `func` calls a function with `this` = constant global, arg1 = stack pointer
/// (the group name string), and returns the constant.
/// The constant may also come from a call to a function returning it.
fn section_getter_groups<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    func: E::VirtualAddress,
) -> Option<Operand<'e>> {
    struct Analyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
        actx: &'a AnalysisCtx<'e, E>,
        calls: BumpVec<'acx, E::VirtualAddress>,
        result: Option<Operand<'e>>,
    }

    impl<'a, 'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'a, 'acx, 'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            if let Operation::Call(dest) = *op {
                let Some(dest) = ctrl.resolve_va(dest) else { return };
                let this = ctrl.resolve_register(1);
                if is_stack_address(ctrl.resolve_arg_thiscall(0)) {
                    let groups = this.if_constant().or_else(|| {
                        let idx = this.if_custom()?;
                        let &func = self.calls.get(idx as usize)?;
                        returned_constant(self.actx, func)
                    });
                    if let Some(groups) = groups {
                        let data = self.actx.binary_sections.data;
                        let addr = E::VirtualAddress::from_u64(groups);
                        if addr >= data.virtual_address &&
                            addr < data.virtual_address + data.virtual_size
                        {
                            self.result = Some(ctrl.ctx().constant(groups));
                            ctrl.end_analysis();
                            return;
                        }
                    }
                }
                let ctx = ctrl.ctx();
                ctrl.skip_call_preserve_esp();
                ctrl.set_register(0, ctx.custom(self.calls.len() as u32));
                self.calls.push(dest);
            }
        }
    }

    let mut analyzer = Analyzer::<E> {
        actx,
        calls: bumpvec_with_capacity(0x8, &actx.bump),
        result: None,
    };
    let mut analysis = FuncAnalysis::new(actx.binary, actx.ctx, func);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

/// Returns the constant `func` returns if every return returns the same constant.
fn returned_constant<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    func: E::VirtualAddress,
) -> Option<u64> {
    struct Analyzer<'e, E: ExecutionState<'e>> {
        result: Option<u64>,
        failed: bool,
        phantom: std::marker::PhantomData<(*const E, &'e ())>,
    }

    impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            if let Operation::Return(..) = *op {
                let value = ctrl.resolve_register(0).if_constant();
                if value.is_none() || (self.result.is_some() && self.result != value) {
                    self.failed = true;
                    ctrl.end_analysis();
                    return;
                }
                self.result = value;
            }
        }
    }

    let mut analyzer = Analyzer::<E> {
        result: None,
        failed: false,
        phantom: Default::default(),
    };
    let mut analysis = FuncAnalysis::new(actx.binary, actx.ctx, func);
    analysis.analyze(&mut analyzer);
    if analyzer.failed {
        None
    } else {
        analyzer.result
    }
}

/// Collects functions called as `f(this = setting getter result, &stack_value, 1)` from a
/// caller of get_key_scroll_setting to `out` as `(f, called_with_key_scroll_setting)`.
fn setting_write_candidates<'acx, 'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    entry: E::VirtualAddress,
    call_site: E::VirtualAddress,
    get_key_scroll_setting: E::VirtualAddress,
    out: &mut BumpVec<'acx, (E::VirtualAddress, bool)>,
) -> EntryOf<()> {
    struct Analyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
        call_site: E::VirtualAddress,
        get_key_scroll_setting: E::VirtualAddress,
        reached_call_site: bool,
        out: &'a mut BumpVec<'acx, (E::VirtualAddress, bool)>,
    }

    impl<'a, 'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'a, 'acx, 'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            if let Operation::Call(dest) = *op {
                if ctrl.instruction_contains_address(self.call_site) {
                    self.reached_call_site = true;
                }
                let Some(dest) = ctrl.resolve_va(dest) else { return };
                let ctx = ctrl.ctx();
                // custom(0) = get_key_scroll_setting() result, custom(1) = any other call
                if dest == self.get_key_scroll_setting {
                    ctrl.skip_call_preserve_esp();
                    ctrl.set_register(0, ctx.custom(0));
                    return;
                }
                let this = ctrl.resolve_register(1);
                if this.if_custom().is_some() &&
                    is_stack_address(ctrl.resolve_arg_thiscall(0)) &&
                    ctrl.resolve_arg_thiscall_u8(1).if_constant() == Some(1)
                {
                    let is_key_scroll = this == ctx.custom(0);
                    match self.out.iter_mut().find(|x| x.0 == dest) {
                        Some(old) => old.1 |= is_key_scroll,
                        None => self.out.push((dest, is_key_scroll)),
                    }
                }
                ctrl.skip_call_preserve_esp();
                ctrl.set_register(0, ctx.custom(1));
            }
        }
    }

    let mut analyzer = Analyzer::<E> {
        call_site,
        get_key_scroll_setting,
        reached_call_site: false,
        out,
    };
    let mut analysis = FuncAnalysis::new(actx.binary, actx.ctx, entry);
    analysis.analyze(&mut analyzer);
    if analyzer.reached_call_site {
        EntryOf::Ok(())
    } else {
        EntryOf::Retry
    }
}

/// Checks that `func` looks like `update_game_setting_x(this, *const value, defer)` and
/// returns the GameSettingValue kind it uses.
///
/// The functions copy the value to a temporary GameSettingValue on stack
/// `{ kind: u32, value }` (value aligned to word size), check the validator
/// tagged pointer `this.validator & 1`, and write `this.persistence_pending`.
fn setting_write_kind<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    func: E::VirtualAddress,
) -> Option<u64> {
    struct Analyzer<'acx, 'e, E: ExecutionState<'e>> {
        this: Operand<'e>,
        value_ptr: Operand<'e>,
        // (stack offset, constant) of u32 constant stores to stack
        stack_constants: BumpVec<'acx, (u64, u64)>,
        // (stack offset, size) of `*value_ptr` stores to stack
        value_copies: BumpVec<'acx, (u64, MemAccessSize)>,
        checks_validator: bool,
        writes_persistence_pending: bool,
        phantom: std::marker::PhantomData<E>,
    }

    impl<'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'acx, 'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            let ctx = ctrl.ctx();
            match *op {
                Operation::Move(DestOperand::Memory(ref mem), value) => {
                    let dest = ctrl.resolve_mem(mem);
                    let (base, offset) = dest.address();
                    if base == ctx.register(4) {
                        let value = ctrl.resolve(value);
                        if let Some(c) = value.if_constant() {
                            if mem.size == MemAccessSize::Mem32 {
                                self.stack_constants.push((offset, c));
                            }
                        } else if let Some(value_mem) = value.if_memory() {
                            if value_mem.address() == (self.value_ptr, 0) {
                                self.value_copies.push((offset, value_mem.size));
                            }
                        }
                    } else if mem.size == MemAccessSize::Mem8 &&
                        dest.address() ==
                            (self.this, E::struct_layouts().game_setting_persistence_pending())
                    {
                        self.writes_persistence_pending = true;
                    }
                }
                Operation::Jump { condition, .. } => {
                    let condition = ctrl.resolve(condition);
                    let validator = E::struct_layouts().game_setting_validator();
                    let has_validator_check = condition.iter()
                        .any(|x| x.if_mem8_offset(validator) == Some(self.this));
                    if has_validator_check {
                        self.checks_validator = true;
                    }
                }
                _ => (),
            }
        }
    }

    let ctx = actx.ctx;
    let bump = &actx.bump;
    let mut analyzer = Analyzer::<E> {
        this: ctx.register(1),
        value_ptr: actx.arg_cache.on_thiscall_entry(0),
        stack_constants: bumpvec_with_capacity(0x10, bump),
        value_copies: bumpvec_with_capacity(0x4, bump),
        checks_validator: false,
        writes_persistence_pending: false,
        phantom: Default::default(),
    };
    let mut analysis = FuncAnalysis::new(actx.binary, ctx, func);
    analysis.analyze(&mut analyzer);
    if !analyzer.checks_validator || !analyzer.writes_persistence_pending {
        return None;
    }
    // The value is stored right after the u32 kind, at the next word-aligned offset,
    // and the size of value read has to agree with the kind.
    // Some builds inline the temporary value's destructor, which sets the kind to 0.
    let mut result = None;
    for &(offset, size) in analyzer.value_copies.iter() {
        let kind_offset = offset.wrapping_sub(E::VirtualAddress::SIZE as u64);
        let mut kinds = analyzer.stack_constants.iter()
            .filter(|x| x.0 == kind_offset && x.1 != 0)
            .map(|x| x.1);
        let kind = kinds.next()?;
        if kinds.any(|x| x != kind) {
            return None;
        }
        let expected_kind = match size {
            MemAccessSize::Mem32 => SETTING_KIND_INT,
            MemAccessSize::Mem8 => SETTING_KIND_BOOL,
            _ => return None,
        };
        if kind != expected_kind || result.is_some_and(|x| x != kind) {
            return None;
        }
        result = Some(kind);
    }
    result
}
