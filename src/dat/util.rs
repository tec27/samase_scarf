use std::cmp::Ordering;

use bumpalo::Bump;
use bumpalo::collections::Vec as BumpVec;
use scarf::analysis::{self, Control};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{ArithOpType, BinaryFile, BinarySection, DestOperand, Operand, Operation, Rva};

use crate::analysis_find::{EntryOf};
use crate::hash_map::{HashMap};
use crate::util::{bumpvec_with_capacity, ControlExt, OptionExt};

/// Queue(*), but also has hash table lookup
/// to remove things from queue.
///
/// (*) Not FIFO though, out order is sorted.
///
/// Assumes that this will be fully built first, and only read
/// from afterwards. (Single HashMap allocation)
///
/// Exists since just using HashSet isn't deterministic.
pub struct UncheckedRefs<'bump> {
    read_pos: u32,
    buf: BumpVec<'bump, Rva>,
    lookup: HashMap<Rva, u32>,
}

impl<'bump> UncheckedRefs<'bump> {
    pub fn new(bump: &'bump Bump) -> UncheckedRefs<'bump> {
        UncheckedRefs {
            read_pos: 0,
            buf: bumpvec_with_capacity(1024, bump),
            lookup: HashMap::default(),
        }
    }

    pub fn push(&mut self, rva: Rva) {
        self.buf.push(rva);
    }

    pub fn pop(&mut self) -> Option<Rva> {
        loop {
            let &rva = self.buf.get(self.read_pos as usize)?;
            self.read_pos += 1;
            // u32::MAX for ones eagerly deleted
            if rva.0 != u32::MAX {
                return Some(rva);
            }
        }
    }

    pub fn build_lookup(&mut self) {
        // Sort so that pop order is consistent.
        // (Push order is not due to code using globals_with_values)
        self.buf.sort_unstable();
        self.lookup.reserve(self.buf.len());
        for (i, &rva) in self.buf.iter().enumerate() {
            self.lookup.insert(rva, i as u32);
        }
    }

    /// Eagerly remove from queue
    pub fn remove(&mut self, rva: Rva) {
        if let Some(idx) = self.lookup.remove(&rva) {
            if let Some(val) = self.buf.get_mut(idx as usize) {
                val.0 = u32::MAX;
            }
        }
    }
}

pub struct InstructionsNeedingVerify<'bump> {
    // Bits 0xc000_0000 in RVA are state
    // 0 = Not checked
    // 0x4000_0000 = Checked, good
    // 0x8000_0000 = Checked, bad
    // RVA itself is at instruction end
    list: BumpVec<'bump, Rva>,
    sorted: bool,
}

pub struct InsVerifyIter<Va: VirtualAddress> {
    list_pos: usize,
    next: Va,
}

const INS_VERIFY_RVA_MASK: u32 = 0x3fff_ffff;

impl<'bump> InstructionsNeedingVerify<'bump> {
    pub fn new(bump: &'bump Bump, capacity: usize) -> InstructionsNeedingVerify<'bump> {
        InstructionsNeedingVerify {
            list: bumpvec_with_capacity(capacity, bump),
            sorted: false,
        }
    }

    /// Rva needs to be at instruction *end*
    pub fn push(&mut self, rva: Rva) {
        debug_assert!(rva.0 & !INS_VERIFY_RVA_MASK == 0);
        debug_assert!(!self.sorted);
        self.list.push(rva);
    }

    pub fn build_lookup(&mut self) {
        if !self.sorted {
            self.list.sort_unstable();
            // There are bunch of duplicates dues to arrays[n] + entry_count == arrays[n + 1]
            // Would be probably better to fix in dat array addition (Currently it just happens
            // to work since the arrays don't get randomly reordered and higher ids go after lower)
            self.list.dedup();
            self.sorted = true;
        }
    }

    /// Returns next unverified address (Not good but not bad either)
    /// `pos` is an 'iterator' that is updated so that next call will always
    /// return a new address. Start with `pos = 0usize`.
    pub fn next_unverified(&mut self, pos: &mut usize) -> Option<Rva> {
        let idx = *pos;
        for (i, &val) in self.list.get(idx..)?.iter().enumerate() {
            if val.0 & !INS_VERIFY_RVA_MASK == 0 {
                *pos = idx + i + 1;
                return Some(val);
            }
        }
        *pos = usize::MAX;
        None
    }

    pub fn finish<'b>(&mut self, bump: &'b Bump) -> BumpVec<'b, Rva> {
        // Expected to have ~5 false positives
        let mut ret = bumpvec_with_capacity(0x10, bump);
        for &rva in &self.list {
            if rva.0 & 0xc000_0000 != 0x4000_0000 {
                ret.push(Rva(rva.0 & INS_VERIFY_RVA_MASK));
            }
        }
        ret
    }

    fn get_rva(&self, index: usize) -> Option<u32> {
        self.list.get(index).map(|x| x.0 & INS_VERIFY_RVA_MASK)
    }
}

impl<Va: VirtualAddress> InsVerifyIter<Va> {
    pub fn empty() -> InsVerifyIter<Va> {
        InsVerifyIter {
            list_pos: 0,
            next: Va::from_u64(0),
        }
    }

    /// Resets for position for branch start.
    pub fn reset(
        &mut self,
        address: Va,
        binary: &BinaryFile<Va>,
        parent: &mut InstructionsNeedingVerify<'_>,
    ) {
        debug_assert!(parent.sorted);
        let rva = binary.rva_32(address);
        if self.quick_reset(address, binary, rva, parent) {
            return;
        }
        let (Ok(start) | Err(start)) = parent.list.binary_search_by(|x| {
            // Since stored rvas are instruction end, if there is one
            // that is equal to argument to this function, don't include it here.
            // (This is upper_bound, not lower_bound like most other bsearches in this crate)
            match x.0 & INS_VERIFY_RVA_MASK <= rva {
                true => Ordering::Less,
                false => Ordering::Greater,
            }
        });
        let next = parent.get_rva(start).map(|x| binary.base() + x)
            .unwrap_or_else(|| Va::from_u64(u64::MAX));
        self.list_pos = start;
        self.next = next;
    }

    /// Tries to reset without doing a binary search.
    fn quick_reset(
        &mut self,
        address: Va,
        binary: &BinaryFile<Va>,
        rva: u32,
        parent: &mut InstructionsNeedingVerify<'_>,
    ) -> bool {
        if address < self.next {
            // Try to check few previous ones if they match
            let mut pos = self.list_pos;
            for i in 0..4 {
                let prev_idx = match pos.checked_sub(1) {
                    Some(s) => s,
                    None => {
                        if i != 0 {
                            self.list_pos = pos;
                            self.next = binary.base() + parent.get_rva(pos).unwrap_or(0);
                        }
                        return true;
                    }
                };
                if let Some(prev) = parent.get_rva(prev_idx) {
                    if prev <= rva {
                        if i != 0 {
                            self.list_pos = pos;
                            self.next = binary.base() + parent.get_rva(pos).unwrap_or(0);
                        }
                        return true;
                    }
                }
                pos = prev_idx;
            }
        } else if self.list_pos != 0 /* skip list_pos == 0 as that's likely from empty() */ {
            // Try to check few following ones
            let mut pos = self.list_pos;
            for _ in 0..4 {
                let next_idx = pos + 1;
                if let Some(next) = parent.get_rva(next_idx) {
                    if next > rva {
                        self.list_pos = next_idx;
                        self.next = binary.base() + next;
                        return true;
                    }
                }
                pos = next_idx;
            }
        }
        false
    }

    /// A cheap check to avoid rest of the work related to instruction end.
    /// The actual 'end' is allowed to be at address less than `address` too.
    #[inline]
    pub fn near_instruction_end(&self, address: Va) -> bool {
        address >= self.next
    }

    pub fn at_instruction_end(
        &mut self,
        address: Va,
        binary: &BinaryFile<Va>,
        parent: &mut InstructionsNeedingVerify<'_>,
    ) {
        if !self.near_instruction_end(address) {
            return;
        }
        let current = match parent.list.get_mut(self.list_pos) {
            Some(s) => s,
            None => return,
        };
        if address == self.next {
            // Ok, good
            current.0 |= 0x4000_0000;
        } else {
            // Bad
            current.0 |= 0x8000_0000;
        }
        self.list_pos += 1;
        self.next = parent.get_rva(self.list_pos).map(|x| binary.base() + x)
            .unwrap_or_else(|| Va::from_u64(u64::MAX));
    }

    pub fn next_address(&self) -> Va {
        self.next
    }
}

pub struct InstructionVerifyOnlyAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    instruction_verify_pos: InsVerifyIter<E::VirtualAddress>,
    instructions_needing_verify: &'a mut InstructionsNeedingVerify<'acx>,
    entry_of: EntryOf<()>,
    text: &'e BinarySection<E::VirtualAddress>,
    rdtsc_tracker: &'a RdtscTracker<'e>,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> InstructionVerifyOnlyAnalyzer<'a, 'acx, 'e, E> {
    pub fn new(
        instructions_needing_verify: &'a mut InstructionsNeedingVerify<'acx>,
        text: &'e BinarySection<E::VirtualAddress>,
        rdtsc_tracker: &'a RdtscTracker<'e>,
    ) -> InstructionVerifyOnlyAnalyzer<'a, 'acx, 'e, E> {
        InstructionVerifyOnlyAnalyzer {
            instruction_verify_pos: InsVerifyIter::empty(),
            instructions_needing_verify,
            entry_of: EntryOf::Retry,
            text,
            rdtsc_tracker,
        }
    }

    pub fn entry_of(&self) -> EntryOf<()> {
        self.entry_of
    }
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    InstructionVerifyOnlyAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let current_instruction_end = ctrl.current_instruction_end();
        let address = ctrl.address();
        if self.instruction_verify_pos.near_instruction_end(current_instruction_end) {
            let instruction_verify_end = current_instruction_end -
                instruction_verify_imm_size(self.text, address);

            let binary = ctrl.binary();
            self.instruction_verify_pos.at_instruction_end(
                instruction_verify_end,
                binary,
                self.instructions_needing_verify,
            );
            self.entry_of = EntryOf::Ok(());
            if self.instruction_verify_pos.next_address() > ctrl.address() + 0x4000 {
                // Assuming that this function won't find anything else.
                ctrl.end_analysis();
            }
        }
        ctrl.aliasing_memory_fix(op);
        if let Operation::Move(ref dest, val, None) = *op {
            if self.rdtsc_tracker.check(ctrl, dest, val) {
                return;
            }
        } else if let Operation::Jump { condition, to } = *op {
            if let Some(to) = ctrl.resolve_va(to) {
                if self.rdtsc_tracker.check_rdtsc_jump(ctrl, condition, to) {
                    return;
                }
            }
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        let address = ctrl.address();
        self.instruction_verify_pos.reset(
            address,
            ctrl.binary(),
            self.instructions_needing_verify,
        );
    }
}

/// Reads bytes for `address` and forwards to x86_64_globals::immediate_size_approx.
/// x86_64_globals::immediate_size_approx is currently 64bit only.
pub fn instruction_verify_imm_size<Va: VirtualAddress>(
    text: &BinarySection<Va>,
    address: Va,
) -> u32 {
    assert!(Va::SIZE == 8);
    let text_offset = (address.as_u64()).wrapping_sub(text.virtual_address.as_u64()) as usize;
    if let Some(instruction_bytes) = Some(()).and_then(|()| {
        let bytes = text.data.get(text_offset..)?.get(..0x10)?;
        bytes.try_into().ok()
    }) {
        // Assuming that the x86_64_globals array is fine for 32bit too, and that
        // 0f opcodes etc don't matter.
        crate::x86_64_globals::immediate_size_approx(instruction_bytes) as u32
    } else {
        0
    }
}

/// Stateless, can be reused by multiple analysis runs.
pub struct RdtscTracker<'e> {
    rdtsc_custom: Operand<'e>,
    custom_no_mask: Operand<'e>,
}

impl<'e> RdtscTracker<'e> {
    pub fn new(rdtsc_custom: Operand<'e>) -> RdtscTracker<'e> {
        RdtscTracker {
            rdtsc_custom,
            custom_no_mask: Operand::and_masked(rdtsc_custom).0,
        }
    }

    /// Special case rdtsc to move Custom() that will be checked
    /// later on in jumps.
    ///
    /// Call on Operation::Move(dest, val, None).
    /// Returns true if the operation was skipped.
    #[inline]
    pub fn check<A: analysis::Analyzer<'e>>(
        &self,
        ctrl: &mut Control<'e, '_, '_, A>,
        dest: &DestOperand<'e>,
        val: Operand<'e>,
    ) -> bool {
        if val.is_undefined() {
            self.check_move_main(ctrl, dest)
        } else {
            false
        }
    }

    fn check_move_main<A: analysis::Analyzer<'e>>(
        &self,
        ctrl: &mut Control<'e, '_, '_, A>,
        dest: &DestOperand<'e>,
    ) -> bool {
        let binary = ctrl.binary();
        let ins_address = ctrl.address();
        if let Ok(slice) = binary.slice_from_address(ins_address, 2) {
            if slice == &[0x0f, 0x31] {
                ctrl.move_resolved(dest, self.rdtsc_custom);
                ctrl.skip_operation();
                return true;
            }
        }
        false
    }

    /// If this is jump on `rdtsc mod C`, assume it to be unconditional, patch it to
    /// be unconditional and skip the non-jump branch.
    pub fn check_rdtsc_jump<A: analysis::Analyzer<'e>>(
        &self,
        ctrl: &mut Control<'e, '_, '_, A>,
        condition: Operand<'e>,
        to: <A::Exec as ExecutionState<'e>>::VirtualAddress,
    ) -> bool {
        let is_rdtsc_jump = condition.if_arithmetic_gt()
            .and_either_other(Operand::if_constant)
            .and_then(|x| {
                if let Some((l, r)) = x.if_arithmetic_and() {
                    // Modulo compiled to `x & c`
                    r.if_constant().filter(|&c| c.wrapping_add(1) & c == 0)?;
                    if l == self.custom_no_mask {
                        Some(())
                    } else {
                        None
                    }
                } else if let Some((l, r)) = x.if_arithmetic(ArithOpType::Modulo) {
                    r.if_constant()?;
                    if l == self.rdtsc_custom || l == self.custom_no_mask {
                        Some(())
                    } else {
                        None
                    }
                } else if let Some((l, r)) = x.if_arithmetic_sub() {
                    // `rdtsc - (rdtsc / x * x)` where division is replaced with multiplication
                    r.if_arithmetic_mul()
                        .or_else(|| r.if_arithmetic_lsh())
                        .and_then(|x| x.1.if_constant())?;
                    l.if_arithmetic_or()
                        .and_if_either_other(|x| x == self.rdtsc_custom)?;
                    Some(())
                } else {
                    None
                }
            })
            .is_some();
        if is_rdtsc_jump {
            ctrl.end_branch();
            ctrl.add_branch_with_current_state(to);
            true
        } else {
            false
        }
    }
}

#[test]
fn test_quick_reset() {
    use scarf::VirtualAddress;

    let binary = &scarf::raw_bin(VirtualAddress(0), vec![]);
    let bump = bumpalo::Bump::new();
    let mut ins = InstructionsNeedingVerify::new(&bump, 64);
    for i in 0..0x10 {
        ins.push(Rva(i * 0x1000));
    }
    ins.build_lookup();
    let mut iter = InsVerifyIter::empty();
    iter.reset(VirtualAddress(0x1800), binary, &mut ins);
    iter.at_instruction_end(VirtualAddress(0x2000), binary, &mut ins);
    assert!(iter.quick_reset(VirtualAddress(0x1800), binary, 0x1800, &mut ins));
    assert_eq!(iter.next.0, 0x2000);
    iter.at_instruction_end(VirtualAddress(0x2000), binary, &mut ins);
    iter.at_instruction_end(VirtualAddress(0x3000), binary, &mut ins);
    assert!(iter.quick_reset(VirtualAddress(0x1800), binary, 0x1800, &mut ins));
    assert_eq!(iter.next.0, 0x2000);

    iter.reset(VirtualAddress(0x9800), binary, &mut ins);
    assert!(iter.quick_reset(VirtualAddress(0x8800), binary, 0x8800, &mut ins));
    assert_eq!(iter.next.0, 0x9000);

    iter.reset(VirtualAddress(0x9800), binary, &mut ins);
    assert!(iter.quick_reset(VirtualAddress(0x6800), binary, 0x6800, &mut ins));
    assert_eq!(iter.next.0, 0x7000);

    iter.reset(VirtualAddress(0x9800), binary, &mut ins);
    assert_eq!(iter.next.0, 0xa000);
    assert!(iter.quick_reset(VirtualAddress(0xa800), binary, 0xa800, &mut ins));
    assert_eq!(iter.next.0, 0xb000);

    iter.reset(VirtualAddress(0x9800), binary, &mut ins);
    assert!(iter.quick_reset(VirtualAddress(0xc800), binary, 0xc800, &mut ins));
    assert_eq!(iter.next.0, 0xd000);
}
