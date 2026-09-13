use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::ArithOpType;
use scarf::{
    DestOperand, MemAccess, MemAccessSize, Operand, OperandCtx, Operation, BinarySection,
    BinaryFile,
};

use crate::analysis::{AnalysisCtx};
use crate::analysis_find::{FunctionFinder, find_bytes, entry_of_until, EntryOf};
use crate::add_terms::collect_arith_add_terms;
use crate::call_tracker::{CallTracker};
use crate::switch::CompleteSwitch;
use crate::util::{
    ControlExt, OperandExt, OptionExt, single_result_assign, if_arithmetic_eq_neq,
    MemAccessExt,
};
use crate::vtables::Vtables;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SnpDefinitions<'e> {
    pub snp_definitions: Operand<'e>,
    pub entry_size: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InitStormNetworking<Va: VirtualAddress> {
    pub init_storm_networking: Option<Va>,
    pub load_snp_list: Option<Va>,
}

#[derive(Copy, Clone, Debug)]
pub struct SnetHandlePackets<Va: VirtualAddress> {
    pub send_packets: Option<Va>,
    pub recv_packets: Option<Va>,
}

#[derive(Copy, Clone, Debug)]
pub struct StepLobbyNetwork<Va: VirtualAddress> {
    pub step_lobby_network: Option<Va>,
    pub send_queued_lobby_commands: Option<Va>,
}

#[derive(Copy, Clone, Debug)]
pub struct StepLobbyState<Va: VirtualAddress> {
    pub process_async_lobby_command: Option<Va>,
    pub command_lobby_map_p2p: Option<Va>,
}

pub struct SnetRecvPackets<'e> {
    pub snet_local_player_list: Option<Operand<'e>>,
    pub snet_player_list: Option<Operand<'e>>,
}

pub(crate) fn snp_definitions<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
) -> Option<SnpDefinitions<'e>> {
    // Search for BNAU code.
    // The data is expected to be
    // SnpDefinition { u32 code, char *string_key, char *string_key, Caps *caps, Functions funcs }
    // Functions { u32 size_bytes, func *funcs[..] } (Functions are global constructor inited
    // though, so they're not in static data)
    // BNAU should be followed by UDPA
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let data = analysis.binary_sections.data;
    let results = find_bytes(bump, &data.data, &[0x55, 0x41, 0x4e, 0x42]);
    let mut result = None;
    for rva in results {
        let address = data.virtual_address + rva.0;
        let entry_size = (0x10..0x100).find(|i| {
            match binary.read_u32(address + i * 4) {
                Ok(o) => o == 0x55445041,
                Err(_) => false,
            }
        }).map(|x| x * 4);
        if let Some(entry_size) = entry_size {
            let new = SnpDefinitions {
                snp_definitions: ctx.constant(address.as_u64()),
                entry_size,
            };
            if single_result_assign(Some(new), &mut result) {
                break;
            }
        }
    }
    result
}

pub(crate) fn init_storm_networking<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    vtables: &Vtables<'e, E::VirtualAddress>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> InitStormNetworking<E::VirtualAddress> {
    let mut result = InitStormNetworking {
        init_storm_networking: None,
        load_snp_list: None,
    };

    // Init function of AVSelectConnectionScreen calls init_storm_networking,
    // init_storm_networking calls load_snp_list(&[fnptr, fnptr], 1)
    let vtables = vtables.vtables_starting_with(b".?AVSelectConnectionScreen@glues@@\0")
        .map(|x| x.address);
    let binary = analysis.binary;
    let text = analysis.binary_sections.text;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let funcs = functions.functions();
    for vtable in vtables {
        let func = match binary.read_address(vtable + 0x3 * E::VirtualAddress::SIZE) {
            Ok(o) => o,
            Err(_) => continue,
        };
        let mut analyzer = FindInitStormNetworking::<E> {
            result: &mut result,
            inlining: false,
            text,
            binary,
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, func);
        analysis.analyze(&mut analyzer);
        if result.init_storm_networking.is_some() {
            break;
        }
    }
    if result.init_storm_networking.is_none() {
        // Fallback: The same function should also refer to string SetGatewayText
        let rdata = analysis.binary_sections.rdata;
        let results = find_bytes(bump, &rdata.data, b"SetGatewayText\0");
        'outer: for rva in results {
            let address = rdata.virtual_address + rva.0;
            let global_refs = functions.find_functions_using_global(analysis, address);
            for global_ref in global_refs {
                entry_of_until(binary, &funcs, global_ref.use_address, |entry| {
                    let mut analyzer = FindInitStormNetworking::<E> {
                        result: &mut result,
                        inlining: false,
                        text,
                        binary,
                    };
                    let mut analysis = FuncAnalysis::new(binary, ctx, entry);
                    analysis.analyze(&mut analyzer);
                    if result.init_storm_networking.is_some() {
                        EntryOf::Ok(())
                    } else {
                        EntryOf::Retry
                    }
                });
                if result.init_storm_networking.is_some() {
                    break 'outer;
                }
            }
        }
    }
    result
}

struct FindInitStormNetworking<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut InitStormNetworking<E::VirtualAddress>,
    inlining: bool,
    text: &'a BinarySection<E::VirtualAddress>,
    binary: &'a BinaryFile<E::VirtualAddress>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindInitStormNetworking<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if !self.inlining {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        self.inlining = true;
                        ctrl.analyze_with_current_state(self, dest);
                        if self.result.init_storm_networking.is_some() {
                            self.result.init_storm_networking = Some(dest);
                            ctrl.end_analysis();
                        }
                        self.inlining = false;
                    }
                } else {
                    let arg1 = ctrl.resolve_arg(0);
                    let arg2 = ctrl.resolve_arg(1).if_constant();
                    let text_start = self.text.virtual_address;
                    let text_end = self.text.virtual_address + self.text.virtual_size;
                    let binary = self.binary;

                    let word_size = u64::from(E::VirtualAddress::SIZE);
                    let ctx = ctrl.ctx();
                    let mem = if arg2 == Some(1) {
                        ctx.mem_access(arg1, 0, E::WORD_SIZE)
                    } else if arg2 == Some(2) {
                        // Older versions have array size 2 and a second fnptr pair
                        ctx.mem_access(arg1, word_size * 2, E::WORD_SIZE)
                    } else {
                        return;
                    };
                    let arg1_1 = ctrl.read_memory(&mem);
                    let arg1_2 = ctrl.read_memory(&mem.with_offset(word_size));

                    let ok = Some(())
                        .and_then(|_| ctrl.if_mem_word(arg1_1)?.if_constant_address())
                        .and_then(|a| binary.read_address(E::VirtualAddress::from_u64(a)).ok())
                        .filter(|&c| c >= text_start && c < text_end)
                        .and_then(|_| ctrl.if_mem_word(arg1_2)?.if_constant_address())
                        .and_then(|a| binary.read_address(E::VirtualAddress::from_u64(a)).ok())
                        .filter(|&c| c >= text_start && c < text_end)
                        .is_some();
                    if ok {
                        self.result.init_storm_networking = Some(E::VirtualAddress::from_u64(0));
                        if let Some(dest) = ctrl.resolve(dest).if_constant() {
                            self.result.load_snp_list = Some(E::VirtualAddress::from_u64(dest));
                        }
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn snet_handle_packets<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    vtables: &Vtables<'e, E::VirtualAddress>,
) -> SnetHandlePackets<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;

    let mut result = SnetHandlePackets {
        send_packets: None,
        recv_packets: None,
    };
    // Look for snet functions in packet received handler of UdpServer (vtable fn #3)
    // First one - receive - immediately calls a function pointer to receive the packets,
    // send is verified by looking for a comparision (a - Mem32[b + C]) < 0xc350,
    // and by then also verifying that it checks bit 4 on the packet flags
    let vtables = BumpVec::from_iter_in(
        vtables.vtables_starting_with(b".?AVUdpServer@").map(|x| x.address),
        bump,
    );
    for root_inline_limit in 0..2 {
        for &vtable in &vtables {
            let func = match binary.read_address(vtable + 0x3 * E::VirtualAddress::SIZE) {
                Ok(o) => o,
                Err(_) => continue,
            };
            let mut analyzer = SnetHandlePacketsAnalyzer::<E> {
                result: &mut result,
                root_inline_limit,
                checking_candidate: false,
                inlining_entry: E::VirtualAddress::from_u64(0),
                verify_recv_packets: false,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, func);
            analysis.analyze(&mut analyzer);
            if result.recv_packets.is_some() {
                break;
            }
        }
    }
    result
}

struct SnetHandlePacketsAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut SnetHandlePackets<E::VirtualAddress>,
    checking_candidate: bool,
    // How much should try inilining before checking for candidate.
    // Do first with no inlining, then with one level of inlining.
    root_inline_limit: u8,
    inlining_entry: E::VirtualAddress,
    verify_recv_packets: bool,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for SnetHandlePacketsAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let searching_for_recv = self.result.recv_packets.is_none();
        let ctx = ctrl.ctx();
        if self.verify_recv_packets {
            match *op {
                Operation::Jump { condition, .. } => {
                    let condition = ctrl.resolve(condition);
                    if condition.if_and_mask_eq_neq(0x4).is_some() {
                        self.result.recv_packets = Some(self.inlining_entry);
                        ctrl.end_analysis();
                    }
                }
                _ => (),
            }
        } else {
            match *op {
                Operation::Call(dest) => {
                    let dest = ctrl.resolve(dest);
                    if !self.checking_candidate {
                        if let Some(dest) = dest.if_constant() {
                            let dest = E::VirtualAddress::from_u64(dest);
                            self.inlining_entry = dest;
                            if self.root_inline_limit == 0 {
                                self.checking_candidate = true;
                            } else {
                                self.root_inline_limit -= 1;
                            }
                            ctrl.analyze_with_current_state(self, dest);
                            self.verify_recv_packets = false;
                            if self.checking_candidate {
                                self.checking_candidate = false;
                            } else {
                                self.root_inline_limit += 1;
                            }
                            if self.result.send_packets.is_some() {
                                ctrl.end_analysis();
                            }
                        }
                    } else {
                        if searching_for_recv {
                            let ok = Some(())
                                .filter(|_| dest.if_memory().is_some())
                                .filter(|_| {
                                    // All arguments are out arguments initialized to 0
                                    (0..3).all(|i| {
                                        Some(())
                                            .map(|_| ctrl.resolve_arg(i))
                                            .map(|x| {
                                                let mem = ctx.mem_access(x, 0, MemAccessSize::Mem32);
                                                ctrl.read_memory(&mem)
                                            })
                                            .filter(|&x| x == ctx.const_0())
                                            .is_some()
                                    })
                                })
                                .is_some();
                            if ok {
                                // Write results that the func won't return
                                let a1 = ctrl.resolve_arg(0);
                                let a1_mem = ctx.mem_access(a1, 0, E::WORD_SIZE);
                                ctrl.write_memory(&a1_mem, ctx.custom(0));

                                let a2 = ctrl.resolve_arg(1);
                                let a2_mem = ctx.mem_access(a2, 0, E::WORD_SIZE);
                                ctrl.write_memory(&a2_mem, ctx.custom(1));

                                ctrl.do_call_with_result(ctx.const_1());
                                self.verify_recv_packets = true;
                            } else {
                                // End even if it isn't recv_packets, the [snp_functions + x] call
                                // should be first.
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
                Operation::Jump { condition, .. } => {
                    if !searching_for_recv && self.checking_candidate {
                        let condition = ctrl.resolve(condition);
                        let ok = condition.if_arithmetic_gt()
                            .filter(|x| x.0.if_constant() == Some(0xc350))
                            .and_then(|x| {
                                let mem = Operand::and_masked(x.1).0
                                    .if_arithmetic_sub()?.1
                                    .if_mem32()?;
                                let (base, _offset) = mem.address();
                                base.if_memory()?;
                                Some(())
                            })
                            .is_some();
                        if ok {
                            self.result.send_packets = Some(self.inlining_entry);
                            ctrl.end_analysis();
                        }
                    }
                }
                _ => (),
            }
        }
    }
}

pub(crate) fn start_udp_server<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    // Check for a function using "Game Data Port" string,
    // immediately checking this.x18 == 0, 4, 6
    let binary = actx.binary;
    let ctx = actx.ctx;
    let str_refs = functions.string_refs(actx, b"game data port");
    let mut result = None;
    let funcs = functions.functions();
    for string in str_refs {
        let new = entry_of_until(binary, &funcs, string.use_address, |entry| {
            let mut analyzer = IsStartUdpServer::<E> {
                result: EntryOf::Retry,
                use_address: string.use_address,
                found: [false; 3],
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        }).into_option_with_entry();
        if let Some((entry, ())) = new {
            if single_result_assign(Some(entry), &mut result) {
                break;
            }
        }
    }
    result
}

struct IsStartUdpServer<'e, E: ExecutionState<'e>> {
    result: EntryOf<()>,
    use_address: E::VirtualAddress,
    found: [bool; 3],
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsStartUdpServer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        /// Matches val = Mem32[ecx + C]
        fn is_this_mem32<'e>(val: Operand<'e>, ctx: OperandCtx<'e>) -> bool {
            val.if_mem32()
                .filter(|x| x.address().0 == ctx.register(1))
                .is_some()
        }

        let address = ctrl.address();
        if self.use_address >= address && self.use_address < ctrl.current_instruction_end() {
            self.result = EntryOf::Stop;
            ctrl.end_branch(); // Branch using "Game Data Port" isn't needed
        }
        if let Operation::Jump { condition, .. } = *op {
            let condition = ctrl.resolve(condition);
            let ctx = ctrl.ctx();
            let ok = if_arithmetic_eq_neq(condition)
                .map(|x| (x.0, x.1))
                .and_either(|x| match x.if_constant() {
                    Some(0) => Some(0),
                    Some(4) => Some(1),
                    Some(6) => Some(2),
                    _ => None,
                })
                .filter(|&(_, other)| is_this_mem32(other, ctx))
                .map(|x| x.0);
            if let Some(index) = ok {
                self.found[index] = true;
                if self.found == [true; 3] {
                    self.result = EntryOf::Ok(());
                    ctrl.end_analysis();
                }
            } else {
                // Also check for val & ffff_fff9 == 0, which matches
                // 0/2/4/6 (It would then check != 2 later)
                let all_ok = if_arithmetic_eq_neq(condition)
                    .filter(|x| x.1 == ctx.const_0())
                    .and_then(|x| x.0.if_arithmetic_and_const(0xffff_fff9))
                    .filter(|&x| is_this_mem32(x, ctx))
                    .is_some();
                if all_ok {
                    self.result = EntryOf::Ok(());
                    ctrl.end_analysis();
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct NetFormatTurnRate<'e, Va: VirtualAddress> {
    pub net_format_turn_rate: Option<Va>,
    pub net_user_latency: Option<Operand<'e>>,
}

pub(crate) fn anaylze_net_format_turn_rate<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> NetFormatTurnRate<'e, E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let str_refs = functions.string_refs(actx, b"bnet_latency_low");
    let mut result = None;
    let funcs = functions.functions();

    for string in str_refs {
        let val = entry_of_until(binary, &funcs, string.use_address, |entry| {

            let mut analyzer = IsNetUserLatency::<E> {
                result: EntryOf::Retry,
                inlining: false,
                bump: &actx.bump,
                phantom: Default::default(),
            };

            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        }).into_option_with_entry();

        if single_result_assign(val, &mut result) {
          break;
        }
    }

    result.map_or(NetFormatTurnRate {
        net_format_turn_rate: None,
        net_user_latency: None,
    }, |r| NetFormatTurnRate {
        net_format_turn_rate: Some(r.0),
        net_user_latency: Some(r.1)
    })
}

struct IsNetUserLatency<'a, 'e, E: ExecutionState<'e>> {
    result: EntryOf<Operand<'e>>,
    inlining: bool,
    bump: &'a bumpalo::Bump,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsNetUserLatency<'a, 'e, E> {
    type Exec = E;
    type State = analysis::DefaultState;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if !self.inlining {
            match *op {
                Operation::Call(dest) => {
                    let dest = ctrl.resolve(dest);
                    if let Some(dest) = dest.if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        self.inlining = true;
                        ctrl.inline(self, dest);
                        ctrl.skip_operation();
                        self.inlining = false;


                    }
                },
                Operation::Move(_, val) => {
                    if let Some(mem) = ctrl.if_mem_word(val) {
                        let (mem_base, _) = mem.address();
                        // Looking for e.g. mov eax, [string_table + net_user_latency*4]
                        let mut terms = collect_arith_add_terms(mem_base, self.bump);
                        let term = terms.remove_get(|x, is_sub| {
                            !is_sub &&
                                x.if_arithmetic_mul_const(E::VirtualAddress::SIZE.into()).is_some()
                        });
                        if let Some(term) = term {
                            let result =
                                term.if_arithmetic_mul_const(E::VirtualAddress::SIZE.into())
                                    .and_then(|x| Some(ctrl.resolve(x).unwrap_sext()));

                            if let Some(result) = result {
                                self.result = EntryOf::Ok(result);
                                ctrl.end_analysis();
                            }
                    }
                }
                },
                _ => (),
            }
        } else {
            // We're only looking for a very small function, so if we find go anywhere else, end
            // analysis
            match *op {
                Operation::Call(_) | Operation::Jump { .. } => {
                    ctrl.end_analysis()
                }
                _ => {}
            }
        }
    }
}

pub(crate) fn step_lobby_network<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    step_network: E::VirtualAddress,
    send_command: E::VirtualAddress,
    functions: &FunctionFinder<'_, 'e, E>,
) -> StepLobbyNetwork<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut result = StepLobbyNetwork {
        step_lobby_network: None,
        send_queued_lobby_commands: None,
    };

    let callers = functions.find_callers(actx, step_network);
    let funcs = functions.functions();
    for caller in callers {
        let new = entry_of_until(binary, &funcs, caller, |entry| {
            let mut analyzer = StepLobbyNetworkAnalyzer::<E> {
                result: &mut result,
                entry_of: EntryOf::Retry,
                inline_limit: 0,
                step_network,
                send_command,
                state: StepLobbyNetworkState::StepNetwork,
                true_state: None,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.entry_of
        }).into_option_with_entry().map(|x| x.0);

        if single_result_assign(new, &mut result.step_lobby_network) {
            break;
        }
    }

    result
}

struct StepLobbyNetworkAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    entry_of: EntryOf<()>,
    result: &'a mut StepLobbyNetwork<E::VirtualAddress>,
    inline_limit: u8,
    step_network: E::VirtualAddress,
    send_command: E::VirtualAddress,
    state: StepLobbyNetworkState,
    true_state: Option<(E, analysis::DefaultState, E::VirtualAddress)>,
}

enum StepLobbyNetworkState {
    /// Find step_network call, and jump based on its return value
    StepNetwork,
    /// False branch should have comparison of GetTickCount() - global, 0x4e20
    StepNetworkFalse,
    /// True branch should call send_queued_lobby_commands
    StepNetworkTrue,
    /// Should have send_command(global, 1) call early in the function
    SendQueuedVerify,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    StepLobbyNetworkAnalyzer<'a, 'e, E>
{
    type Exec = E;
    type State = analysis::DefaultState;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            StepLobbyNetworkState::StepNetwork => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if dest == self.step_network {
                            self.entry_of = EntryOf::Stop;
                            ctrl.do_call_with_result(ctx.custom(0));
                        }
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((other, eq)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                        if other.unwrap_and_mask().if_custom() == Some(0) {
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_eq_address(eq, to);
                            self.true_state = ctrl.state_for_neq_address(eq, to);
                            self.state = StepLobbyNetworkState::StepNetworkFalse;
                        }
                    }
                }
            }
            StepLobbyNetworkState::StepNetworkFalse => {
                if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    let ok = condition.if_arithmetic_gt()
                        .is_some_and(|x| x.0.if_constant() == Some(0x4e20));
                    if ok {
                        self.entry_of = EntryOf::Ok(());
                        if let Some(state) = self.true_state.take() {
                            ctrl.continue_with_state(state);
                            self.state = StepLobbyNetworkState::StepNetworkTrue;
                        }
                    }
                }
            }
            StepLobbyNetworkState::StepNetworkTrue => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.inline_limit = 6;
                        self.state = StepLobbyNetworkState::SendQueuedVerify;
                        ctrl.analyze_with_current_state(self, dest);
                        if self.result.send_queued_lobby_commands.is_some() {
                            self.result.send_queued_lobby_commands = Some(dest);
                            ctrl.end_analysis();
                        } else {
                            self.state = StepLobbyNetworkState::StepNetworkTrue;
                        }
                    }
                }
            }
            StepLobbyNetworkState::SendQueuedVerify => {
                match *op {
                    Operation::Call(..) | Operation::Jump { .. } => {
                        if self.inline_limit == 0 {
                            ctrl.end_analysis();
                        } else {
                            self.inline_limit -= 1;
                        }
                    }
                    _ => (),
                }
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if dest == self.send_command {
                            let arg2 = ctrl.resolve_arg_u32(1);
                            if arg2 == ctx.const_1() {
                                self.result.send_queued_lobby_commands =
                                    Some(E::VirtualAddress::from_u64(0));
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn step_lobby_state<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    step_lobby_network: E::VirtualAddress,
    functions: &FunctionFinder<'_, 'e, E>,
) -> StepLobbyState<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut result = StepLobbyState {
        process_async_lobby_command: None,
        command_lobby_map_p2p: None,
    };

    let callers = functions.find_callers(actx, step_lobby_network);
    let funcs = functions.functions();
    for caller in callers {
        // Can match two different functions that both work for async command
        entry_of_until(binary, &funcs, caller, |entry| {
            let mut analyzer = StepLobbyStateAnalyzer::<E> {
                result: &mut result,
                entry_of: EntryOf::Retry,
                inline_limit: 0,
                step_lobby_network,
                state: StepLobbyStateState::StepLobbyNetwork,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.entry_of
        });

        if result.process_async_lobby_command.is_some() {
            break;
        }
    }

    result
}

struct StepLobbyStateAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    entry_of: EntryOf<()>,
    result: &'a mut StepLobbyState<E::VirtualAddress>,
    inline_limit: u8,
    step_lobby_network: E::VirtualAddress,
    state: StepLobbyStateState,
}

enum StepLobbyStateState {
    /// Find step_lobby_network call, and jump based on its return value
    StepLobbyNetwork,
    /// Should be next call / tail call on 0 branch
    FindAsyncCommands,
    /// Should have a switch
    VerifyAsyncCommands,
    /// On branch 0x4f, should have a call to lobby_command_map_p2p
    MapP2pPacket,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for StepLobbyStateAnalyzer<'a, 'e, E> {
    type Exec = E;
    type State = analysis::DefaultState;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            StepLobbyStateState::StepLobbyNetwork => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if dest == self.step_lobby_network {
                            self.entry_of = EntryOf::Stop;
                            ctrl.do_call_with_result(ctx.custom(0));
                        }
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((other, eq)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                        if other.unwrap_and_mask().if_custom() == Some(0) {
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_eq_address(eq, to);
                            self.state = StepLobbyStateState::FindAsyncCommands;
                        }
                    }
                }
            }
            StepLobbyStateState::FindAsyncCommands => {
                let dest = match *op {
                    Operation::Call(dest) => dest,
                    Operation::Jump { condition, to } => {
                        if condition == ctx.const_1() &&
                            ctrl.resolve_register(4) == ctx.register(4)
                        {
                            to
                        } else {
                            ctrl.end_analysis();
                            return;
                        }
                    }
                    _ => return,
                };
                if let Some(dest) = ctrl.resolve_va(dest) {
                    self.inline_limit = 8;
                    self.state = StepLobbyStateState::VerifyAsyncCommands;
                    // This doesn't do stack correctly for tail call but there are no
                    // arguments so it's fine..
                    ctrl.analyze_with_current_state(self, dest);
                    if self.result.process_async_lobby_command.is_some() {
                        self.result.process_async_lobby_command = Some(dest);
                    }
                }
                ctrl.end_analysis();
            }
            StepLobbyStateState::VerifyAsyncCommands => {
                match *op {
                    Operation::Call(..) | Operation::Jump { .. } => {
                        if self.inline_limit == 0 {
                            ctrl.end_analysis();
                        } else {
                            self.inline_limit -= 1;
                        }
                    }
                    _ => (),
                }
                if let Operation::Jump { condition, to } = *op {
                    if condition == ctx.const_1() && to.if_constant().is_none() {
                        let to = ctrl.resolve(to);
                        let exec_state = ctrl.exec_state();
                        if let Some(switch) = CompleteSwitch::new(to, ctx, exec_state) {
                            self.result.process_async_lobby_command =
                                Some(E::VirtualAddress::from_u64(0));
                            let binary = ctrl.binary();
                            if let Some(branch) = switch.branch(binary, ctx, 0x4f) {
                                ctrl.clear_unchecked_branches();
                                ctrl.continue_at_address(branch);
                                self.state = StepLobbyStateState::MapP2pPacket;
                            }
                        }
                    }
                }
            }
            StepLobbyStateState::MapP2pPacket => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let a1 = ctrl.resolve_arg(0);
                        let a2 = ctrl.resolve_arg(1);
                        let ok = a2.if_mem16().is_some_and(|mem| {
                            mem.with_offset(2) == ctx.mem_access(a1, 0, MemAccessSize::Mem16)
                        });
                        if ok {
                            self.result.command_lobby_map_p2p = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_snet_recv_packets<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    snet_recv_packets: E::VirtualAddress,
) -> SnetRecvPackets<'e> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut result = SnetRecvPackets {
        snet_local_player_list: None,
        snet_player_list: None,
    };

    let mut analyzer = SnetRecvAnalyzer::<E> {
        result: &mut result,
        state: SnetRecvState::Init,
        call_tracker: CallTracker::with_capacity(actx, 0x1000, 0x8),
        inline_depth: 0,
        ctx,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, snet_recv_packets);
    analysis.analyze(&mut analyzer);

    result
}

struct SnetRecvAnalyzer<'acx, 'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut SnetRecvPackets<'e>,
    call_tracker: CallTracker<'acx, 'e, E>,
    state: SnetRecvState,
    inline_depth: u8,
    ctx: OperandCtx<'e>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum SnetRecvState {
    /// Find call to fnptr(&mut sockaddr_in, ..), write Custom(0) to that ptr (sockaddr)
    /// and Custom(1) to arg 2 (data)
    Init,
    /// Find jump on packet.flags & 4, follow zero branch
    PacketFlags4,
    /// Inline once to find_snet_player_by_sockaddr(*a1 = Custom(0)),
    /// then find check of bit1 of list.next
    PlayerList,
    /// Find jump on a func return value from before being nonnull, then use same
    /// logic as in PlayerList. If the func was inlined then the list got already set in
    /// PacketFlags4 state.
    LocalPlayerList,
    /// Same as PlayerList
    LocalPlayerListGetFn,
}

impl<'acx, 'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    SnetRecvAnalyzer<'acx, 'a, 'e, E>
{
    type Exec = E;
    type State = analysis::DefaultState;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            SnetRecvState::Init => {
                if let Operation::Call(dest) = *op {
                    let dest = ctrl.resolve(dest);
                    if ctrl.if_mem_word(dest).is_some() {
                        let a1 = ctrl.resolve_arg(0);
                        let a1_mem = ctx.mem_access(a1, 0, E::WORD_SIZE);
                        ctrl.write_memory(&a1_mem, ctx.custom(0));

                        let a2 = ctrl.resolve_arg(1);
                        let a2_mem = ctx.mem_access(a2, 0, E::WORD_SIZE);
                        ctrl.write_memory(&a2_mem, ctx.custom(1));

                        ctrl.do_call_with_result(ctx.const_1());
                        self.state = SnetRecvState::PacketFlags4;
                    }
                }
            }
            SnetRecvState::PacketFlags4 => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let result = condition.if_and_mask_eq_neq(0x4);
                    if let Some((_, eq_zero)) = result {
                        ctrl.continue_at_eq_address(eq_zero, to);
                        self.state = SnetRecvState::PlayerList;
                    } else if let Some(cand) = self.check_player_list_head_bit1(condition) {
                        self.result.snet_local_player_list = Some(cand);
                    }
                } else if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.call_tracker.add_call(ctrl, dest);
                    }
                }
            }
            SnetRecvState::PlayerList | SnetRecvState::LocalPlayerListGetFn => {
                if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some(result) = self.check_player_list_head_bit1(condition) {
                        if self.state == SnetRecvState::PlayerList {
                            self.result.snet_player_list = Some(result);
                            if self.result.snet_local_player_list.is_some() {
                                // local player list access was inlined, and found in
                                // flag4 check, can stop now
                                ctrl.end_analysis();
                            } else {
                                if self.inline_depth != 0 {
                                    ctrl.end_analysis();
                                }
                                self.state = SnetRecvState::LocalPlayerList;
                            }
                        } else {
                            self.result.snet_local_player_list = Some(result);
                            ctrl.end_analysis();
                        }
                    }
                } else if let Operation::Call(dest) = *op {
                    if self.inline_depth == 0 {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let a1 = ctrl.resolve_arg(0);
                            let a1_mem = ctx.mem_access(a1, 0, E::WORD_SIZE);
                            let a1_mem_value = ctrl.read_memory(&a1_mem);
                            let inline = ctrl.if_mem_word(a1_mem_value)
                                .is_some_and(|x| x.address().0.if_custom() == Some(0));
                            if inline {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                if self.result.snet_player_list.is_some() &&
                                    self.result.snet_local_player_list.is_some()
                                {
                                    // local player list access was inlined, and found in
                                    // flag4 check, can stop now
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                }
            }
            SnetRecvState::LocalPlayerList => {
                if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some(x) = condition.if_arithmetic_eq_neq_zero(ctx) &&
                        let Some(custom) = x.0.unwrap_and_mask().if_custom()
                    {
                        if let Some(addr) = self.call_tracker.custom_id_to_func(custom) {
                            self.state = SnetRecvState::LocalPlayerListGetFn;
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, addr);
                            self.inline_depth -= 1;
                            if self.result.snet_local_player_list.is_some() {
                                ctrl.end_analysis();
                            } else {
                                self.state = SnetRecvState::LocalPlayerList;
                            }
                        }
                    }
                }
            }
        }
    }
}

impl<'acx, 'a, 'e, E: ExecutionState<'e>> SnetRecvAnalyzer<'acx, 'a, 'e, E> {
    fn check_player_list_head_bit1(&self, condition: Operand<'e>) -> Option<Operand<'e>> {
        let ctx = self.ctx;
        condition.if_and_mask_eq_neq(0x1)
            .and_then(|x| {
                let mem = x.0.if_memory()?;
                if mem.is_global() {
                    let offset = 0u64.wrapping_sub(2 * E::VirtualAddress::SIZE as u64);
                    Some(mem.with_offset(offset).address_op(ctx))
                } else {
                    None
                }
            })
    }
}

/// Globals of the per-turn sync check ring.
///
/// Once per turn the game hashes one of a few rotating "check kinds" of the simulation state
/// into the next slot of the `sync_data` ring and sends a summary of that slot to the other
/// players, which lets them notice a desync.
pub struct TurnSyncChecks<'e, Va: VirtualAddress> {
    /// Fills one ring slot; called once per turn from step_network.
    pub record_turn_sync_slot: Option<Va>,
    /// u8 ring cursor, wrapped to 0 at the ring's slot count before the slot is written.
    pub sync_slot_index: Option<Operand<'e>>,
    /// u8 cursor into sync_check_kinds, wrapped at sync_check_kind_count.
    pub sync_check_kind_index: Option<Operand<'e>>,
    pub sync_check_kind_count: Option<Operand<'e>>,
    /// u8 array of the check kinds that are rotated through.
    pub sync_check_kinds: Option<Operand<'e>>,
    /// Row of map_tile_flags hashed this turn; stepped by one per turn, wraps at map height.
    pub sync_map_row_index: Option<Operand<'e>>,
    pub captured_minimap_unit_vision_sync_value: Option<Operand<'e>>,
    pub captured_minimap_marker_count_sync_value: Option<Operand<'e>>,
    /// u8 fold of the sprite vision rows that current_sync_check_hash names.
    pub current_sync_state_byte: Option<Operand<'e>>,
    /// u32 copied to the slot next to current_sync_state_byte. Despite holding a value the
    /// receiver checks the fold against, it is the first sprite hline row of the window that
    /// was folded, not a hash.
    pub current_sync_check_hash: Option<Operand<'e>>,
    /// u8 array, one visibility mask per sprite hline row.
    pub current_sync_vision_bytes: Option<Operand<'e>>,
}

impl<'e, Va: VirtualAddress> Default for TurnSyncChecks<'e, Va> {
    fn default() -> Self {
        TurnSyncChecks {
            record_turn_sync_slot: None,
            sync_slot_index: None,
            sync_check_kind_index: None,
            sync_check_kind_count: None,
            sync_check_kinds: None,
            sync_map_row_index: None,
            captured_minimap_unit_vision_sync_value: None,
            captured_minimap_marker_count_sync_value: None,
            current_sync_state_byte: None,
            current_sync_check_hash: None,
            current_sync_vision_bytes: None,
        }
    }
}

/// Finds the turn sync check ring globals, given `sync_data`.
///
/// Anchored on the functions referencing sync_data: only the slot writer stores to
/// `sync_data + index * slot_size` at several offsets inside a single slot, while the command
/// sender and the peer verifier only read slots. Each of those stores names one of the wanted
/// globals as its source: the check kind is read out of sync_check_kinds, two more bytes come
/// from the captured minimap values, and the rest of the slot is filled from the current sync
/// state (a byte, a dword, and a row array which is either block copied inline or memcpy'd).
///
/// The two cursors are recognized from the wraparound comparisons that step them, which have
/// the same `index + 1` shape and differ in what they are bounded by: the slot cursor by the
/// ring's slot count, the kind cursor by another global, which is then the kind count.
/// sync_map_row_index is the global multiplied by the map width to reach the turn's map row.
pub(crate) fn turn_sync_checks<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    sync_data: Operand<'e>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> TurnSyncChecks<'e, E::VirtualAddress> {
    let mut result = TurnSyncChecks::default();
    let binary = actx.binary;
    let ctx = actx.ctx;
    let sync_data_addr = match sync_data.if_constant() {
        Some(s) => s,
        None => return result,
    };
    let funcs = functions.functions();
    let global_refs = functions.find_functions_using_global(
        actx,
        E::VirtualAddress::from_u64(sync_data_addr),
    );
    for global_ref in &global_refs {
        let mut candidate = TurnSyncChecks::default();
        let entry = entry_of_until(binary, &funcs, global_ref.use_address, |entry| {
            candidate = TurnSyncChecks::default();
            let vision_copy = {
                let mut analyzer = TurnSyncAnalyzer::<E> {
                    result: &mut candidate,
                    sync_data_addr,
                    slot_size: 0,
                    vision_copy: None,
                    data_constant: None,
                    inline_depth: 0,
                    phantom: Default::default(),
                };
                let mut analysis = FuncAnalysis::new(binary, ctx, entry);
                analysis.analyze(&mut analyzer);
                analyzer.vision_copy
            };
            if let Some((_, address)) = vision_copy {
                candidate.current_sync_vision_bytes = Some(ctx.constant(address));
            }
            let is_slot_writer = candidate.sync_check_kinds.is_some() &&
                candidate.captured_minimap_unit_vision_sync_value.is_some() &&
                candidate.captured_minimap_marker_count_sync_value.is_some();
            match is_slot_writer {
                true => EntryOf::Ok(()),
                false => EntryOf::Retry,
            }
        }).into_option_with_entry().map(|x| x.0);
        if let Some(entry) = entry {
            candidate.record_turn_sync_slot = Some(entry);
            result = candidate;
            break;
        }
    }
    result
}

/// Slot offsets that hold a single global each; everything else that is copied in from a
/// constant address belongs to the vision row array.
const SYNC_SLOT_STATE_BYTE: u64 = 3;
const SYNC_SLOT_MINIMAP_UNIT_VISION: u64 = 4;
const SYNC_SLOT_MINIMAP_MARKER_COUNT: u64 = 5;
const SYNC_SLOT_CHECK_HASH: u64 = 8;

struct TurnSyncAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut TurnSyncChecks<'e, E::VirtualAddress>,
    sync_data_addr: u64,
    /// Byte size of one ring slot, learned from the index multiplier of the first indexed
    /// slot access. Zero until then.
    slot_size: u64,
    /// (slot offset, source address) of the lowest-offset store that copies the vision rows
    /// in; the source of that one is the array's base.
    vision_copy: Option<(u64, u64)>,
    /// Single non-code address loaded as a constant by the slot fill, or u64::MAX if there
    /// was more than one.
    data_constant: Option<u64>,
    inline_depth: u8,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for TurnSyncAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match *op {
            Operation::Move(ref dest, value) => {
                if let DestOperand::Memory(ref mem) = *dest {
                    let mem = ctrl.resolve_mem(mem);
                    if let Some(offset) = self.slot_offset(ctx, &mem) {
                        let value = ctrl.resolve(value);
                        self.slot_store(ctx, offset, value);
                        return;
                    }
                }
                if value.if_arithmetic_mul().is_some() {
                    let value = ctrl.resolve(value);
                    self.check_map_row(ctx, value);
                } else if value.if_memory().is_some_and(|x| x.size == MemAccessSize::Mem8) {
                    let value = ctrl.resolve(value);
                    self.check_check_kinds(ctx, value);
                } else if self.inline_depth != 0 && value.if_constant().is_some() {
                    let value = ctrl.resolve(value);
                    self.check_data_constant(ctrl, value);
                }
            }
            Operation::Call(dest) => {
                // memcpy(slot + vision_offset, current_sync_vision_bytes, row_count)
                let arg1 = ctrl.resolve_arg(0);
                let arg1_mem = ctx.mem_access(arg1, 0, MemAccessSize::Mem8);
                if let Some(offset) = self.slot_offset(ctx, &arg1_mem) {
                    let len = ctrl.resolve_arg(2).if_constant().unwrap_or(0);
                    let source = ctrl.resolve_arg(1).if_constant().unwrap_or(0);
                    if source != 0 && len != 0 && offset.wrapping_add(len) <= self.slot_size {
                        self.add_vision_copy(offset, source);
                        return;
                    }
                }
                // The slot fill is a tail call on some builds, which gets followed as a
                // branch of this same function, and a regular call on others.
                if self.inline_depth == 0 && self.slot_size != 0 {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let had_state = self.has_sync_state();
                        let outer_constant = self.data_constant;
                        self.data_constant = None;
                        self.inline_depth = 1;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inline_depth = 0;
                        let constant = self.data_constant;
                        self.data_constant = outer_constant;
                        // Builds that copy the row array with a string move leave nothing to
                        // match the source address against; the array is then the one data
                        // address that the slot fill loads by itself.
                        if !had_state && self.has_sync_state() && self.vision_copy.is_none() {
                            if let Some(constant) = constant.filter(|&x| x != u64::MAX) {
                                self.vision_copy = Some((u64::MAX, constant));
                            }
                        }
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                let condition = ctrl.resolve(condition);
                self.check_cursor_wrap(ctx, condition);
            }
            Operation::ConditionalMove(_, _, condition) => {
                let condition = ctrl.resolve(condition);
                self.check_cursor_wrap(ctx, condition);
            }
            _ => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> TurnSyncAnalyzer<'a, 'e, E> {
    /// Byte offset inside a ring slot for memory that is `sync_data + index * slot_size`
    /// based. Learns the slot size from the index multiplier; a slot has to be larger than
    /// the row array it contains, which alone rules out unrelated multiplications.
    fn slot_offset(&mut self, ctx: OperandCtx<'e>, mem: &MemAccess<'e>) -> Option<u64> {
        let (base, offset) = mem.address();
        if let Some((index, mul)) = base.if_arithmetic_mul() {
            let size = mul.if_constant()?;
            if size < 0x40 {
                return None;
            }
            if self.slot_size == 0 {
                self.slot_size = size;
            } else if self.slot_size != size {
                return None;
            }
            self.check_slot_index(ctx, index);
        } else if self.slot_size == 0 || base.if_constant() != Some(0) {
            // Slot 0's address has no multiply left in it, but only accept that once the
            // slot size has been learned from a properly indexed access.
            return None;
        }
        Some(offset.wrapping_sub(self.sync_data_addr)).filter(|&x| x < self.slot_size)
    }

    fn slot_store(&mut self, ctx: OperandCtx<'e>, offset: u64, value: Operand<'e>) {
        let result = &mut self.result;
        let global = value.unwrap_and_mask().if_memory()
            .filter(|mem| mem.is_global() && mem.if_constant_address().is_some());
        let global = match global {
            Some(s) => s,
            None => return,
        };
        let size = global.size;
        let op = ctx.memory(global);
        match offset {
            SYNC_SLOT_STATE_BYTE if size == MemAccessSize::Mem8 => {
                result.current_sync_state_byte = Some(op);
            }
            SYNC_SLOT_MINIMAP_UNIT_VISION if size == MemAccessSize::Mem8 => {
                result.captured_minimap_unit_vision_sync_value = Some(op);
            }
            SYNC_SLOT_MINIMAP_MARKER_COUNT if size == MemAccessSize::Mem8 => {
                result.captured_minimap_marker_count_sync_value = Some(op);
            }
            SYNC_SLOT_CHECK_HASH if size == MemAccessSize::Mem32 => {
                result.current_sync_check_hash = Some(op);
            }
            _ => {
                if offset > SYNC_SLOT_CHECK_HASH {
                    if let Some(address) = global.if_constant_address() {
                        self.add_vision_copy(offset, address);
                    }
                }
            }
        }
    }

    fn add_vision_copy(&mut self, offset: u64, address: u64) {
        let better = match self.vision_copy {
            Some((prev, _)) => offset < prev,
            None => true,
        };
        if better {
            self.vision_copy = Some((offset, address));
        }
    }

    fn has_sync_state(&self) -> bool {
        self.result.current_sync_state_byte.is_some() ||
            self.result.current_sync_check_hash.is_some()
    }

    /// Notes the single non-code address the slot fill loads as a plain constant, or that
    /// there was more than one. u64::MAX means "more than one".
    fn check_data_constant(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, value: Operand<'e>) {
        let constant = match value.if_constant() {
            Some(s) if s > 0x1000 => s,
            _ => return,
        };
        let address = E::VirtualAddress::from_u64(constant);
        let is_code = ctrl.binary().section_by_addr(address)
            .is_some_and(|section| &section.name[..5] == b".text");
        if is_code {
            return;
        }
        self.data_constant = match self.data_constant {
            None => Some(constant),
            Some(prev) if prev == constant => Some(prev),
            Some(_) => Some(u64::MAX),
        };
    }

    /// The ring cursor is the byte global that the slot address is indexed by. Builds which
    /// wrap it with a conditional move lose it here, and get it from the wrap comparison
    /// instead.
    fn check_slot_index(&mut self, ctx: OperandCtx<'e>, index: Operand<'e>) {
        if self.result.sync_slot_index.is_some() {
            return;
        }
        let mut found = None;
        for part in index.iter() {
            if let Some(mem) = part.if_memory() {
                if mem.size != MemAccessSize::Mem8 || !mem.is_global() {
                    return;
                }
                let op = ctx.memory(mem);
                if found.is_some_and(|x| x != op) {
                    return;
                }
                found = Some(op);
            }
        }
        self.result.sync_slot_index = found;
    }

    /// The check kind of the turn is `sync_check_kinds[sync_check_kind_index]`. The kind is
    /// matched where it is read rather than where it is stored into the slot, since the
    /// register holding it does not survive the state hashing calls in between.
    fn check_check_kinds(&mut self, ctx: OperandCtx<'e>, value: Operand<'e>) {
        let kind_index = match self.result.sync_check_kind_index {
            Some(s) => s,
            None => return,
        };
        if self.result.sync_check_kinds.is_some() {
            return;
        }
        if let Some(mem) = value.if_memory() {
            let (index, array) = mem.address();
            if array > 0x1000 && index.iter().any(|x| x == kind_index) {
                self.result.sync_check_kinds = Some(ctx.constant(array));
            }
        }
    }

    /// The turn's map row is `sync_map_row_index * map_width_tiles` tiles into map_tile_flags.
    fn check_map_row(&mut self, ctx: OperandCtx<'e>, value: Operand<'e>) {
        let (l, r) = match value.unwrap_and_mask().if_arithmetic_mul() {
            Some(s) => s,
            None => return,
        };
        for &(width, row) in &[(l, r), (r, l)] {
            if width.unwrap_and_mask().if_mem16_offset(0xe4).is_none() {
                continue;
            }
            let row = row.unwrap_sext().unwrap_and_mask();
            if let Some(mem) = row.if_memory() {
                if mem.size == MemAccessSize::Mem32 && mem.if_constant_address().is_some() {
                    self.result.sync_map_row_index = Some(ctx.memory(mem));
                    return;
                }
            }
        }
    }

    /// Both cursors are stepped as `index + 1` and wrapped back to zero when the sum reaches
    /// their bound; the bound is a constant for the ring slots and a global for the kinds.
    fn check_cursor_wrap(&mut self, ctx: OperandCtx<'e>, condition: Operand<'e>) {
        let condition = condition.if_arithmetic_eq_neq_zero(ctx)
            .map(|x| x.0)
            .unwrap_or(condition);
        let (l, r) = match condition.if_arithmetic(ArithOpType::GreaterThan) {
            Some(s) => s,
            None => return,
        };
        for &(bound, index) in &[(l, r), (r, l)] {
            let index = match index.unwrap_and_mask().if_arithmetic_add_const(1) {
                Some(s) => s,
                None => continue,
            };
            let index = match index.unwrap_and_mask().if_memory() {
                Some(s) if s.size == MemAccessSize::Mem8 && s.is_global() => s,
                _ => continue,
            };
            let index = ctx.memory(index);
            if let Some(c) = bound.if_constant() {
                // Ring slot counts are small; the wrap can be written either against the
                // count or against the last valid index.
                if c >= 2 && c <= 0x100 {
                    self.result.sync_slot_index = Some(index);
                }
            } else if let Some(count) = bound.unwrap_and_mask().if_memory() {
                if count.size == MemAccessSize::Mem8 && count.is_global() {
                    self.result.sync_check_kind_index = Some(index);
                    self.result.sync_check_kind_count = Some(ctx.memory(count));
                }
            }
            return;
        }
    }
}
