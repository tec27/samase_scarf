use std::rc::Rc;

use bumpalo::Bump;
use byteorder::{ByteOrder, LittleEndian};

use scarf::analysis::{FuncCallPair, RelocValues};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, BinarySection, MemAccessSize, Operand, OperandCtx};

use crate::ai::{self, AiScriptHook};
use crate::analysis_find::{FunctionFinder};
use crate::bullets;
use crate::campaign;
use crate::clientside;
use crate::commands;
use crate::crt;
use crate::dat::{self, DatTablePtr, DatPatch, DatPatches, DatReplaceFunc};
use crate::dialog;
use crate::eud::{self, EudTable};
use crate::file;
use crate::firegraft::{self, RequirementTables};
use crate::game::{self, Limits};
use crate::game_init;
use crate::iscript::{self, StepIscriptHook};
use crate::map::{self, RunTriggers, TriggerUnitCountCaches};
use crate::minimap;
use crate::network::{self, SnpDefinitions};
use crate::pathing;
use crate::players;
use crate::renderer::{self, PrismShaders};
use crate::requirements;
use crate::rng;
use crate::save;
use crate::sound;
use crate::step_order::{self, SecondaryOrderHook, StepOrderHiddenHook};
use crate::sprites;
use crate::switch::{CompleteSwitch};
use crate::text;
use crate::units;
use crate::vtables::{self, Vtables};
use crate::x86_64_globals;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FiregraftAddresses<Va: VirtualAddress> {
    pub buttonsets: Vec<Va>,
    pub requirement_table_refs: RequirementTables<Va>,
    pub unit_status_funcs: Vec<Va>,
}

#[derive(Clone, Debug)]
pub struct Patch<Va: VirtualAddress> {
    pub address: Va,
    pub data: Vec<u8>,
}

// Just since option spam for caches is a bit hard to keep track of
struct Cached<T: Clone>(Option<T>);

impl<T: Clone> Cached<T> {
    pub fn get_or_insert_with<F: FnOnce() -> T>(&mut self, fun: F) -> &mut T {
        self.0.get_or_insert_with(fun)
    }

    pub fn cached(&self) -> Option<T> {
        self.0.clone()
    }

    pub fn cache(&mut self, val: &T) {
        self.0 = Some(val.clone());
    }

    pub fn is_none(&self) -> bool {
        self.0.is_none()
    }
}

impl<T: Clone> Default for Cached<T> {
    fn default() -> Cached<T> {
        Cached(None)
    }
}

// Using repr(C) to make sure that the large, less accessed cache is placed last
// in this struct's layout
#[repr(C)]
pub struct Analysis<'e, E: ExecutionState<'e>> {
    shareable: AnalysisCtx<'e, E>,
    cache: AnalysisCache<'e, E>,
}

pub struct AnalysisCtx<'e, E: ExecutionState<'e>> {
    pub binary: &'e BinaryFile<E::VirtualAddress>,
    pub binary_sections: BinarySections<'e, E>,
    pub ctx: scarf::OperandCtx<'e>,
    pub arg_cache: ArgCache<'e, E>,
    pub bump: Bump,
}

pub struct BinarySections<'e, E: ExecutionState<'e>> {
    pub text: &'e BinarySection<E::VirtualAddress>,
    pub data: &'e BinarySection<E::VirtualAddress>,
    pub rdata: &'e BinarySection<E::VirtualAddress>,
}

macro_rules! results {
    (enum $name:ident {
        $($variant:ident => $variant_name:expr,)*
    }) => {
        #[derive(Copy, Clone, Debug)]
        pub enum $name {
            $($variant,)*
        }

        impl $name {
            const COUNT: usize = $( ($variant_name, 1).1 + )* 0;
            pub fn name(self) -> &'static str {
                match self {
                    $($name::$variant => $variant_name,)*
                }
            }

            pub fn iter() -> impl Iterator<Item = $name> {
                static ITEMS: [$name; $name::COUNT] = [
                    $($name::$variant,)*
                ];
                ITEMS.iter().copied()
            }
        }
    };
}

results! {
    enum AddressAnalysis {
        StepObjects => "step_objects",
        SendCommand => "send_command",
        PrintText => "print_text",
        AddToReplayData => "add_to_replay_data",
        StepOrder => "step_order",
        PrepareDrawImage => "prepare_draw_image",
        DrawImage => "draw_image",
        PlaySmk => "play_smk",
        AddOverlayIscript => "add_overlay_iscript",
        RunDialog => "run_dialog",
        GluCmpgnEventHandler => "glucmpgn_event_handler",
        AiUpdateAttackTarget => "ai_update_attack_target",
        IsOutsideGameScreen => "is_outside_game_screen",
        ChooseSnp => "choose_snp",
        LoadImages => "load_images",
        InitGameNetwork => "init_game_network",
        SpawnDialog => "spawn_dialog",
        TtfMalloc => "ttf_malloc",
        DrawGraphicLayers => "draw_graphic_layers",
        AiAttackPrepare => "ai_attack_prepare",
        JoinGame => "join_game",
        SnetInitializeProvider => "snet_initialize_provider",
        CheckDatRequirements => "check_dat_requirements",
        GiveAi => "give_ai",
        PlaySound => "play_sound",
        AiPrepareMovingTo => "ai_prepare_moving_to",
        StepReplayCommands => "step_replay_commands",
        AiTrainMilitary => "ai_train_military",
        AiAddMilitaryToRegion => "ai_add_military_to_region",
        GetRegion => "get_region",
        ChangeAiRegionState => "change_ai_region_state",
        InitGame => "init_game",
        CreateLoneSprite => "create_lone_sprite",
        CreateUnit => "create_unit",
        FinishUnitPre => "finish_unit_pre",
        FinishUnitPost => "finish_unit_post",
        InitSprites => "init_sprites",
        SerializeSprites => "serialize_sprites",
        DeserializeSprites => "deserialize_sprites",
        FontCacheRenderAscii => "font_cache_render_ascii",
        TtfCacheCharacter => "ttf_cache_character",
        TtfRenderSdf => "ttf_render_sdf",
        UpdateVisibilityPoint => "update_visibility_point",
        LayoutDrawText => "layout_draw_text",
        DrawF10MenuTooltip => "draw_f10_menu_tooltip",
        DrawTooltipLayer => "draw_tooltip_layer",
        SelectMapEntry => "select_map_entry",
        CreateBullet => "create_bullet",
        OrderInitArbiter => "order_init_arbiter",
        PrepareIssueOrder => "prepare_issue_order",
        DoNextQueuedOrder => "do_next_queued_order",
        ResetUiEventHandlers => "reset_ui_event_handlers",
        ClampZoom => "clamp_zoom",
        DrawMinimapUnits => "draw_minimap_units",
        InitNetPlayer => "init_net_player",
        ScMain => "sc_main",
        MainMenuEntryHook => "mainmenu_entry_hook",
        GameLoop => "game_loop",
        RunMenus => "run_menus",
        SinglePlayerStart => "single_player_start",
        InitUnits => "init_units",
        LoadDat => "load_dat",
        InitStormNetworking => "init_storm_networking",
        LoadSnpList => "load_snp_list",
        SetBriefingMusic => "set_briefing_music",
        PreMissionGlue => "pre_mission_glue",
        ShowMissionGlue => "show_mission_glue",
        MenuSwishIn => "menu_swish_in",
        MenuSwishOut => "menu_swish_out",
        AiSpellCast => "ai_spell_cast",
        GiveUnit => "give_unit",
        SetUnitPlayer => "set_unit_player",
        RemoveFromSelections => "remove_from_selections",
        RemoveFromClientSelection => "remove_from_client_selection",
        ClearBuildQueue => "clear_build_queue",
        UnitChangingPlayer => "unit_changing_player",
        PlayerGainedUpgrade => "player_gained_upgrade",
        UnitApplySpeedUpgrades => "unit_apply_speed_upgrades",
        UnitUpdateSpeed => "unit_update_speed",
        UnitUpdateSpeedIscript => "unit_update_speed_iscript",
        UnitBuffedFlingySpeed => "unit_buffed_flingy_speed",
        UnitBuffedAcceleration => "unit_buffed_acceleration",
        UnitBuffedTurnSpeed => "unit_buffed_turn_speed",
        StartUdpServer => "start_udp_server",
        OpenAnimSingleFile => "open_anim_single_file",
        OpenAnimMultiFile => "open_anim_multi_file",
        InitSkins => "init_skins",
        AddAssetChangeCallback => "add_asset_change_callback",
        AnimAssetChangeCb => "anim_asset_change_cb",
        InitRealTimeLighting => "init_real_time_lighting",
        StepActiveUnitFrame => "step_active_unit_frame",
        StepHiddenUnitFrame => "step_hidden_unit_frame",
        StepBulletFrame => "step_bullet_frame",
        RevealUnitArea => "reveal_unit_area",
        UpdateUnitVisibility => "update_unit_visibility",
        UpdateCloakState => "update_cloak_state",
        StepUnitMovement => "step_unit_movement",
        InitMapFromPath => "init_map_from_path",
        MapInitChkCallbacks => "map_init_chk_callbacks",
        StepNetwork => "step_network",
        ReceiveStormTurns => "receive_storm_turns",
        AiStepRegion => "ai_step_region",
        AiSpendMoney => "ai_spend_money",
        DoAttack => "do_attack",
        DoAttackMain => "do_attack_main",
        CheckUnitRequirements => "check_unit_requirements",
        SnetSendPackets => "snet_send_packets",
        SnetRecvPackets => "snet_recv_packets",
        OpenFile => "open_file",
        DrawGameLayer => "draw_game_layer",
        RenderScreen => "render_screen",
        LoadPcx => "load_pcx",
        SetMusic => "set_music",
        StepIscript => "step_iscript",
        StepIscriptSwitch => "step_iscript_switch",
        ProcessCommands => "process_commands",
        ProcessLobbyCommands => "process_lobby_commands",
        StepAiScript => "step_ai_script",
        StepGameLoop => "step_game_loop",
        StepGameLogic => "step_game_logic",
        ProcessEvents => "process_events",
        StepBnetController => "step_bnet_controller",
        CreateGameMultiplayer => "create_game_multiplayer",
        MapEntryLoadMap => "map_entry_load_map",
        MapEntryLoadSave => "map_entry_load_save",
        MapEntryLoadReplay => "map_entry_load_replay",
        GetMouseX => "get_mouse_x",
        GetMouseY => "get_mouse_y",
        AddPylonAura => "add_pylon_aura",
        SinglePlayerMapEnd => "single_player_map_end",
        SetScmainState => "set_scmain_state",
        UnlockMission => "unlock_mission",
        CreateFowSprite => "create_fow_sprite",
        DuplicateSprite => "duplicate_sprite",
        InitStatusScreen => "init_status_screen",
        StatusScreenEventHandler => "status_screen_event_handler",
        NetFormatTurnRate => "net_format_turn_rate",
        LoadReplayScenarioChk => "load_replay_scenario_chk",
        SfileCloseArchive => "sfile_close_archive",
        OpenMapMpq => "open_map_mpq",
        // arg 1 void *mpq_handle, arg 2 char *filename, arg 3 u8 *out_ptr arg 4 u32 *out_size,
        // arg 5 extra_out_size (0), arg 6 storm flags (0), arg 7 unk opt ptr? (0); stdcall
        ReadWholeMpqFile => "read_whole_mpq_file",
        // Takes 8th argument which is unused anyway but affects calling convention
        // so have separate analysis result for it.
        ReadWholeMpqFile2 => "read_whole_mpq_file2",
        TargetingLClick => "targeting_lclick",
        TargetingRClick => "targeting_rclick",
        BuildingPlacementLClick => "building_placement_lclick",
        BuildingPlacementRClick => "building_placement_rclick",
        // These are active when not targeting / placing building
        GameScreenLClick => "game_screen_lclick",
        GameScreenRClick => "game_screen_rclick",
        UiDefaultKeyDownHandler => "ui_default_key_down_handler",
        UiDefaultKeyUpHandler => "ui_default_key_up_handler",
        UiDefaultLeftDownHandler => "ui_default_left_down_handler",
        UiDefaultLeftDoubleHandler => "ui_default_left_double_handler",
        UiDefaultRightDownHandler => "ui_default_right_down_handler",
        UiDefaultMiddleDownHandler => "ui_default_middle_down_handler",
        UiDefaultMiddleUpHandler => "ui_default_middle_up_handler",
        UiDefaultPeriodicHandler => "ui_default_periodic_handler",
        UiDefaultCharHandler => "ui_default_char_handler",
        UiDefaultScrollHandler => "ui_default_scroll_handler",
        StartTargeting => "start_targeting",
        FindUnitForClick => "find_unit_for_click",
        FindFowSpriteForClick => "find_fow_sprite_for_click",
        HandleTargetedClick => "handle_targeted_click",
        CheckWeaponTargetingFlags => "check_weapon_targeting_flags",
        CheckTechTargeting => "check_tech_targeting",
        CheckOrderTargeting => "check_order_targeting",
        CheckFowOrderTargeting => "check_fow_order_targeting",
        AiFocusDisabled => "ai_focus_disabled",
        AiFocusAir => "ai_focus_air",
        FileExists => "file_exists",
    }
}

results! {
    enum OperandAnalysis {
        Game => "game",
        Pathing => "pathing",
        CommandUser => "command_user",
        IsReplay => "is_replay",
        LocalPlayerId => "local_player_id",
        LocalPlayerName => "local_player_name",
        LobbyState => "lobby_state",
        DrawCursorMarker => "draw_cursor_marker",
        Units => "units",
        FirstAiScript => "first_ai_script",
        FirstGuardAi => "first_guard_ai",
        PlayerAiTowns => "player_ai_towns",
        PlayerAi => "player_ai",
        Players => "players",
        Campaigns => "campaigns",
        Fonts => "fonts",
        StatusScreenMode => "status_screen_mode",
        CheatFlags => "cheat_flags",
        UnitStrength => "unit_strength",
        SpriteIncludeInVisionSync => "sprite_include_in_vision_sync",
        WireframDdsgrp => "wirefram_ddsgrp",
        ChkInitPlayers => "chk_init_players",
        OriginalChkPlayerTypes => "original_chk_player_types",
        AiTransportReachabilityCachedRegion => "ai_transport_reachability_cached_region",
        PlayerUnitSkins => "player_unit_skins",
        ReplayData => "replay_data",
        VertexBuffer => "vertex_buffer",
        RngSeed => "rng_seed",
        RngEnable => "rng_enable",
        AiRegions => "ai_regions",
        LoadedSave => "loaded_save",
        SpriteHlines => "sprite_hlines",
        SpriteHlinesEnd => "sprite_hlines_end",
        FirstFreeSprite => "first_free_sprite",
        LastFreeSprite => "last_free_sprite",
        FirstLoneSprite => "first_lone_sprite",
        LastLoneSprite => "last_lone_sprite",
        FirstFreeLoneSprite => "first_free_lone_sprite",
        LastFreeLoneSprite => "last_free_lone_sprite",
        ScreenX => "screen_x",
        ScreenY => "screen_y",
        Zoom => "zoom",
        FirstFowSprite => "first_fow_sprite",
        LastFowSprite => "last_fow_sprite",
        FirstFreeFowSprite => "first_free_fow_sprite",
        LastFreeFowSprite => "last_free_fow_sprite",
        Sprites => "sprites",
        FirstActiveUnit => "first_active_unit",
        FirstHiddenUnit => "first_hidden_unit",
        MapTileFlags => "map_tile_flags",
        TooltipDrawFunc => "tooltip_draw_func",
        CurrentTooltipCtrl => "current_tooltip_ctrl",
        GraphicLayers => "graphic_layers",
        IsMultiplayer => "is_multiplayer",
        FirstActiveBullet => "first_active_bullet",
        LastActiveBullet => "last_active_bullet",
        FirstFreeBullet => "first_free_bullet",
        LastFreeBullet => "last_free_bullet",
        ActiveIscriptUnit => "active_iscript_unit",
        UniqueCommandUser => "unique_command_user",
        Selections => "selections",
        GlobalEventHandlers => "global_event_handlers",
        ReplayVisions => "replay_visions",
        ReplayShowEntireMap => "replay_show_entire_map",
        FirstPlayerUnit => "first_player_unit",
        NetPlayers => "net_players",
        ScMainState => "scmain_state",
        LocalStormPlayerId => "local_storm_player_id",
        LocalUniquePlayerId => "local_unique_player_id",
        NetPlayerToGame => "net_player_to_game",
        NetPlayerToUnique => "net_player_to_unique",
        GameData => "game_data",
        Skins => "skins",
        PlayerSkins => "player_skins",
        IsPaused => "is_paused",
        IsPlacingBuilding => "is_placing_building",
        IsTargeting => "is_targeting",
        ClientSelection => "client_selection",
        DialogReturnCode => "dialog_return_code",
        BaseAnimSet => "base_anim_set",
        ImageGrps => "image_grps",
        ImageOverlays => "image_overlays",
        FireOverlayMax => "fire_overlay_max",
        AssetScale => "asset_scale",
        ImagesLoaded => "images_loaded",
        VisionUpdateCounter => "vision_update_counter",
        VisionUpdated => "vision_updated",
        FirstDyingUnit => "first_dying_unit",
        FirstRevealer => "first_revealer",
        FirstInvisibleUnit => "first_invisible_unit",
        ActiveIscriptFlingy => "active_iscript_flingy",
        ActiveIscriptBullet => "active_iscript_bullet",
        UnitShouldRevealArea => "unit_should_reveal_area",
        MenuScreenId => "menu_screen_id",
        NetPlayerFlags => "net_player_flags",
        PlayerTurns => "player_turns",
        PlayerTurnsSize => "player_turns_size",
        NetworkReady => "network_ready",
        NetUserLatency => "net_user_latency",
        LastBulletSpawner => "last_bullet_spawner",
        CmdIconsDdsGrp => "cmdicons_ddsgrp",
        CmdBtnsDdsGrp => "cmdbtns_ddsgrp",
        DatRequirementError => "dat_requirement_error",
        CursorMarker => "cursor_marker",
        MainPalette => "main_palette",
        PaletteSet => "palette_set",
        TfontGam => "tfontgam",
        SyncActive => "sync_active",
        SyncData => "sync_data",
        IscriptBin => "iscript_bin",
        StormCommandUser => "storm_command_user",
        FirstFreeOrder => "first_free_order",
        LastFreeOrder => "last_free_order",
        AllocatedOrderCount => "allocated_order_count",
        ReplayBfix => "replay_bfix",
        ReplayGcfg => "replay_gcfg",
        ContinueGameLoop => "continue_game_loop",
        AntiTroll => "anti_troll",
        StepGameFrames => "step_game_frames",
        NextGameStepTick => "next_game_step_tick",
        ReplaySeekFrame => "replay_seek_frame",
        BnetController => "bnet_controller",
        MouseX => "mouse_x",
        MouseY => "mouse_y",
        FirstPylon => "first_pylon",
        PylonAurasVisible => "pylon_auras_visible",
        PylonRefresh => "pylon_refresh",
        LocalGameResult => "local_game_result",
        IsCustomSinglePlayer => "is_custom_single_player",
        CurrentCampaignMission => "current_campaign_mission",
        LocalVisions => "local_visions",
        FirstFreeSelectionCircle => "first_free_selection_circle",
        LastFreeSelectionCircle => "last_free_selection_circle",
        UnitSkinMap => "unit_skin_map",
        SpriteSkinMap => "sprite_skin_map",
        GrpWireGrp => "grpwire_grp",
        GrpWireDdsGrp => "grpwire_ddsgrp",
        TranWireGrp => "tranwire_grp",
        TranWireDdsGrp => "tranwire_ddsgrp",
        StatusScreen => "status_screen",
        ReplayScenarioChk => "replay_scenario_chk",
        ReplayScenarioChkSize => "replay_scenario_chk_size",
        MapMpq => "map_mpq",
        MapHistory => "map_history",
        GameScreenLClickCallback => "game_screen_lclick_callback",
        GameScreenRClickCallback => "game_screen_rclick_callback",
        TargetedOrderUnit => "targeted_order_unit",
        TargetedOrderGround => "targeted_order_fow",
        TargetedOrderFow => "targeted_order_ground",
        MinimapCursorType => "minimap_cursor_type",
    }
}

pub struct AnalysisCache<'e, E: ExecutionState<'e>> {
    binary: &'e BinaryFile<E::VirtualAddress>,
    text: &'e BinarySection<E::VirtualAddress>,
    relocs: Cached<Rc<Vec<E::VirtualAddress>>>,
    globals_with_values: Cached<Rc<Vec<RelocValues<E::VirtualAddress>>>>,
    functions: Cached<Rc<Vec<E::VirtualAddress>>>,
    functions_with_callers: Cached<Rc<Vec<FuncCallPair<E::VirtualAddress>>>>,
    vtables: Cached<Rc<Vtables<'e, E::VirtualAddress>>>,
    firegraft_addresses: Cached<Rc<FiregraftAddresses<E::VirtualAddress>>>,
    aiscript_hook: Option<AiScriptHook<'e, E::VirtualAddress>>,
    // 0 = Not calculated, 1 = Not found
    address_results: [E::VirtualAddress; AddressAnalysis::COUNT],
    // None = Not calculated, Custom(1234578) = Not found
    operand_results: [Option<Operand<'e>>; OperandAnalysis::COUNT],
    operand_not_found: Operand<'e>,
    process_commands_switch: Cached<Option<CompleteSwitch<'e>>>,
    process_lobby_commands_switch: Cached<Option<CompleteSwitch<'e>>>,
    bnet_message_switch: Option<CompleteSwitch<'e>>,
    command_lengths: Cached<Rc<Vec<u32>>>,
    step_order_hidden: Cached<Rc<Vec<StepOrderHiddenHook<'e, E::VirtualAddress>>>>,
    step_secondary_order: Cached<Rc<Vec<SecondaryOrderHook<'e, E::VirtualAddress>>>>,
    step_iscript_hook: Option<StepIscriptHook<'e, E::VirtualAddress>>,
    sprite_x_position: Option<(Operand<'e>, u32, MemAccessSize)>,
    sprite_y_position: Option<(Operand<'e>, u32, MemAccessSize)>,
    eud: Cached<Rc<EudTable<'e>>>,
    renderer_vtables: Cached<Rc<Vec<E::VirtualAddress>>>,
    snp_definitions: Cached<Option<SnpDefinitions<'e>>>,
    sprite_struct_size: u16,
    net_player_size: u16,
    skins_size: u16,
    anim_struct_size: u16,
    bnet_message_vtable_type: u16,
    create_game_dialog_vtbl_on_multiplayer_create: u16,
    join_param_variant_type_offset: u16,
    limits: Cached<Rc<Limits<'e, E::VirtualAddress>>>,
    prism_shaders: Cached<PrismShaders<E::VirtualAddress>>,
    dat_patches: Cached<Option<Rc<DatPatches<'e, E::VirtualAddress>>>>,
    run_triggers: Cached<RunTriggers<E::VirtualAddress>>,
    trigger_unit_count_caches: Cached<TriggerUnitCountCaches<'e>>,
    replay_minimap_unexplored_fog_patch: Cached<Option<Rc<Patch<E::VirtualAddress>>>>,
    crt_fastfail: Cached<Rc<Vec<E::VirtualAddress>>>,
    dat_tables: DatTables<'e>,
}

pub struct ArgCache<'e, E: ExecutionState<'e>> {
    args: [Operand<'e>; 8],
    ctx: scarf::OperandCtx<'e>,
    phantom: std::marker::PhantomData<E>,
}

impl<'e, E: ExecutionState<'e>> ArgCache<'e, E> {
    fn new(ctx: OperandCtx<'e>) -> ArgCache<'e, E> {
        let is_x64 = <E::VirtualAddress as VirtualAddress>::SIZE == 8;
        let stack_pointer = ctx.register(4);
        let args = array_init::array_init(|i| {
            if is_x64 {
                match i {
                    0 => ctx.register(1),
                    1 => ctx.register(2),
                    2 => ctx.register(8),
                    3 => ctx.register(9),
                    _ => ctx.mem64(
                        stack_pointer,
                        i as u64 * 8,
                    ),
                }
            } else {
                ctx.mem32(
                    stack_pointer,
                    i as u64 * 4,
                )
            }
        });
        ArgCache {
            args,
            ctx,
            phantom: std::marker::PhantomData,
        }
    }

    /// Returns operand corresponding to location of argument *before* call instruction
    /// is executed.
    pub fn on_call(&self, index: u8) -> Operand<'e> {
        if (index as usize) < self.args.len() {
            self.args[index as usize]
        } else {
            let size = <E::VirtualAddress as VirtualAddress>::SIZE as u64;
            let is_x64 = <E::VirtualAddress as VirtualAddress>::SIZE == 8;
            let stack_pointer = self.ctx.register(4);
            let mem_size = match is_x64 {
                true => MemAccessSize::Mem64,
                false => MemAccessSize::Mem32,
            };
            self.ctx.mem_any(
                mem_size,
                stack_pointer,
                index as u64 * size,
            )
        }
    }

    /// Returns operand corresponding to location of nth non-this argument *before*
    /// call instruction when calling convention is thiscall.
    pub fn on_thiscall_call(&self, index: u8) -> Operand<'e> {
        let is_x64 = <E::VirtualAddress as VirtualAddress>::SIZE == 8;
        if !is_x64 {
            self.on_call(index)
        } else {
            self.on_call(index + 1)
        }
    }

    /// Returns operand corresponding to location of argument *on function entry*.
    pub fn on_entry(&self, index: u8) -> Operand<'e> {
        let is_x64 = <E::VirtualAddress as VirtualAddress>::SIZE == 8;
        let ctx = self.ctx;
        let stack_pointer = ctx.register(4);
        if !is_x64 {
            if index as usize + 1 < self.args.len() {
                self.args[index as usize + 1]
            } else {
                ctx.mem32(
                    stack_pointer,
                    (index as u64 + 1) * 4,
                )
            }
        } else {
            if index < 4 {
                self.args[index as usize]
            } else {
                ctx.mem64(
                    stack_pointer,
                    (index as u64 + 1) * 8,
                )
            }
        }
    }

    /// Returns operand corresponding to location of nth non-this argument *on function entry*
    /// when calling convention is thiscall.
    pub fn on_thiscall_entry(&self, index: u8) -> Operand<'e> {
        let is_x64 = <E::VirtualAddress as VirtualAddress>::SIZE == 8;
        if !is_x64 {
            self.on_entry(index)
        } else {
            self.on_entry(index + 1)
        }
    }
}

macro_rules! declare_dat {
    ($($struct_field:ident, $filename:expr, $enum_variant:ident,)*) => {
        struct DatTables<'e> {
            $($struct_field: Option<Option<DatTablePtr<'e>>>,)*
        }

        impl<'e> DatTables<'e> {
            fn new() -> DatTables<'e> {
                DatTables {
                    $($struct_field: None,)*
                }
            }

            fn field(&mut self, field: DatType) ->
                (&mut Option<Option<DatTablePtr<'e>>>, &'static str)
            {
                match field {
                    $(DatType::$enum_variant =>
                      (&mut self.$struct_field, concat!("arr\\", $filename)),)*
                }
            }
        }

        #[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
        pub enum DatType {
            $($enum_variant,)*
        }
    }
}

declare_dat! {
    units, "units.dat", Units,
    weapons, "weapons.dat", Weapons,
    flingy, "flingy.dat", Flingy,
    upgrades, "upgrades.dat", Upgrades,
    techdata, "techdata.dat", TechData,
    sprites, "sprites.dat", Sprites,
    images, "images.dat", Images,
    orders, "orders.dat", Orders,
    sfxdata, "sfxdata.dat", SfxData,
    portdata, "portdata.dat", PortData,
    mapdata, "mapdata.dat", MapData,
}

impl<'e, E: ExecutionState<'e>> Analysis<'e, E> {
    pub fn new(
        binary: &'e BinaryFile<E::VirtualAddress>,
        ctx: scarf::OperandCtx<'e>,
    ) -> Analysis<'e, E> {
        let text = binary.section(b".text\0\0\0").unwrap();
        Analysis {
            cache: AnalysisCache {
                binary,
                text,
                relocs: Default::default(),
                globals_with_values: Default::default(),
                functions: Default::default(),
                functions_with_callers: Default::default(),
                vtables: Default::default(),
                firegraft_addresses: Default::default(),
                aiscript_hook: Default::default(),
                address_results:
                    [E::VirtualAddress::from_u64(0); AddressAnalysis::COUNT],
                operand_results: [None; OperandAnalysis::COUNT],
                operand_not_found: ctx.custom(0x12345678),
                process_commands_switch: Default::default(),
                process_lobby_commands_switch: Default::default(),
                bnet_message_switch: Default::default(),
                command_lengths: Default::default(),
                step_order_hidden: Default::default(),
                step_secondary_order: Default::default(),
                step_iscript_hook: Default::default(),
                sprite_x_position: Default::default(),
                sprite_y_position: Default::default(),
                eud: Default::default(),
                renderer_vtables: Default::default(),
                snp_definitions: Default::default(),
                sprite_struct_size: 0,
                net_player_size: 0,
                skins_size: 0,
                anim_struct_size: 0,
                bnet_message_vtable_type: 0,
                create_game_dialog_vtbl_on_multiplayer_create: 0,
                join_param_variant_type_offset: u16::MAX,
                limits: Default::default(),
                prism_shaders: Default::default(),
                dat_patches: Default::default(),
                run_triggers: Default::default(),
                trigger_unit_count_caches: Default::default(),
                replay_minimap_unexplored_fog_patch: Default::default(),
                crt_fastfail: Default::default(),
                dat_tables: DatTables::new(),
            },
            shareable: AnalysisCtx {
                binary,
                binary_sections: BinarySections {
                    rdata: binary.section(b".rdata\0\0").unwrap(),
                    data: binary.section(b".data\0\0\0").unwrap(),
                    text,
                },
                ctx,
                bump: Bump::new(),
                arg_cache: ArgCache::new(ctx),
            },
        }
    }

    pub fn ctx(&self) -> OperandCtx<'e> {
        self.shareable.ctx
    }

    fn is_valid_function(address: E::VirtualAddress) -> bool {
        address.as_u64() & 0xf == 0
    }

    /// Entry point for any analysis calls.
    /// Creates AnalysisCtx from self that is used across actual analysis functions.
    fn enter<F: for<'b> FnOnce(&mut AnalysisCache<'e, E>, &AnalysisCtx<'e, E>) -> R, R>(
        &mut self,
        func: F,
    ) -> R {
        let ret = func(&mut self.cache, &self.shareable);
        self.shareable.bump.reset();
        ret
    }

    pub fn address_analysis(&mut self, addr: AddressAnalysis) -> Option<E::VirtualAddress> {
        use self::AddressAnalysis::*;
        match addr {
            StepObjects => self.step_objects(),
            SendCommand => self.send_command(),
            PrintText => self.print_text(),
            AddToReplayData => self.add_to_replay_data(),
            StepOrder => self.step_order(),
            PrepareDrawImage => self.prepare_draw_image(),
            DrawImage => self.draw_image(),
            PlaySmk => self.play_smk(),
            AddOverlayIscript => self.add_overlay_iscript(),
            RunDialog => self.run_dialog(),
            GluCmpgnEventHandler => self.glucmpgn_event_handler(),
            AiUpdateAttackTarget => self.ai_update_attack_target(),
            IsOutsideGameScreen => self.is_outside_game_screen(),
            ChooseSnp => self.choose_snp(),
            LoadImages => self.load_images(),
            InitGameNetwork => self.init_game_network(),
            SpawnDialog => self.spawn_dialog(),
            TtfMalloc => self.ttf_malloc(),
            DrawGraphicLayers => self.draw_graphic_layers(),
            AiAttackPrepare => self.ai_attack_prepare(),
            JoinGame => self.join_game(),
            SnetInitializeProvider => self.snet_initialize_provider(),
            CheckDatRequirements => self.check_dat_requirements(),
            GiveAi => self.give_ai(),
            PlaySound => self.play_sound(),
            AiPrepareMovingTo => self.ai_prepare_moving_to(),
            StepReplayCommands => self.step_replay_commands(),
            AiTrainMilitary => self.ai_train_military(),
            AiAddMilitaryToRegion => self.ai_add_military_to_region(),
            GetRegion => self.get_region(),
            ChangeAiRegionState => self.change_ai_region_state(),
            InitGame => self.init_game(),
            CreateLoneSprite => self.create_lone_sprite(),
            CreateUnit => self.create_unit(),
            FinishUnitPre => self.finish_unit_pre(),
            FinishUnitPost => self.finish_unit_post(),
            InitSprites => self.init_sprites(),
            SerializeSprites => self.serialize_sprites(),
            DeserializeSprites => self.deserialize_sprites(),
            FontCacheRenderAscii => self.font_cache_render_ascii(),
            TtfCacheCharacter => self.ttf_cache_character(),
            TtfRenderSdf => self.ttf_render_sdf(),
            UpdateVisibilityPoint => self.update_visibility_point(),
            LayoutDrawText => self.layout_draw_text(),
            DrawF10MenuTooltip => self.draw_f10_menu_tooltip(),
            DrawTooltipLayer => self.draw_tooltip_layer(),
            SelectMapEntry => self.select_map_entry(),
            CreateBullet => self.create_bullet(),
            OrderInitArbiter => self.order_init_arbiter(),
            PrepareIssueOrder => self.prepare_issue_order(),
            DoNextQueuedOrder => self.do_next_queued_order(),
            ResetUiEventHandlers => self.reset_ui_event_handlers(),
            UiDefaultScrollHandler => self.ui_default_scroll_handler(),
            ClampZoom => self.clamp_zoom(),
            DrawMinimapUnits => self.draw_minimap_units(),
            InitNetPlayer => self.init_net_player(),
            ScMain => self.sc_main(),
            MainMenuEntryHook => self.mainmenu_entry_hook(),
            GameLoop => self.game_loop(),
            RunMenus => self.run_menus(),
            SinglePlayerStart => self.single_player_start(),
            InitUnits => self.init_units(),
            LoadDat => self.load_dat(),
            GameScreenRClick => self.game_screen_rclick(),
            InitStormNetworking => self.init_storm_networking(),
            LoadSnpList => self.load_snp_list(),
            SetBriefingMusic => self.set_briefing_music(),
            PreMissionGlue => self.pre_mission_glue(),
            ShowMissionGlue => self.show_mission_glue(),
            MenuSwishIn => self.menu_swish_in(),
            MenuSwishOut => self.menu_swish_out(),
            AiSpellCast => self.ai_spell_cast(),
            GiveUnit => self.give_unit(),
            SetUnitPlayer => self.set_unit_player(),
            RemoveFromSelections => self.remove_from_selections(),
            RemoveFromClientSelection => self.remove_from_client_selection(),
            ClearBuildQueue => self.clear_build_queue(),
            UnitChangingPlayer => self.unit_changing_player(),
            PlayerGainedUpgrade => self.player_gained_upgrade(),
            UnitApplySpeedUpgrades => self.unit_apply_speed_upgrades(),
            UnitUpdateSpeed => self.unit_update_speed(),
            UnitUpdateSpeedIscript => self.unit_update_speed_iscript(),
            UnitBuffedFlingySpeed => self.unit_buffed_flingy_speed(),
            UnitBuffedAcceleration => self.unit_buffed_acceleration(),
            UnitBuffedTurnSpeed => self.unit_buffed_turn_speed(),
            StartUdpServer => self.start_udp_server(),
            OpenAnimSingleFile => self.open_anim_single_file(),
            OpenAnimMultiFile => self.open_anim_multi_file(),
            InitSkins => self.init_skins(),
            AddAssetChangeCallback => self.add_asset_change_callback(),
            AnimAssetChangeCb => self.anim_asset_change_cb(),
            InitRealTimeLighting => self.init_real_time_lighting(),
            StepActiveUnitFrame => self.step_active_unit_frame(),
            StepHiddenUnitFrame => self.step_hidden_unit_frame(),
            StepBulletFrame => self.step_bullet_frame(),
            RevealUnitArea => self.reveal_unit_area(),
            UpdateUnitVisibility => self.update_unit_visibility(),
            UpdateCloakState => self.update_cloak_state(),
            StepUnitMovement => self.step_unit_movement(),
            InitMapFromPath => self.init_map_from_path(),
            MapInitChkCallbacks => self.map_init_chk_callbacks(),
            StepNetwork => self.step_network(),
            ReceiveStormTurns => self.receive_storm_turns(),
            AiStepRegion => self.ai_step_region(),
            AiSpendMoney => self.ai_spend_money(),
            DoAttack => self.do_attack(),
            DoAttackMain => self.do_attack_main(),
            CheckUnitRequirements => self.check_unit_requirements(),
            SnetSendPackets => self.snet_send_packets(),
            SnetRecvPackets => self.snet_recv_packets(),
            OpenFile => self.open_file(),
            DrawGameLayer => self.draw_game_layer(),
            RenderScreen => self.render_screen(),
            LoadPcx => self.load_pcx(),
            SetMusic => self.set_music(),
            StepIscript => self.step_iscript(),
            StepIscriptSwitch => self.step_iscript_switch(),
            ProcessCommands => self.process_commands(),
            ProcessLobbyCommands => self.process_lobby_commands(),
            StepAiScript => self.step_ai_script(),
            StepGameLoop => self.step_game_loop(),
            StepGameLogic => self.step_game_logic(),
            ProcessEvents => self.process_events(),
            StepBnetController => self.step_bnet_controller(),
            CreateGameMultiplayer => self.create_game_multiplayer(),
            MapEntryLoadMap => self.map_entry_load_map(),
            MapEntryLoadSave => self.map_entry_load_save(),
            MapEntryLoadReplay => self.map_entry_load_replay(),
            GetMouseX => self.get_mouse_x(),
            GetMouseY => self.get_mouse_y(),
            AddPylonAura => self.add_pylon_aura(),
            SinglePlayerMapEnd => self.single_player_map_end(),
            SetScmainState => self.set_scmain_state(),
            UnlockMission => self.unlock_mission(),
            CreateFowSprite => self.create_fow_sprite(),
            DuplicateSprite => self.duplicate_sprite(),
            InitStatusScreen => self.init_status_screen(),
            StatusScreenEventHandler => self.status_screen_event_handler(),
            NetFormatTurnRate => self.net_format_turn_rate(),
            LoadReplayScenarioChk => self.load_replay_scenario_chk(),
            SfileCloseArchive => self.sfile_close_archive(),
            OpenMapMpq => self.open_map_mpq(),
            ReadWholeMpqFile => self.read_whole_mpq_file(),
            ReadWholeMpqFile2 => self.read_whole_mpq_file2(),
            TargetingLClick => self.targeting_lclick(),
            TargetingRClick => self.targeting_rclick(),
            BuildingPlacementLClick => self.building_placement_lclick(),
            BuildingPlacementRClick => self.building_placement_rclick(),
            GameScreenLClick => self.game_screen_l_click(),
            UiDefaultKeyDownHandler => self.ui_default_key_down_handler(),
            UiDefaultKeyUpHandler => self.ui_default_key_up_handler(),
            UiDefaultLeftDownHandler => self.ui_default_left_down_handler(),
            UiDefaultLeftDoubleHandler => self.ui_default_left_double_handler(),
            UiDefaultRightDownHandler => self.ui_default_right_down_handler(),
            UiDefaultMiddleDownHandler => self.ui_default_middle_down_handler(),
            UiDefaultMiddleUpHandler => self.ui_default_middle_up_handler(),
            UiDefaultPeriodicHandler => self.ui_default_periodic_handler(),
            UiDefaultCharHandler => self.ui_default_char_handler(),
            StartTargeting => self.start_targeting(),
            FindUnitForClick => self.find_unit_for_click(),
            FindFowSpriteForClick => self.find_fow_sprite_for_click(),
            HandleTargetedClick => self.handle_targeted_click(),
            CheckWeaponTargetingFlags => self.check_weapon_targeting_flags(),
            CheckTechTargeting => self.check_tech_targeting(),
            CheckOrderTargeting => self.check_order_targeting(),
            CheckFowOrderTargeting => self.check_fow_order_targeting(),
            AiFocusDisabled => self.ai_focus_disabled(),
            AiFocusAir => self.ai_focus_air(),
            FileExists => self.file_exists(),
        }
    }

    pub fn operand_analysis(&mut self, addr: OperandAnalysis) -> Option<Operand<'e>> {
        use self::OperandAnalysis::*;
        match addr {
            Game => self.game(),
            Pathing => self.pathing(),
            CommandUser => self.command_user(),
            IsReplay => self.is_replay(),
            LocalPlayerId => self.local_player_id(),
            LocalPlayerName => self.local_player_name(),
            LobbyState => self.lobby_state(),
            DrawCursorMarker => self.draw_cursor_marker(),
            Units => self.units(),
            FirstAiScript => self.first_ai_script(),
            FirstGuardAi => self.first_guard_ai(),
            PlayerAiTowns => self.player_ai_towns(),
            PlayerAi => self.player_ai(),
            Players => self.players(),
            Campaigns => self.campaigns(),
            Fonts => self.fonts(),
            StatusScreenMode => self.status_screen_mode(),
            CheatFlags => self.cheat_flags(),
            UnitStrength => self.unit_strength(),
            SpriteIncludeInVisionSync => self.sprite_include_in_vision_sync(),
            WireframDdsgrp => self.wirefram_ddsgrp(),
            ChkInitPlayers => self.chk_init_players(),
            OriginalChkPlayerTypes => self.original_chk_player_types(),
            AiTransportReachabilityCachedRegion => self.ai_transport_reachability_cached_region(),
            PlayerUnitSkins => self.player_unit_skins(),
            ReplayData => self.replay_data(),
            VertexBuffer => self.vertex_buffer(),
            RngSeed => self.rng_seed(),
            RngEnable => self.rng_enable(),
            AiRegions => self.ai_regions(),
            LoadedSave => self.loaded_save(),
            SpriteHlines => self.sprite_hlines(),
            SpriteHlinesEnd => self.sprite_hlines_end(),
            FirstFreeSprite => self.first_free_sprite(),
            LastFreeSprite => self.last_free_sprite(),
            FirstLoneSprite => self.first_lone_sprite(),
            LastLoneSprite => self.last_lone_sprite(),
            FirstFreeLoneSprite => self.first_free_lone_sprite(),
            LastFreeLoneSprite => self.last_free_lone_sprite(),
            ScreenX => self.screen_x(),
            ScreenY => self.screen_y(),
            Zoom => self.zoom(),
            FirstFowSprite => self.first_fow_sprite(),
            LastFowSprite => self.last_fow_sprite(),
            FirstFreeFowSprite => self.first_free_fow_sprite(),
            LastFreeFowSprite => self.last_free_fow_sprite(),
            Sprites => self.sprite_array().map(|x| x.0),
            FirstActiveUnit => self.first_active_unit(),
            FirstHiddenUnit => self.first_hidden_unit(),
            MapTileFlags => self.map_tile_flags(),
            TooltipDrawFunc => self.tooltip_draw_func(),
            CurrentTooltipCtrl => self.current_tooltip_ctrl(),
            GraphicLayers => self.graphic_layers(),
            IsMultiplayer => self.is_multiplayer(),
            FirstActiveBullet => self.first_active_bullet(),
            LastActiveBullet => self.last_active_bullet(),
            FirstFreeBullet => self.first_free_bullet(),
            LastFreeBullet => self.last_free_bullet(),
            ActiveIscriptUnit => self.active_iscript_unit(),
            UniqueCommandUser => self.unique_command_user(),
            Selections => self.selections(),
            GlobalEventHandlers => self.global_event_handlers(),
            ReplayVisions => self.replay_visions(),
            ReplayShowEntireMap => self.replay_show_entire_map(),
            FirstPlayerUnit => self.first_player_unit(),
            NetPlayers => self.net_players().map(|x| x.0),
            ScMainState => self.scmain_state(),
            LocalStormPlayerId => self.local_storm_player_id(),
            LocalUniquePlayerId => self.local_unique_player_id(),
            NetPlayerToGame => self.net_player_to_game(),
            NetPlayerToUnique => self.net_player_to_unique(),
            GameData => self.game_data(),
            Skins => self.skins(),
            PlayerSkins => self.player_skins(),
            IsPaused => self.is_paused(),
            IsPlacingBuilding => self.is_placing_building(),
            IsTargeting => self.is_targeting(),
            ClientSelection => self.client_selection(),
            DialogReturnCode => self.dialog_return_code(),
            BaseAnimSet => self.base_anim_set(),
            ImageGrps => self.image_grps(),
            ImageOverlays => self.image_overlays(),
            FireOverlayMax => self.fire_overlay_max(),
            AssetScale => self.asset_scale(),
            ImagesLoaded => self.images_loaded(),
            VisionUpdateCounter => self.vision_update_counter(),
            VisionUpdated => self.vision_updated(),
            FirstDyingUnit => self.first_dying_unit(),
            FirstRevealer => self.first_revealer(),
            FirstInvisibleUnit => self.first_invisible_unit(),
            ActiveIscriptFlingy => self.active_iscript_flingy(),
            ActiveIscriptBullet => self.active_iscript_bullet(),
            UnitShouldRevealArea => self.unit_should_reveal_area(),
            MenuScreenId => self.menu_screen_id(),
            NetPlayerFlags => self.net_player_flags(),
            PlayerTurns => self.player_turns(),
            PlayerTurnsSize => self.player_turns_size(),
            NetworkReady => self.network_ready(),
            NetUserLatency => self.net_user_latency(),
            LastBulletSpawner => self.last_bullet_spawner(),
            CmdIconsDdsGrp => self.cmdicons_ddsgrp(),
            CmdBtnsDdsGrp => self.cmdbtns_ddsgrp(),
            DatRequirementError => self.dat_requirement_error(),
            CursorMarker => self.cursor_marker(),
            MainPalette => self.main_palette(),
            PaletteSet => self.palette_set(),
            TfontGam => self.tfontgam(),
            SyncActive => self.sync_active(),
            SyncData => self.sync_data(),
            IscriptBin => self.iscript_bin(),
            StormCommandUser => self.storm_command_user(),
            FirstFreeOrder => self.first_free_order(),
            LastFreeOrder => self.last_free_order(),
            AllocatedOrderCount => self.allocated_order_count(),
            ReplayBfix => self.replay_bfix(),
            ReplayGcfg => self.replay_gcfg(),
            ContinueGameLoop => self.continue_game_loop(),
            AntiTroll => self.anti_troll(),
            StepGameFrames => self.step_game_frames(),
            NextGameStepTick => self.next_game_step_tick(),
            ReplaySeekFrame => self.replay_seek_frame(),
            BnetController => self.bnet_controller(),
            MouseX => self.mouse_x(),
            MouseY => self.mouse_y(),
            FirstPylon => self.first_pylon(),
            PylonAurasVisible => self.pylon_auras_visible(),
            PylonRefresh => self.pylon_refresh(),
            LocalGameResult => self.local_game_result(),
            IsCustomSinglePlayer => self.is_custom_single_player(),
            CurrentCampaignMission => self.current_campaign_mission(),
            LocalVisions => self.local_visions(),
            FirstFreeSelectionCircle => self.first_free_selection_circle(),
            LastFreeSelectionCircle => self.last_free_selection_circle(),
            UnitSkinMap => self.unit_skin_map(),
            SpriteSkinMap => self.sprite_skin_map(),
            GrpWireGrp => self.grpwire_grp(),
            GrpWireDdsGrp => self.grpwire_ddsgrp(),
            TranWireGrp => self.tranwire_grp(),
            TranWireDdsGrp => self.tranwire_ddsgrp(),
            StatusScreen => self.status_screen(),
            ReplayScenarioChk => self.replay_scenario_chk(),
            ReplayScenarioChkSize => self.replay_scenario_chk_size(),
            MapMpq => self.map_mpq(),
            MapHistory => self.map_history(),
            GameScreenLClickCallback => self.game_screen_lclick_callback(),
            GameScreenRClickCallback => self.game_screen_rclick_callback(),
            TargetedOrderUnit => self.targeted_order_unit(),
            TargetedOrderGround => self.targeted_order_fow(),
            TargetedOrderFow => self.targeted_order_ground(),
            MinimapCursorType => self.minimap_cursor_type(),
        }
    }

    fn analyze_many_addr<F>(
        &mut self,
        addr: AddressAnalysis,
        cache_fn: F,
    ) -> Option<E::VirtualAddress>
    where F: FnOnce(&mut AnalysisCache<'e, E>, &AnalysisCtx<'e, E>)
    {
        if self.cache.address_results[addr as usize] == E::VirtualAddress::from_u64(0) {
            self.enter(cache_fn);
        }
        Some(self.cache.address_results[addr as usize])
            .filter(|&addr| addr != E::VirtualAddress::from_u64(1))
    }

    fn analyze_many_op<F>(&mut self, op: OperandAnalysis, cache_fn: F) -> Option<Operand<'e>>
    where F: FnOnce(&mut AnalysisCache<'e, E>, &AnalysisCtx<'e, E>)
    {
        if self.cache.operand_results[op as usize].is_none() {
            self.enter(cache_fn);
        }
        self.cache.operand_results[op as usize]
            .filter(|&op| op != self.cache.operand_not_found)
    }

    pub fn firegraft_addresses(&mut self) -> Rc<FiregraftAddresses<E::VirtualAddress>> {
        self.enter(|x, s| x.firegraft_addresses(s))
    }

    pub fn dat(&mut self, ty: DatType) -> Option<DatTablePtr<'e>> {
        self.enter(|x, s| x.dat(ty, s))
    }

    pub fn open_file(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.open_file(s))
    }

    pub fn rng_seed(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::RngSeed, AnalysisCache::cache_rng)
    }

    pub fn rng_enable(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::RngEnable, AnalysisCache::cache_rng)
    }

    pub fn step_objects(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.step_objects(s))
    }

    pub fn game(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.game(s))
    }

    pub fn aiscript_hook(&mut self) -> Option<AiScriptHook<'e, E::VirtualAddress>> {
        self.enter(AnalysisCache::aiscript_hook)
    }

    pub fn get_region(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::GetRegion, AnalysisCache::cache_regions)
    }

    pub fn change_ai_region_state(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::ChangeAiRegionState, AnalysisCache::cache_regions)
    }

    pub fn ai_regions(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::AiRegions, AnalysisCache::cache_regions)
    }

    pub fn pathing(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.pathing(s))
    }

    pub fn first_active_unit(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::FirstActiveUnit,
            AnalysisCache::cache_active_hidden_units,
        )
    }

    pub fn first_hidden_unit(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::FirstHiddenUnit,
            AnalysisCache::cache_active_hidden_units,
        )
    }

    pub fn order_init_arbiter(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::OrderInitArbiter,
            AnalysisCache::cache_order_issuing,
        )
    }

    pub fn prepare_issue_order(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::PrepareIssueOrder,
            AnalysisCache::cache_order_issuing,
        )
    }

    pub fn do_next_queued_order(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::DoNextQueuedOrder,
            AnalysisCache::cache_order_issuing,
        )
    }

    pub fn process_commands(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::ProcessCommands,
            AnalysisCache::cache_step_network,
        )
    }

    pub fn command_user(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.command_user(s))
    }

    /// May return an overly long array
    pub fn command_lengths(&mut self) -> Rc<Vec<u32>> {
        self.enter(|x, s| x.command_lengths(s))
    }

    pub fn selections(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::Selections, AnalysisCache::cache_selections)
    }

    pub fn unique_command_user(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::UniqueCommandUser, AnalysisCache::cache_selections)
    }

    pub fn is_replay(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.is_replay(s))
    }

    pub fn process_lobby_commands(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::ProcessLobbyCommands,
            AnalysisCache::cache_step_network,
        )
    }

    pub fn send_command(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.send_command(s))
    }

    pub fn print_text(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::PrintText, AnalysisCache::cache_print_text)
    }

    pub fn add_to_replay_data(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::AddToReplayData, AnalysisCache::cache_print_text)
    }

    pub fn init_map_from_path(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::InitMapFromPath, AnalysisCache::cache_init_map)
    }

    pub fn map_init_chk_callbacks(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::MapInitChkCallbacks,
            AnalysisCache::cache_init_map,
        )
    }

    pub fn choose_snp(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.choose_snp(s))
    }

    pub fn renderer_vtables(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        self.enter(|x, s| x.renderer_vtables(s))
    }

    pub fn vtables(&mut self) -> Vec<E::VirtualAddress> {
        self.enter(|x, s| x.all_vtables(s))
    }

    pub fn vtables_for_class(&mut self, name: &[u8]) -> Vec<E::VirtualAddress> {
        self.enter(|x, s| x.vtables_for_class(name, s))
    }

    pub fn single_player_start(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::SinglePlayerStart,
            AnalysisCache::cache_single_player_start,
        )
    }

    pub fn local_storm_player_id(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::LocalStormPlayerId,
            AnalysisCache::cache_single_player_start,
        )
    }

    pub fn local_unique_player_id(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::LocalUniquePlayerId,
            AnalysisCache::cache_single_player_start,
        )
    }

    pub fn net_player_to_game(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::NetPlayerToGame,
            AnalysisCache::cache_single_player_start,
        )
    }

    pub fn net_player_to_unique(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::NetPlayerToUnique,
            AnalysisCache::cache_single_player_start,
        )
    }

    pub fn game_data(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::GameData,
            AnalysisCache::cache_single_player_start,
        )
    }

    pub fn skins(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::Skins,
            AnalysisCache::cache_single_player_start,
        )
    }

    pub fn player_skins(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::PlayerSkins,
            AnalysisCache::cache_single_player_start,
        )
    }

    pub fn skins_size(&mut self) -> Option<u32> {
        self.player_skins()
            .map(|_| self.cache.skins_size as u32)
    }

    pub fn local_player_id(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.local_player_id(s))
    }

    pub fn game_screen_rclick(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::GameScreenRClick,
            AnalysisCache::cache_game_screen_rclick,
        )
    }

    pub fn client_selection(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::ClientSelection,
            AnalysisCache::cache_game_screen_rclick,
        )
    }

    pub fn select_map_entry(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::SelectMapEntry,
            AnalysisCache::cache_select_map_entry,
        )
    }

    pub fn is_multiplayer(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::IsMultiplayer,
            AnalysisCache::cache_select_map_entry,
        )
    }

    pub fn load_images(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.load_images(s))
    }

    pub fn images_loaded(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::ImagesLoaded, AnalysisCache::cache_images_loaded)
    }

    pub fn init_real_time_lighting(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::InitRealTimeLighting,
            AnalysisCache::cache_images_loaded,
        )
    }

    pub fn local_player_name(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.local_player_name(s))
    }

    pub fn receive_storm_turns(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::ReceiveStormTurns,
            AnalysisCache::cache_step_network,
        )
    }

    pub fn net_player_flags(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::NetPlayerFlags, AnalysisCache::cache_step_network)
    }

    pub fn player_turns(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::PlayerTurns, AnalysisCache::cache_step_network)
    }

    pub fn player_turns_size(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::PlayerTurnsSize, AnalysisCache::cache_step_network)
    }

    pub fn network_ready(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::NetworkReady, AnalysisCache::cache_step_network)
    }

    pub fn net_user_latency(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.net_user_latency(s))
    }

    pub fn net_format_turn_rate(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.net_format_turn_rate(s))
    }

    pub fn storm_command_user(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::StormCommandUser, AnalysisCache::cache_step_network)
    }

    pub fn init_game_network(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.init_game_network(s))
    }

    pub fn snp_definitions(&mut self) -> Option<SnpDefinitions<'e>> {
        self.enter(|x, s| x.snp_definitions(s))
    }

    pub fn lobby_state(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.lobby_state(s))
    }

    pub fn init_storm_networking(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::InitStormNetworking,
            AnalysisCache::cache_init_storm_networking,
        )
    }

    pub fn load_snp_list(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::LoadSnpList,
            AnalysisCache::cache_init_storm_networking,
        )
    }

    pub fn step_order(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.step_order(s))
    }

    pub fn step_order_hidden(&mut self) ->
        Rc<Vec<step_order::StepOrderHiddenHook<'e, E::VirtualAddress>>>
    {
        self.enter(|x, s| x.step_order_hidden(s))
    }

    pub fn step_secondary_order(&mut self) ->
        Rc<Vec<step_order::SecondaryOrderHook<'e, E::VirtualAddress>>>
    {
        self.enter(|x, s| x.step_secondary_order(s))
    }

    pub fn step_iscript(&mut self) -> Option<E::VirtualAddress> {
        self.enter(AnalysisCache::step_iscript)
    }

    pub fn step_iscript_switch(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::StepIscriptSwitch,
            AnalysisCache::cache_step_iscript,
        )
    }

    pub fn step_iscript_hook(&mut self) -> Option<StepIscriptHook<'e, E::VirtualAddress>> {
        self.step_iscript_switch()?;
        self.cache.step_iscript_hook
    }

    pub fn iscript_bin(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::IscriptBin, AnalysisCache::cache_step_iscript)
    }

    pub fn add_overlay_iscript(&mut self) -> Option<E::VirtualAddress> {
        self.enter(AnalysisCache::add_overlay_iscript)
    }

    pub fn draw_cursor_marker(&mut self) -> Option<Operand<'e>> {
        self.enter(AnalysisCache::draw_cursor_marker)
    }

    pub fn play_smk(&mut self) -> Option<E::VirtualAddress> {
        self.enter(AnalysisCache::play_smk)
    }

    pub fn sc_main(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::ScMain, AnalysisCache::cache_game_init)
    }

    pub fn mainmenu_entry_hook(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::MainMenuEntryHook, AnalysisCache::cache_game_init)
    }

    pub fn game_loop(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::GameLoop, AnalysisCache::cache_game_init)
    }

    pub fn run_menus(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::RunMenus, AnalysisCache::cache_game_init)
    }

    pub fn scmain_state(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::ScMainState, AnalysisCache::cache_game_init)
    }

    pub fn is_paused(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::IsPaused, AnalysisCache::cache_misc_clientside)
    }

    pub fn is_placing_building(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::IsPlacingBuilding,
            AnalysisCache::cache_misc_clientside,
        )
    }

    pub fn is_targeting(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::IsTargeting, AnalysisCache::cache_misc_clientside)
    }

    pub fn init_units(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::InitUnits, AnalysisCache::cache_init_units)
    }

    pub fn load_dat(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::LoadDat, AnalysisCache::cache_init_units)
    }

    pub fn units(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.units(s))
    }

    pub fn first_ai_script(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::FirstAiScript, AnalysisCache::cache_ai_step_frame)
    }

    pub fn step_ai_script(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::StepAiScript, AnalysisCache::cache_ai_step_frame)
    }

    pub fn first_guard_ai(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.first_guard_ai(s))
    }

    pub fn player_ai_towns(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.player_ai_towns(s))
    }

    pub fn player_ai(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.player_ai(s))
    }

    pub fn init_game(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::InitGame, AnalysisCache::cache_init_game)
    }

    pub fn loaded_save(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::LoadedSave, AnalysisCache::cache_init_game)
    }

    pub fn create_lone_sprite(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::CreateLoneSprite, AnalysisCache::cache_sprites)
    }

    pub fn sprite_hlines(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::SpriteHlines, AnalysisCache::cache_sprites)
    }

    pub fn sprite_hlines_end(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::SpriteHlinesEnd, AnalysisCache::cache_sprites)
    }

    pub fn first_free_sprite(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::FirstFreeSprite, AnalysisCache::cache_sprites)
    }

    pub fn last_free_sprite(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::LastFreeSprite, AnalysisCache::cache_sprites)
    }

    pub fn first_lone_sprite(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::FirstLoneSprite, AnalysisCache::cache_sprites)
    }

    pub fn last_lone_sprite(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::LastLoneSprite, AnalysisCache::cache_sprites)
    }

    pub fn first_free_lone_sprite(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::FirstFreeLoneSprite, AnalysisCache::cache_sprites)
    }

    pub fn last_free_lone_sprite(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::LastFreeLoneSprite, AnalysisCache::cache_sprites)
    }

    pub fn sprite_x_position(&mut self) -> Option<(Operand<'e>, u32, MemAccessSize)> {
        self.sprite_hlines(); // Ends up caching sprite pos
        self.cache.sprite_x_position
    }

    pub fn sprite_y_position(&mut self) -> Option<(Operand<'e>, u32, MemAccessSize)> {
        self.sprite_hlines(); // Ends up caching sprite pos
        self.cache.sprite_y_position
    }

    pub fn eud_table(&mut self) -> Rc<EudTable<'e>> {
        self.enter(|x, s| x.eud_table(s))
    }

    pub fn map_tile_flags(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::MapTileFlags, AnalysisCache::cache_map_tile_flags)
    }

    pub fn update_visibility_point(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UpdateVisibilityPoint,
            AnalysisCache::cache_map_tile_flags,
        )
    }

    pub fn players(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::Players, AnalysisCache::cache_ai_step_frame)
    }

    pub fn prepare_draw_image(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::PrepareDrawImage,
            AnalysisCache::cache_draw_game_layer,
        )
    }

    pub fn draw_image(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::DrawImage,
            AnalysisCache::cache_draw_game_layer,
        )
    }

    pub fn cursor_marker(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::CursorMarker,
            AnalysisCache::cache_draw_game_layer,
        )
    }

    pub fn first_active_bullet(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::FirstActiveBullet,
            AnalysisCache::cache_bullet_creation,
        )
    }

    pub fn last_active_bullet(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::LastActiveBullet,
            AnalysisCache::cache_bullet_creation,
        )
    }

    pub fn first_free_bullet(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::FirstFreeBullet,
            AnalysisCache::cache_bullet_creation,
        )
    }

    pub fn last_free_bullet(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::LastFreeBullet,
            AnalysisCache::cache_bullet_creation,
        )
    }

    pub fn active_iscript_unit(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::ActiveIscriptUnit,
            AnalysisCache::cache_bullet_creation,
        )
    }

    pub fn create_bullet(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::CreateBullet,
            AnalysisCache::cache_bullet_creation,
        )
    }

    pub fn net_players(&mut self) -> Option<(Operand<'e>, u32)> {
        self.analyze_many_op(
            OperandAnalysis::NetPlayers,
            AnalysisCache::cache_net_players,
        ).map(|x| (x, self.cache.net_player_size.into()))
    }

    pub fn init_net_player(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::InitNetPlayer,
            AnalysisCache::cache_net_players,
        )
    }

    pub fn campaigns(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.campaigns(s))
    }

    pub fn run_dialog(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::RunDialog, AnalysisCache::cache_run_dialog)
    }

    pub fn glucmpgn_event_handler(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::GluCmpgnEventHandler,
            AnalysisCache::cache_run_dialog,
        )
    }

    pub fn ai_update_attack_target(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.ai_update_attack_target(s))
    }

    pub fn is_outside_game_screen(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.is_outside_game_screen(s))
    }

    pub fn screen_x(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::ScreenX, AnalysisCache::cache_coord_conversion)
    }

    pub fn screen_y(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::ScreenY, AnalysisCache::cache_coord_conversion)
    }

    pub fn zoom(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::Zoom, AnalysisCache::cache_coord_conversion)
    }

    pub fn first_fow_sprite(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::FirstFowSprite, AnalysisCache::cache_fow_sprites)
    }

    pub fn last_fow_sprite(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::LastFowSprite, AnalysisCache::cache_fow_sprites)
    }

    pub fn first_free_fow_sprite(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::FirstFreeFowSprite,
            AnalysisCache::cache_fow_sprites,
        )
    }

    pub fn last_free_fow_sprite(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::LastFreeFowSprite, AnalysisCache::cache_fow_sprites)
    }

    pub fn spawn_dialog(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.spawn_dialog(s))
    }

    pub fn create_unit(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::CreateUnit, AnalysisCache::cache_unit_creation)
    }

    pub fn finish_unit_pre(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::FinishUnitPre, AnalysisCache::cache_unit_creation)
    }

    pub fn finish_unit_post(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::FinishUnitPost,
            AnalysisCache::cache_unit_creation,
        )
    }

    pub fn fonts(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.fonts(s))
    }

    pub fn init_sprites(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::InitSprites, AnalysisCache::cache_init_sprites)
    }

    pub fn sprite_array(&mut self) -> Option<(Operand<'e>, u32)> {
        self.analyze_many_op(OperandAnalysis::Sprites, AnalysisCache::cache_init_sprites)
            .map(|x| (x, self.cache.sprite_struct_size.into()))
    }

    pub fn serialize_sprites(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::SerializeSprites,
            AnalysisCache::cache_sprite_serialization,
        )
    }

    pub fn deserialize_sprites(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::DeserializeSprites,
            AnalysisCache::cache_sprite_serialization,
        )
    }

    pub fn limits(&mut self) -> Rc<Limits<'e, E::VirtualAddress>> {
        self.enter(|x, s| x.limits(s))
    }

    pub fn font_cache_render_ascii(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::FontCacheRenderAscii,
            AnalysisCache::cache_font_render,
        )
    }

    pub fn ttf_cache_character(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::TtfCacheCharacter,
            AnalysisCache::cache_font_render,
        )
    }

    pub fn ttf_render_sdf(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::TtfRenderSdf,
            AnalysisCache::cache_font_render,
        )
    }

    /// Memory allocation function that at least TTF code uses.
    ///
    /// (Should be Win32 HeapAlloc with a specific heap)
    pub fn ttf_malloc(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.ttf_malloc(s))
    }

    /// Offset to CreateGameScreen.OnMultiplayerGameCreate in the dialog's vtable
    pub fn create_game_dialog_vtbl_on_multiplayer_create(&mut self) -> Option<usize> {
        self.create_game_multiplayer();
        Some(self.cache.create_game_dialog_vtbl_on_multiplayer_create as usize)
            .filter(|&x| x != 0)
    }

    pub fn tooltip_draw_func(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::TooltipDrawFunc,
            AnalysisCache::cache_tooltip_related,
        )
    }

    pub fn current_tooltip_ctrl(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::CurrentTooltipCtrl,
            AnalysisCache::cache_tooltip_related,
        )
    }

    pub fn layout_draw_text(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::LayoutDrawText,
            AnalysisCache::cache_tooltip_related,
        )
    }

    pub fn graphic_layers(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::GraphicLayers,
            AnalysisCache::cache_tooltip_related,
        )
    }

    pub fn draw_f10_menu_tooltip(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::DrawF10MenuTooltip,
            AnalysisCache::cache_tooltip_related,
        )
    }

    pub fn draw_tooltip_layer(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::DrawTooltipLayer,
            AnalysisCache::cache_tooltip_related,
        )
    }

    pub fn draw_graphic_layers(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.draw_graphic_layers(s))
    }

    pub fn prism_vertex_shaders(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        self.enter(|x, s| x.prism_vertex_shaders(s))
    }

    pub fn prism_pixel_shaders(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        self.enter(|x, s| x.prism_pixel_shaders(s))
    }

    pub fn ai_attack_prepare(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.ai_attack_prepare(s))
    }

    pub fn ai_step_region(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::AiStepRegion, AnalysisCache::cache_ai_step_frame)
    }

    pub fn ai_spend_money(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::AiSpendMoney, AnalysisCache::cache_ai_step_frame)
    }

    pub fn join_game(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.join_game(s))
    }

    pub fn snet_initialize_provider(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.snet_initialize_provider(s))
    }

    pub fn set_status_screen_tooltip(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.set_status_screen_tooltip(s))
    }

    pub fn dat_patches(&mut self) -> Option<Rc<DatPatches<'e, E::VirtualAddress>>> {
        self.enter(|x, s| x.dat_patches(s))
    }

    pub fn do_attack(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::DoAttack, AnalysisCache::cache_do_attack)
    }

    pub fn do_attack_main(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::DoAttackMain, AnalysisCache::cache_do_attack)
    }

    pub fn last_bullet_spawner(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::LastBulletSpawner, AnalysisCache::cache_do_attack)
    }

    pub fn smem_alloc(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.smem_alloc(s))
    }

    pub fn smem_free(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.smem_free(s))
    }

    pub fn allocator(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.allocator(s))
    }

    pub fn cmdicons_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::CmdIconsDdsGrp, AnalysisCache::cache_cmdicons)
    }

    pub fn cmdbtns_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::CmdBtnsDdsGrp, AnalysisCache::cache_cmdicons)
    }

    pub fn status_screen_mode(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.status_screen_mode(s))
    }

    pub fn check_unit_requirements(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::CheckUnitRequirements,
            AnalysisCache::cache_unit_requirements,
        )
    }

    pub fn check_dat_requirements(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.check_dat_requirements(s))
    }

    pub fn dat_requirement_error(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::DatRequirementError,
            AnalysisCache::cache_unit_requirements,
        )
    }

    pub fn cheat_flags(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.cheat_flags(s))
    }

    pub fn unit_strength(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::UnitStrength,
            AnalysisCache::cache_unit_strength_etc,
        )
    }

    pub fn sprite_include_in_vision_sync(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::SpriteIncludeInVisionSync,
            AnalysisCache::cache_unit_strength_etc,
        )
    }

    pub fn grpwire_grp(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::GrpWireGrp,
            AnalysisCache::cache_multi_wireframes,
        )
    }

    pub fn grpwire_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::GrpWireDdsGrp,
            AnalysisCache::cache_multi_wireframes,
        )
    }

    pub fn tranwire_grp(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::TranWireGrp,
            AnalysisCache::cache_multi_wireframes,
        )
    }

    pub fn tranwire_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::TranWireDdsGrp,
            AnalysisCache::cache_multi_wireframes,
        )
    }

    pub fn status_screen(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::StatusScreen, AnalysisCache::cache_multi_wireframes)
    }

    pub fn status_screen_event_handler(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::StatusScreenEventHandler,
            AnalysisCache::cache_multi_wireframes,
        )
    }

    /// Note: Struct that contains { grp, sd_ddsgrp, hd_ddsgrp }
    pub fn wirefram_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.wirefram_ddsgrp(s))
    }

    pub fn init_status_screen(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.init_status_screen(s))
    }

    pub fn trigger_conditions(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.trigger_conditions(s))
    }

    pub fn trigger_actions(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.trigger_actions(s))
    }

    pub fn trigger_completed_units_cache(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.trigger_completed_units_cache(s))
    }

    pub fn trigger_all_units_cache(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.trigger_all_units_cache(s))
    }

    pub fn snet_send_packets(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::SnetSendPackets,
            AnalysisCache::cache_snet_handle_packets,
        )
    }

    pub fn snet_recv_packets(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::SnetRecvPackets,
            AnalysisCache::cache_snet_handle_packets,
        )
    }

    pub fn chk_init_players(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.chk_init_players(s))
    }

    pub fn original_chk_player_types(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.original_chk_player_types(s))
    }

    pub fn give_ai(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.give_ai(s))
    }

    pub fn play_sound(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.play_sound(s))
    }

    pub fn ai_prepare_moving_to(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.ai_prepare_moving_to(s))
    }

    pub fn ai_transport_reachability_cached_region(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.ai_transport_reachability_cached_region(s))
    }

    pub fn player_unit_skins(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.player_unit_skins(s))
    }

    /// A patch to show resource fog sprites on minimap in replays even if they're
    /// in unexplored fog.
    pub fn replay_minimap_unexplored_fog_patch(
        &mut self,
    ) -> Option<Rc<Patch<E::VirtualAddress>>> {
        self.enter(|x, s| x.replay_minimap_unexplored_fog_patch(s))
    }

    pub fn draw_minimap_units(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.draw_minimap_units(s))
    }

    pub fn step_replay_commands(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.step_replay_commands(s))
    }

    pub fn replay_data(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.replay_data(s))
    }

    pub fn ai_train_military(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.ai_train_military(s))
    }

    pub fn ai_add_military_to_region(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.ai_add_military_to_region(s))
    }

    /// Renderer's vertex (and index) buffer
    pub fn vertex_buffer(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.vertex_buffer(s))
    }

    pub fn crt_fastfail(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        self.enter(|x, s| x.crt_fastfail(s))
    }

    pub fn reset_ui_event_handlers(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::ResetUiEventHandlers,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn ui_default_scroll_handler(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UiDefaultScrollHandler,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn global_event_handlers(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::GlobalEventHandlers,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn replay_visions(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::ReplayVisions,
            AnalysisCache::cache_replay_visions,
        )
    }

    pub fn replay_show_entire_map(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::ReplayShowEntireMap,
            AnalysisCache::cache_replay_visions,
        )
    }

    pub fn first_player_unit(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::FirstPlayerUnit,
            AnalysisCache::cache_replay_visions,
        )
    }

    pub fn clamp_zoom(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.clamp_zoom(s))
    }

    pub fn set_briefing_music(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::SetBriefingMusic,
            AnalysisCache::cache_menu_screens,
        )
    }

    pub fn pre_mission_glue(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::PreMissionGlue,
            AnalysisCache::cache_menu_screens,
        )
    }

    pub fn show_mission_glue(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::ShowMissionGlue,
            AnalysisCache::cache_menu_screens,
        )
    }

    pub fn menu_swish_in(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::MenuSwishIn,
            AnalysisCache::cache_glucmpgn_events,
        )
    }

    pub fn menu_swish_out(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::MenuSwishOut,
            AnalysisCache::cache_glucmpgn_events,
        )
    }

    pub fn dialog_return_code(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::DialogReturnCode,
            AnalysisCache::cache_glucmpgn_events,
        )
    }

    pub fn ai_spell_cast(&mut self) -> Option<E::VirtualAddress> {
        self.enter(AnalysisCache::ai_spell_cast)
    }

    pub fn give_unit(&mut self) -> Option<E::VirtualAddress> {
        self.enter(AnalysisCache::give_unit)
    }

    pub fn set_unit_player(&mut self) -> Option<E::VirtualAddress> {
        self.enter(AnalysisCache::set_unit_player)
    }

    pub fn remove_from_selections(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::RemoveFromSelections,
            AnalysisCache::cache_set_unit_player_fns,
        )
    }

    pub fn remove_from_client_selection(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::RemoveFromClientSelection,
            AnalysisCache::cache_set_unit_player_fns,
        )
    }

    pub fn clear_build_queue(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::ClearBuildQueue,
            AnalysisCache::cache_set_unit_player_fns,
        )
    }

    pub fn unit_changing_player(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UnitChangingPlayer,
            AnalysisCache::cache_set_unit_player_fns,
        )
    }

    pub fn player_gained_upgrade(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::PlayerGainedUpgrade,
            AnalysisCache::cache_set_unit_player_fns,
        )
    }

    pub fn unit_apply_speed_upgrades(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UnitApplySpeedUpgrades,
            AnalysisCache::cache_unit_speed,
        )
    }

    pub fn unit_update_speed(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UnitUpdateSpeed,
            AnalysisCache::cache_unit_speed,
        )
    }

    pub fn unit_update_speed_iscript(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UnitUpdateSpeedIscript,
            AnalysisCache::cache_unit_speed,
        )
    }

    pub fn unit_buffed_flingy_speed(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UnitBuffedFlingySpeed,
            AnalysisCache::cache_unit_speed,
        )
    }

    pub fn unit_buffed_acceleration(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UnitBuffedAcceleration,
            AnalysisCache::cache_unit_speed,
        )
    }

    pub fn unit_buffed_turn_speed(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UnitBuffedTurnSpeed,
            AnalysisCache::cache_unit_speed,
        )
    }

    pub fn start_udp_server(&mut self) -> Option<E::VirtualAddress> {
        self.enter(AnalysisCache::start_udp_server)
    }

    pub fn open_anim_single_file(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::OpenAnimSingleFile,
            AnalysisCache::cache_image_loading,
        )
    }

    pub fn open_anim_multi_file(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::OpenAnimMultiFile,
            AnalysisCache::cache_image_loading,
        )
    }

    pub fn init_skins(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::InitSkins,
            AnalysisCache::cache_image_loading,
        )
    }

    pub fn add_asset_change_callback(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::AddAssetChangeCallback,
            AnalysisCache::cache_image_loading,
        )
    }

    pub fn anim_asset_change_cb(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::AnimAssetChangeCb,
            AnalysisCache::cache_image_loading,
        )
    }

    pub fn asset_scale(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::AssetScale, AnalysisCache::cache_images_loaded)
    }

    pub fn base_anim_set(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::BaseAnimSet, AnalysisCache::cache_image_loading)
    }

    pub fn image_grps(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::ImageGrps, AnalysisCache::cache_image_loading)
    }

    pub fn image_overlays(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::ImageOverlays, AnalysisCache::cache_image_loading)
    }

    pub fn fire_overlay_max(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::FireOverlayMax, AnalysisCache::cache_image_loading)
    }

    pub fn anim_struct_size(&mut self) -> Option<u16> {
        self.base_anim_set().map(|_| self.cache.anim_struct_size)
    }

    pub fn step_active_unit_frame(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::StepActiveUnitFrame,
            AnalysisCache::cache_step_objects,
        )
    }

    pub fn step_hidden_unit_frame(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::StepHiddenUnitFrame,
            AnalysisCache::cache_step_objects,
        )
    }

    pub fn step_bullet_frame(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::StepBulletFrame,
            AnalysisCache::cache_step_objects,
        )
    }

    pub fn reveal_unit_area(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::RevealUnitArea, AnalysisCache::cache_step_objects)
    }

    pub fn vision_update_counter(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::VisionUpdateCounter,
            AnalysisCache::cache_step_objects,
        )
    }

    pub fn vision_updated(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::VisionUpdated, AnalysisCache::cache_step_objects)
    }

    pub fn first_dying_unit(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::FirstDyingUnit, AnalysisCache::cache_step_objects)
    }

    pub fn first_revealer(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::FirstRevealer, AnalysisCache::cache_step_objects)
    }

    pub fn first_invisible_unit(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::FirstInvisibleUnit,
            AnalysisCache::cache_step_objects,
        )
    }

    pub fn active_iscript_flingy(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::ActiveIscriptFlingy,
            AnalysisCache::cache_step_objects,
        )
    }

    pub fn active_iscript_bullet(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::ActiveIscriptBullet,
            AnalysisCache::cache_step_objects,
        )
    }

    pub fn update_unit_visibility(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UpdateUnitVisibility,
            AnalysisCache::cache_step_objects,
        )
    }

    pub fn update_cloak_state(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UpdateCloakState,
            AnalysisCache::cache_step_objects,
        )
    }

    pub fn step_unit_movement(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::StepUnitMovement,
            AnalysisCache::cache_step_active_unit,
        )
    }

    pub fn unit_should_reveal_area(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::UnitShouldRevealArea,
            AnalysisCache::cache_step_active_unit,
        )
    }

    pub fn draw_game_layer(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.draw_game_layer(s))
    }

    pub fn menu_screen_id(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::MenuScreenId, AnalysisCache::cache_game_loop)
    }

    pub fn step_network(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::StepNetwork, AnalysisCache::cache_game_loop)
    }

    pub fn render_screen(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::RenderScreen, AnalysisCache::cache_game_loop)
    }

    pub fn step_game_loop(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::StepGameLoop, AnalysisCache::cache_game_loop)
    }

    pub fn process_events(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::ProcessEvents, AnalysisCache::cache_game_loop)
    }

    pub fn step_game_logic(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::StepGameLogic, AnalysisCache::cache_game_loop)
    }

    pub fn load_pcx(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::LoadPcx, AnalysisCache::cache_game_loop)
    }

    pub fn set_music(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::SetMusic, AnalysisCache::cache_game_loop)
    }

    pub fn main_palette(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::MainPalette, AnalysisCache::cache_game_loop)
    }

    pub fn palette_set(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::PaletteSet, AnalysisCache::cache_game_loop)
    }

    pub fn tfontgam(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::TfontGam, AnalysisCache::cache_game_loop)
    }

    pub fn sync_active(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::SyncActive, AnalysisCache::cache_game_loop)
    }

    pub fn sync_data(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::SyncData, AnalysisCache::cache_game_loop)
    }

    pub fn continue_game_loop(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::ContinueGameLoop, AnalysisCache::cache_game_loop)
    }

    pub fn anti_troll(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::AntiTroll, AnalysisCache::cache_game_loop)
    }

    pub fn step_game_frames(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::StepGameFrames, AnalysisCache::cache_game_loop)
    }

    pub fn next_game_step_tick(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::NextGameStepTick, AnalysisCache::cache_game_loop)
    }

    pub fn replay_seek_frame(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::ReplaySeekFrame, AnalysisCache::cache_game_loop)
    }

    pub fn first_free_order(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::FirstFreeOrder,
            AnalysisCache::cache_prepare_issue_order,
        )
    }

    pub fn last_free_order(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::LastFreeOrder,
            AnalysisCache::cache_prepare_issue_order,
        )
    }

    pub fn allocated_order_count(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::AllocatedOrderCount,
            AnalysisCache::cache_prepare_issue_order,
        )
    }

    pub fn replay_bfix(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::ReplayBfix,
            AnalysisCache::cache_prepare_issue_order,
        )
    }

    pub fn replay_gcfg(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::ReplayGcfg,
            AnalysisCache::cache_prepare_issue_order,
        )
    }

    pub fn step_bnet_controller(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::StepBnetController,
            AnalysisCache::cache_process_events,
        )
    }

    pub fn bnet_controller(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::BnetController, AnalysisCache::cache_process_events)
    }

    pub fn bnet_message_vtable_type(&mut self) -> Option<u16> {
        self.bnet_controller()?;
        self.cache.bnet_message_switch?;
        Some(self.cache.bnet_message_vtable_type)
    }

    pub fn bnet_message_switch_op(&mut self) -> Option<Operand<'e>> {
        Some(self.cache.bnet_message_switch?.as_operand(self.shareable.ctx))
    }

    pub fn create_game_multiplayer(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::CreateGameMultiplayer,
            AnalysisCache::cache_select_map_entry_children,
        )
    }

    pub fn map_entry_load_map(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::MapEntryLoadMap,
            AnalysisCache::cache_select_map_entry_children,
        )
    }

    pub fn map_entry_load_save(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::MapEntryLoadSave,
            AnalysisCache::cache_select_map_entry_children,
        )
    }

    pub fn map_entry_load_replay(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::MapEntryLoadReplay,
            AnalysisCache::cache_select_map_entry_children,
        )
    }

    pub fn join_param_variant_type_offset(&mut self) -> Option<usize> {
        self.enter(AnalysisCache::join_param_variant_type_offset)
    }

    pub fn get_mouse_x(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::GetMouseX, AnalysisCache::cache_mouse_xy)
    }

    pub fn get_mouse_y(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::GetMouseY, AnalysisCache::cache_mouse_xy)
    }

    pub fn mouse_x(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::MouseX, AnalysisCache::cache_mouse_xy)
    }

    pub fn mouse_y(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::MouseY, AnalysisCache::cache_mouse_xy)
    }

    pub fn pylon_auras_visible(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::PylonAurasVisible, AnalysisCache::cache_pylon_aura)
    }

    pub fn first_pylon(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::FirstPylon, AnalysisCache::cache_pylon_aura)
    }

    pub fn pylon_refresh(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::PylonRefresh, AnalysisCache::cache_pylon_aura)
    }

    pub fn add_pylon_aura(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(AddressAnalysis::AddPylonAura, AnalysisCache::cache_pylon_aura)
    }

    pub fn single_player_map_end(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::SinglePlayerMapEnd,
            AnalysisCache::cache_sp_map_end,
        )
    }

    pub fn local_game_result(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::LocalGameResult, AnalysisCache::cache_sp_map_end)
    }

    pub fn set_scmain_state(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::SetScmainState,
            AnalysisCache::cache_sp_map_end_analysis,
        )
    }

    pub fn unlock_mission(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UnlockMission,
            AnalysisCache::cache_sp_map_end_analysis,
        )
    }

    pub fn is_custom_single_player(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::IsCustomSinglePlayer,
            AnalysisCache::cache_sp_map_end_analysis,
        )
    }

    pub fn current_campaign_mission(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::CurrentCampaignMission,
            AnalysisCache::cache_sp_map_end_analysis,
        )
    }

    pub fn local_visions(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::LocalVisions,
            AnalysisCache::cache_update_unit_visibility,
        )
    }

    pub fn first_free_selection_circle(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::FirstFreeSelectionCircle,
            AnalysisCache::cache_update_unit_visibility,
        )
    }

    pub fn last_free_selection_circle(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::LastFreeSelectionCircle,
            AnalysisCache::cache_update_unit_visibility,
        )
    }

    pub fn unit_skin_map(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::UnitSkinMap,
            AnalysisCache::cache_update_unit_visibility,
        )
    }

    pub fn sprite_skin_map(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::SpriteSkinMap,
            AnalysisCache::cache_update_unit_visibility,
        )
    }

    pub fn create_fow_sprite(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::CreateFowSprite,
            AnalysisCache::cache_update_unit_visibility,
        )
    }

    pub fn duplicate_sprite(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::DuplicateSprite,
            AnalysisCache::cache_update_unit_visibility,
        )
    }

    pub fn load_replay_scenario_chk(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::LoadReplayScenarioChk,
            AnalysisCache::cache_init_map_from_path,
        )
    }

    pub fn sfile_close_archive(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::SfileCloseArchive,
            AnalysisCache::cache_init_map_from_path,
        )
    }

    pub fn open_map_mpq(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::OpenMapMpq,
            AnalysisCache::cache_init_map_from_path,
        )
    }

    pub fn read_whole_mpq_file(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::ReadWholeMpqFile,
            AnalysisCache::cache_init_map_from_path,
        )
    }

    pub fn read_whole_mpq_file2(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::ReadWholeMpqFile2,
            AnalysisCache::cache_init_map_from_path,
        )
    }

    pub fn replay_scenario_chk(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::ReplayScenarioChk,
            AnalysisCache::cache_init_map_from_path,
        )
    }

    pub fn replay_scenario_chk_size(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::ReplayScenarioChkSize,
            AnalysisCache::cache_init_map_from_path,
        )
    }

    pub fn map_mpq(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::MapMpq, AnalysisCache::cache_init_map_from_path)
    }

    pub fn map_history(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(OperandAnalysis::MapHistory, AnalysisCache::cache_init_map_from_path)
    }

    pub fn game_screen_lclick_callback(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::GameScreenLClickCallback,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn game_screen_rclick_callback(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::GameScreenRClickCallback,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn targeting_lclick(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::TargetingLClick,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn targeting_rclick(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::TargetingRClick,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn building_placement_lclick(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::BuildingPlacementLClick,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn building_placement_rclick(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::BuildingPlacementRClick,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn game_screen_l_click(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::GameScreenLClick,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn ui_default_key_down_handler(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UiDefaultKeyDownHandler,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn ui_default_key_up_handler(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UiDefaultKeyUpHandler,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn ui_default_left_down_handler(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UiDefaultLeftDownHandler,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn ui_default_left_double_handler(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UiDefaultLeftDoubleHandler,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn ui_default_right_down_handler(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UiDefaultRightDownHandler,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn ui_default_middle_down_handler(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UiDefaultMiddleDownHandler,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn ui_default_middle_up_handler(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UiDefaultMiddleUpHandler,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn ui_default_periodic_handler(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UiDefaultPeriodicHandler,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn ui_default_char_handler(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::UiDefaultCharHandler,
            AnalysisCache::cache_ui_event_handlers,
        )
    }

    pub fn start_targeting(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::StartTargeting,
            AnalysisCache::cache_start_targeting,
        )
    }

    pub fn targeted_order_unit(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::TargetedOrderUnit,
            AnalysisCache::cache_start_targeting,
        )
    }

    pub fn targeted_order_ground(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::TargetedOrderGround,
            AnalysisCache::cache_start_targeting,
        )
    }

    pub fn targeted_order_fow(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::TargetedOrderFow,
            AnalysisCache::cache_start_targeting,
        )
    }

    pub fn minimap_cursor_type(&mut self) -> Option<Operand<'e>> {
        self.analyze_many_op(
            OperandAnalysis::MinimapCursorType,
            AnalysisCache::cache_start_targeting,
        )
    }

    pub fn find_unit_for_click(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::FindUnitForClick,
            AnalysisCache::cache_targeting_lclick,
        )
    }

    pub fn find_fow_sprite_for_click(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::FindFowSpriteForClick,
            AnalysisCache::cache_targeting_lclick,
        )
    }

    pub fn handle_targeted_click(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::HandleTargetedClick,
            AnalysisCache::cache_targeting_lclick,
        )
    }

    pub fn check_weapon_targeting_flags(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::CheckWeaponTargetingFlags,
            AnalysisCache::cache_handle_targeted_click,
        )
    }

    pub fn check_tech_targeting(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::CheckTechTargeting,
            AnalysisCache::cache_handle_targeted_click,
        )
    }

    pub fn check_order_targeting(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::CheckOrderTargeting,
            AnalysisCache::cache_handle_targeted_click,
        )
    }

    pub fn check_fow_order_targeting(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::CheckFowOrderTargeting,
            AnalysisCache::cache_handle_targeted_click,
        )
    }

    pub fn ai_focus_disabled(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::AiFocusDisabled,
            AnalysisCache::cache_step_order,
        )
    }

    pub fn ai_focus_air(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::AiFocusAir,
            AnalysisCache::cache_step_order,
        )
    }

    pub fn file_exists(&mut self) -> Option<E::VirtualAddress> {
        self.analyze_many_addr(
            AddressAnalysis::FileExists,
            AnalysisCache::cache_open_file,
        )
    }

    /// Mainly for tests/dump
    pub fn dat_patches_debug_data(
        &mut self,
    ) -> Option<DatPatchesDebug<'e, E::VirtualAddress>> {
        let patches = self.dat_patches()?;
        let warnings = patches.warnings.get_all().into();
        let mut map = fxhash::FxHashMap::default();
        let mut replaces = Vec::new();
        let mut func_replaces = Vec::new();
        let mut hooks = Vec::new();
        let mut two_step_hooks = Vec::new();
        let mut ext_array_patches = Vec::new();
        let mut ext_array_args = Vec::new();
        let mut grp_index_hooks = Vec::new();
        let mut grp_texture_hooks = Vec::new();
        for patch in &patches.patches {
            match *patch {
                DatPatch::Array(ref a) => {
                    let vec = &mut map.entry(a.dat)
                        .or_insert_with(DatTablePatchesDebug::default)
                        .array_patches;
                    while vec.len() <= a.field_id as usize {
                        vec.push(Vec::new());
                    }
                    vec[a.field_id as usize].push((a.address, a.entry, a.byte_offset));
                    vec[a.field_id as usize].sort_unstable();
                }
                DatPatch::EntryCount(ref a) => {
                    let entry_counts = &mut map.entry(a.dat)
                        .or_insert_with(DatTablePatchesDebug::default)
                        .entry_counts;
                    entry_counts.push(a.address);
                    entry_counts.sort_unstable();
                }
                DatPatch::Replace(addr, offset, len) => {
                    let data = &patches.code_bytes[offset as usize..][..len as usize];
                    replaces.push((addr, data.into()));
                }
                DatPatch::Hook(addr, offset, len, skip) => {
                    let data = &patches.code_bytes[offset as usize..][..len as usize];
                    hooks.push((addr, skip, data.into()));
                }
                DatPatch::TwoStepHook(addr, free_space, offset, len, skip) => {
                    let data = &patches.code_bytes[offset as usize..][..len as usize];
                    two_step_hooks.push((addr, free_space, skip, data.into()));
                }
                DatPatch::ReplaceFunc(addr, ty) => {
                    func_replaces.push((addr, ty));
                }
                DatPatch::ExtendedArray(ref a) => {
                    ext_array_patches.push(
                        (a.address, a.two_step, a.instruction_len, a.ext_array_id, a.index)
                    );
                }
                DatPatch::ExtendedArrayArg(addr, args) => {
                    let args = args.iter().enumerate()
                        .filter_map(|x| Some((x.0, x.1.checked_sub(1)?)))
                        .collect();
                    ext_array_args.push((addr, args));
                }
                DatPatch::GrpIndexHook(addr) => {
                    grp_index_hooks.push(addr);
                }
                DatPatch::GrpTextureHook(ref a) => {
                    grp_texture_hooks.push(
                        (a.address, a.instruction_len, a.dest, a.base, a.index_bytes)
                    );
                }
            }
        }
        replaces.sort_unstable_by_key(|x| x.0);
        func_replaces.sort_unstable_by_key(|x| x.0);
        hooks.sort_unstable_by_key(|x| x.0);
        two_step_hooks.sort_unstable_by_key(|x| x.0);
        ext_array_patches.sort_unstable_by_key(|x| (x.3, x.0));
        ext_array_args.sort_unstable_by_key(|x| x.0);
        grp_index_hooks.sort_unstable_by_key(|x| *x);
        grp_texture_hooks.sort_unstable_by_key(|x| x.0);
        Some(DatPatchesDebug {
            warnings,
            tables: map,
            replaces,
            func_replaces,
            hooks,
            two_step_hooks,
            ext_array_patches,
            ext_array_args,
            grp_index_hooks,
            grp_texture_hooks,
        })
    }
}

impl<'e, E: ExecutionState<'e>> AnalysisCache<'e, E> {
    pub fn functions(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        let binary = self.binary;
        let text = self.text;
        let relocs = self.relocs();
        self.functions.get_or_insert_with(|| {
            let mut functions = scarf::analysis::find_functions::<E>(binary, &relocs);
            functions.retain(|&fun| Analysis::<E>::is_valid_function(fun));

            // Add functions which immediately jump to another
            let text_end = text.virtual_address + text.virtual_size;
            let mut extra_funcs = Vec::with_capacity(64);
            for &func in &functions {
                let relative = func.as_u64().wrapping_sub(text.virtual_address.as_u64()) as usize;
                if let Some(bytes) = text.data.get(relative..).and_then(|x| x.get(..5)) {
                    if bytes[0] == 0xe9 {
                        let offset = LittleEndian::read_u32(&bytes[1..]);
                        let dest = func.as_u64()
                            .wrapping_add(5)
                            .wrapping_add(offset as i32 as i64 as u64);
                        let dest = E::VirtualAddress::from_u64(dest);
                        if dest >= text.virtual_address && dest <= text_end {
                            if let Err(index) = functions.binary_search(&dest) {
                                extra_funcs.push((dest, index));
                            }
                        }
                    }
                }
            }
            // Insert functions without having to memmove every entry more than once
            extra_funcs.sort_unstable_by_key(|x| x.0);
            extra_funcs.dedup_by_key(|x| x.0);
            let mut end_pos = functions.len();
            functions.resize_with(
                functions.len() + extra_funcs.len(),
                || E::VirtualAddress::from_u64(0),
            );
            for (i, &(val, index)) in extra_funcs.iter().enumerate().rev() {
                functions.copy_within(index..end_pos, index + i + 1);
                functions[index + i] = val;
                end_pos = index;
            }
            Rc::new(functions)
        }).clone()
    }

    pub fn globals_with_values(&mut self) -> Rc<Vec<RelocValues<E::VirtualAddress>>> {
        let result = match self.globals_with_values.is_none() {
            true => {
                let relocs = self.relocs();
                let mut result = match scarf::analysis::relocs_with_values(self.binary, &relocs) {
                    Ok(o) => o,
                    Err(e) => {
                        debug!("Error getting relocs with values: {}", e);
                        Vec::new()
                    }
                };
                if E::VirtualAddress::SIZE == 8 {
                    let mut text_globals = x86_64_globals::x86_64_globals(self.binary);
                    if result.len() < text_globals.len() {
                        std::mem::swap(&mut result, &mut text_globals);
                    }
                    result.extend_from_slice(&text_globals);
                    result.sort_unstable_by_key(|x| x.value);
                }
                result
            }
            false => Vec::new(),
        };
        self.globals_with_values.get_or_insert_with(|| {
            Rc::new(result)
        }).clone()
    }

    /// Sorted by address
    pub fn relocs(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        let relocs = match self.relocs.is_none() {
            true => match scarf::analysis::find_relocs::<E>(self.binary) {
                Ok(s) => s,
                Err(e) => {
                    debug!("Error getting relocs: {}", e);
                    Vec::new()
                }
            },
            false => Vec::new(),
        };
        self.relocs.get_or_insert_with(|| {
            Rc::new(relocs)
        }).clone()
    }

    // TODO Should share search w/ self.functions
    fn functions_with_callers(&mut self) -> Rc<Vec<FuncCallPair<E::VirtualAddress>>> {
        let binary = self.binary;
        self.functions_with_callers.get_or_insert_with(|| {
            let mut functions = scarf::analysis::find_functions_with_callers::<E>(binary);
            functions.retain(|fun| Analysis::<E>::is_valid_function(fun.callee));
            Rc::new(functions)
        }).clone()
    }

    pub fn function_finder<'s>(&'s mut self) -> FunctionFinder<'s, 'e, E> {
        if self.functions.is_none() {
            self.functions();
        }
        if self.globals_with_values.is_none() {
            self.globals_with_values();
        }
        if self.functions_with_callers.is_none() {
            self.functions_with_callers();
        }
        let functions = self.functions.0.as_deref().unwrap();
        let globals_with_values = self.globals_with_values.0.as_deref().unwrap();
        let functions_with_callers = self.functions_with_callers.0.as_deref().unwrap();
        FunctionFinder::new(functions, globals_with_values, functions_with_callers)
    }

    fn cache_single_address<F>(
        &mut self,
        addr: AddressAnalysis,
        cb: F,
    ) -> Option<E::VirtualAddress>
    where F: FnOnce(&mut Self) -> Option<E::VirtualAddress>
    {
        let result = self.address_results[addr as usize];
        if result != E::VirtualAddress::from_u64(0) {
            if result == E::VirtualAddress::from_u64(1) {
                return None;
            } else {
                return Some(result);
            }
        }
        self.address_results[addr as usize] = E::VirtualAddress::from_u64(1);
        let result = cb(self);
        if let Some(result) = result {
            self.address_results[addr as usize] = result;
        }
        result
    }

    fn cache_single_operand<F>(&mut self, op: OperandAnalysis, cb: F) -> Option<Operand<'e>>
    where F: FnOnce(&mut Self) -> Option<Operand<'e>>
    {
        if let Some(result) = self.operand_results[op as usize] {
            if result == self.operand_not_found {
                return None;
            } else {
                return Some(result);
            }
        }
        self.operand_results[op as usize] = Some(self.operand_not_found);
        let result = cb(self);
        if result.is_some() {
            self.operand_results[op as usize] = result;
        }
        result
    }

    fn cache_many<F, const ADDR_COUNT: usize, const OPERAND_COUNT: usize>(
        &mut self,
        addresses: &[AddressAnalysis; ADDR_COUNT],
        operands: &[OperandAnalysis; OPERAND_COUNT],
        func: F,
    )
    where F: FnOnce(&mut AnalysisCache<'e, E>) ->
        Option<([Option<E::VirtualAddress>; ADDR_COUNT], [Option<Operand<'e>>; OPERAND_COUNT])>
    {
        for &addr in addresses {
            self.address_results[addr as usize] = E::VirtualAddress::from_u64(1);
        }
        for &op in operands {
            self.operand_results[op as usize] = Some(self.operand_not_found);
        }
        let result = func(self);
        if let Some(ref res) = result {
            for i in 0..ADDR_COUNT {
                if let Some(addr) = res.0[i] {
                    self.address_results[addresses[i] as usize] = addr;
                }
            }
            for i in 0..OPERAND_COUNT {
                if let Some(op) = res.1[i] {
                    self.operand_results[operands[i] as usize] = Some(op);
                }
            }
        }
    }

    fn cache_many_addr<F>(
        &mut self,
        addr: AddressAnalysis,
        cache_fn: F,
    ) -> Option<E::VirtualAddress>
    where F: FnOnce(&mut AnalysisCache<'e, E>)
    {
        if self.address_results[addr as usize] == E::VirtualAddress::from_u64(0) {
            cache_fn(self);
        }
        Some(self.address_results[addr as usize])
            .filter(|&addr| addr != E::VirtualAddress::from_u64(1))
    }

    fn cache_many_op<F>(&mut self, op: OperandAnalysis, cache_fn: F) -> Option<Operand<'e>>
    where F: FnOnce(&mut AnalysisCache<'e, E>)
    {
        if self.operand_results[op as usize].is_none() {
            cache_fn(self);
        }
        self.operand_results[op as usize]
            .filter(|&op| op != self.operand_not_found)
    }

    pub fn firegraft_addresses(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<FiregraftAddresses<E::VirtualAddress>> {
        if let Some(cached) = self.firegraft_addresses.cached() {
            return cached;
        }
        let functions = &self.function_finder();
        let relocs = functions.globals_with_values();
        let buttonsets = firegraft::find_buttonsets(actx);
        let status_funcs = firegraft::find_unit_status_funcs(actx, &functions);
        let reqs = firegraft::find_requirement_tables(actx, &functions, relocs);
        let result = Rc::new(FiregraftAddresses {
            buttonsets,
            requirement_table_refs: reqs,
            unit_status_funcs: status_funcs,
        });
        self.firegraft_addresses.cache(&result);
        result
    }

    /// Returns address and dat table struct size
    pub fn dat_virtual_address(
        &mut self,
        ty: DatType,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<(E::VirtualAddress, u32)> {
        let dat = self.dat(ty, actx);
        let result = dat.iter()
            .filter_map(|x| x.address.if_constant().map(|y| (y, x.entry_size)))
            .next()
            .map(|(addr, size)| (E::VirtualAddress::from_u64(addr), size));
        result
    }

    pub fn dat(&mut self, ty: DatType, actx: &AnalysisCtx<'e, E>) -> Option<DatTablePtr<'e>> {
        let filename = {
            let (field, filename) = self.dat_tables.field(ty);
            if let Some(ref f) = *field {
                return f.clone();
            }
            filename
        };
        let result = dat::dat_table(actx, filename, &self.function_finder());
        let (field, _) = self.dat_tables.field(ty);
        *field = Some(result.clone());
        result
    }

    fn open_file(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::OpenFile, |s| {
            file::open_file(actx, &s.function_finder())
        })
    }

    fn cache_rng(&mut self, actx: &AnalysisCtx<'e, E>) {
        self.cache_many(&[], &[OperandAnalysis::RngSeed, OperandAnalysis::RngEnable], |s| {
            let units_dat = s.dat_virtual_address(DatType::Units, actx)?;
            let rng = rng::rng(actx, units_dat, &s.function_finder());
            Some(([], [rng.seed, rng.enable]))
        })
    }

    pub fn rng_enable(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::RngEnable, |s| s.cache_rng(actx))
    }

    fn step_objects(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::StepObjects, |s| {
            game::step_objects(actx, s.rng_enable(actx)?, &s.function_finder())
        })
    }

    pub fn game(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::Game, |s| {
            game::game(actx, s.step_objects(actx)?)
        })
    }

    fn aiscript_hook(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<AiScriptHook<'e, E::VirtualAddress>> {
        self.ai_spend_money(actx);
        self.aiscript_hook
    }

    fn aiscript_switch_table(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<E::VirtualAddress> {
        Some(self.aiscript_hook(actx)?.switch_table)
    }

    fn cache_regions(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[GetRegion, ChangeAiRegionState], &[OperandAnalysis::AiRegions], |s| {
            let aiscript_hook = s.aiscript_hook(actx);
            let result = pathing::regions(actx, aiscript_hook.as_ref()?);
            Some(([result.get_region, result.change_ai_region_state], [result.ai_regions]))
        })
    }

    fn get_region(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::GetRegion, |s| s.cache_regions(actx))
    }

    fn ai_regions(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::AiRegions, |s| s.cache_regions(actx))
    }

    fn pathing(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::Pathing, |s| {
            let get_region = s.get_region(actx)?;
            pathing::pathing(actx, get_region)
        })
    }

    fn cache_active_hidden_units(&mut self, actx: &AnalysisCtx<'e, E>) {
        use OperandAnalysis::*;
        self.cache_many(&[], &[FirstActiveUnit, FirstHiddenUnit], |s| {
            let orders_dat = s.dat_virtual_address(DatType::Orders, actx)?;
            let functions = s.function_finder();
            let result = units::active_hidden_units(actx, orders_dat, &functions);
            Some(([], [result.first_active_unit, result.first_hidden_unit]))
        })
    }

    fn first_active_unit(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(
            OperandAnalysis::FirstActiveUnit,
            |s| s.cache_active_hidden_units(actx),
        )
    }

    fn first_hidden_unit(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(
            OperandAnalysis::FirstHiddenUnit,
            |s| s.cache_active_hidden_units(actx),
        )
    }

    fn cache_order_issuing(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[OrderInitArbiter, PrepareIssueOrder, DoNextQueuedOrder], &[], |s| {
            let units_dat = s.dat_virtual_address(DatType::Units, actx)?;
            let functions = s.function_finder();
            let result = units::order_issuing(actx, units_dat, &functions);
            Some(([result.order_init_arbiter, result.prepare_issue_order,
                result.do_next_queued_order], []))
        })
    }

    fn prepare_issue_order(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::PrepareIssueOrder, |s| s.cache_order_issuing(actx))
    }

    fn order_init_arbiter(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::OrderInitArbiter, |s| s.cache_order_issuing(actx))
    }

    pub fn process_commands_switch(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<CompleteSwitch<'e>> {
        if let Some(cached) = self.process_commands_switch.cached() {
            return cached;
        }
        let func = self.process_commands(actx)?;
        let result = commands::analyze_process_fn_switch(actx, func);
        self.process_commands_switch.cache(&result);
        result
    }

    pub fn process_lobby_commands_switch(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<CompleteSwitch<'e>> {
        if let Some(cached) = self.process_lobby_commands_switch.cached() {
            return cached;
        }
        let func = self.process_lobby_commands(actx)?;
        let result = commands::analyze_process_fn_switch(actx, func);
        self.process_lobby_commands_switch.cache(&result);
        result
    }

    pub fn command_user(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::CommandUser, |s| {
            let switch = s.process_commands_switch(actx)?;
            commands::command_user(actx, s.game(actx)?, &switch)
        })
    }

    fn command_lengths(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Vec<u32>> {
        if let Some(cached) = self.command_lengths.cached() {
            return cached;
        }

        let result = commands::command_lengths(actx);
        let result = Rc::new(result);
        self.command_lengths.cache(&result);
        result
    }

    fn cache_selections(&mut self, actx: &AnalysisCtx<'e, E>) {
        use OperandAnalysis::*;
        self.cache_many(&[], &[UniqueCommandUser, Selections], |s| {
            let switch = s.process_commands_switch(actx)?;
            let result = commands::selections(actx, &switch);
            Some(([], [result.unique_command_user, result.selections]))
        })
    }

    fn selections(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::Selections, |s| s.cache_selections(actx))
    }

    fn is_replay(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::IsReplay, |s| {
            let switch = s.process_commands_switch(actx)?;
            commands::is_replay(actx, &switch)
        })
    }

    fn send_command(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::SendCommand, |s| {
            commands::send_command(actx, &s.firegraft_addresses(actx))
        })
    }

    fn cache_print_text(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[PrintText, AddToReplayData], &[], |s| {
            let process_commands = s.process_commands(actx)?;
            let switch = s.process_commands_switch(actx)?;
            let result = commands::print_text(actx, process_commands, &switch);
            Some(([result.print_text, result.add_to_replay_data], []))
        })
    }

    fn cache_init_map(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[InitMapFromPath, MapInitChkCallbacks], &[], |s| {
            let result = game_init::init_map_from_path(actx, &s.function_finder())?;
            Some(([Some(result.init_map_from_path), Some(result.map_init_chk_callbacks)], []))
        })
    }

    fn init_map_from_path(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::InitMapFromPath, |s| s.cache_init_map(actx))
    }

    fn map_init_chk_callbacks(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::MapInitChkCallbacks, |s| s.cache_init_map(actx))
    }

    fn choose_snp(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::ChooseSnp, |s| {
            let vtables = s.vtables(actx);
            game_init::choose_snp(actx, &s.function_finder(), &vtables)
        })
    }

    fn renderer_vtables(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Vec<E::VirtualAddress>> { if let Some(cached) = self.renderer_vtables.cached() {
            return cached;
        }
        let vtables = self.vtables(actx);
        let result = Rc::new(
            vtables.vtables_starting_with(b".?AVRenderer@@\0").map(|x| x.address).collect()
        );
        self.renderer_vtables.cache(&result);
        result
    }

    fn vtables(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Vtables<'e, E::VirtualAddress>> {
        if let Some(cached) = self.vtables.cached() {
            return cached;
        }
        let relocs = self.relocs();
        let result = Rc::new(vtables::vtables(actx, &relocs));
        self.vtables.cache(&result);
        result
    }

    fn all_vtables(&mut self, actx: &AnalysisCtx<'e, E>) -> Vec<E::VirtualAddress> {
        let mut result = self.vtables(actx).all_vtables().iter()
            .map(|x| x.address)
            .collect::<Vec<_>>();
        result.sort_unstable();
        result.dedup();
        result
    }

    fn vtables_for_class(
        &mut self,
        name: &[u8],
        actx: &AnalysisCtx<'e, E>,
    ) -> Vec<E::VirtualAddress> {
        let vtables = self.vtables(actx);
        let mut result = vtables.vtables_starting_with(name)
            .map(|x| x.address)
            .collect::<Vec<_>>();
        result.sort_unstable();
        result.dedup();
        result
    }

    fn cache_single_player_start(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(&[SinglePlayerStart], &[
            LocalStormPlayerId, LocalUniquePlayerId, NetPlayerToGame, NetPlayerToUnique,
            GameData, Skins, PlayerSkins,
        ], |s| {
            let choose_snp = s.choose_snp(actx)?;
            let local_player_id = s.local_player_id(actx)?;
            let functions = s.function_finder();
            let result =
                game_init::single_player_start(actx, &functions, choose_snp, local_player_id);
            s.skins_size = result.skins_size as u16;
            Some(([result.single_player_start], [result.local_storm_player_id,
                result.local_unique_player_id, result.net_player_to_game,
                result.net_player_to_unique, result.game_data, result.skins,
                result.player_skins]))
        })
    }

    fn single_player_start(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(
            AddressAnalysis::SinglePlayerStart,
            |s| s.cache_single_player_start(actx),
        )
    }

    fn local_storm_player_id(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(
            OperandAnalysis::LocalStormPlayerId,
            |s| s.cache_single_player_start(actx),
        )
    }

    fn local_player_id(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::LocalPlayerId, |s| {
            players::local_player_id(actx, s.game_screen_rclick(actx)?)
        })
    }

    fn cache_game_screen_rclick(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[GameScreenRClick], &[OperandAnalysis::ClientSelection], |s| {
            let units_dat = s.dat_virtual_address(DatType::Units, actx)?;
            let functions = s.function_finder();
            let result = clientside::game_screen_rclick(actx, units_dat, &functions);
            Some(([result.game_screen_rclick], [result.client_selection]))
        });
    }

    fn game_screen_rclick(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(
            AddressAnalysis::GameScreenRClick,
            |s| s.cache_game_screen_rclick(actx),
        )
    }

    fn cache_select_map_entry(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[SelectMapEntry], &[OperandAnalysis::IsMultiplayer], |s| {
            let single_player_start = s.single_player_start(actx)?;
            let functions = s.function_finder();
            let result = game_init::select_map_entry(actx, single_player_start, &functions);
            Some(([result.select_map_entry], [result.is_multiplayer]))
        })
    }

    fn select_map_entry(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::SelectMapEntry, |s| s.cache_select_map_entry(actx))
    }

    fn is_multiplayer(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::IsMultiplayer, |s| s.cache_select_map_entry(actx))
    }

    fn load_images(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::LoadImages, |s| {
            game_init::load_images(actx, &s.function_finder())
        })
    }

    fn cache_images_loaded(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(&[InitRealTimeLighting], &[ImagesLoaded, AssetScale], |s| {
            let load_images = s.load_images(actx)?;
            let result = game_init::images_loaded(actx, load_images, &s.function_finder());
            Some(([result.init_real_time_lighting], [result.images_loaded, result.asset_scale]))
        })
    }

    fn local_player_name(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::LocalPlayerName, |s| {
            let vtables = s.vtables(actx);
            let relocs = s.relocs();
            game_init::local_player_name(actx, &relocs, &vtables)
        })
    }

    fn cache_step_network(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(&[ReceiveStormTurns, ProcessCommands, ProcessLobbyCommands], &[
            NetPlayerFlags, PlayerTurns, PlayerTurnsSize, NetworkReady, StormCommandUser,
        ], |s| {
            let step_network = s.step_network(actx)?;
            let result = commands::analyze_step_network(actx, step_network);
            Some(([result.receive_storm_turns, result.process_commands,
                result.process_lobby_commands], [result.net_player_flags, result.player_turns,
                result.player_turns_size, result.network_ready, result.storm_command_user]))
        })
    }

    fn cache_net_format_turn_rate(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(&[NetFormatTurnRate], &[NetUserLatency], |s| {
            let result = network::anaylze_net_format_turn_rate(actx, &s.function_finder());
            Some(([result.net_format_turn_rate], [result.net_user_latency]))
        })
    }

    fn net_user_latency(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::NetUserLatency, |s| s.cache_net_format_turn_rate(actx))
    }

    fn net_format_turn_rate(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::NetFormatTurnRate,
                             |s| s.cache_net_format_turn_rate(actx))
    }

    fn process_commands(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::ProcessCommands, |s| s.cache_step_network(actx))
    }

    fn process_lobby_commands(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(
            AddressAnalysis::ProcessLobbyCommands,
            |s| s.cache_step_network(actx),
        )
    }

    fn init_game_network(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::InitGameNetwork, |s| {
            let local_storm_player_id = s.local_storm_player_id(actx)?;
            let vtables = s.vtables(actx);
            game_init::init_game_network(actx, local_storm_player_id, &vtables)
        })
    }

    fn snp_definitions(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<SnpDefinitions<'e>> {
        if let Some(cached) = self.snp_definitions.cached() {
            return cached;
        }
        let result = network::snp_definitions(actx);
        self.snp_definitions.cache(&result);
        result
    }

    fn lobby_state(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::LobbyState, |s| {
            let switch = s.process_lobby_commands_switch(actx)?;
            game_init::lobby_state(actx, &switch)
        })
    }

    fn cache_init_storm_networking(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[InitStormNetworking, LoadSnpList], &[], |s| {
            let vtables = s.vtables(actx);
            let result = network::init_storm_networking(actx, &vtables);
            Some(([result.init_storm_networking, result.load_snp_list], []))
        })
    }

    fn step_order(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::StepOrder, |s| {
            let order_init_arbiter = s.order_init_arbiter(actx)?;
            let funcs = s.function_finder();
            step_order::step_order(actx, order_init_arbiter, &funcs)
        })
    }

    fn step_order_hidden(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<Vec<step_order::StepOrderHiddenHook<'e, E::VirtualAddress>>> {
        if let Some(cached) = self.step_order_hidden.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let step_hidden = self.step_hidden_unit_frame(actx)?;
            Some(step_order::step_order_hidden(actx, step_hidden))
        }).unwrap_or_else(|| Vec::new());
        let result = Rc::new(result);
        self.step_order_hidden.cache(&result);
        result
    }

    fn step_secondary_order(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<Vec<step_order::SecondaryOrderHook<'e, E::VirtualAddress>>> {
        if let Some(cached) = self.step_secondary_order.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let step_order = self.step_order(actx)?;
            Some(step_order::step_secondary_order(actx, step_order, &self.function_finder()))
        }).unwrap_or_else(|| Vec::new());
        let result = Rc::new(result);
        self.step_secondary_order.cache(&result);
        result
    }

    pub fn step_iscript(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::StepIscript, |s| {
            let finish_unit_pre = s.finish_unit_pre(actx)?;
            let sprite_size = s.sprite_array(actx)?.1;
            iscript::step_iscript(actx, finish_unit_pre, sprite_size)
        })
    }

    fn cache_step_iscript(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(&[StepIscriptSwitch], &[IscriptBin], |s| {
            let step_iscript = s.step_iscript(actx)?;
            let result = iscript::analyze_step_iscript(actx, step_iscript);
            s.step_iscript_hook = result.hook;
            Some(([result.switch_table], [result.iscript_bin]))
        })
    }

    pub fn step_iscript_switch(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::StepIscriptSwitch, |s| s.cache_step_iscript(actx))
    }

    fn add_overlay_iscript(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::AddOverlayIscript, |s| {
            iscript::add_overlay_iscript(actx, s.step_iscript_switch(actx)?)
        })
    }

    fn draw_cursor_marker(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::DrawCursorMarker, |s| {
            iscript::draw_cursor_marker(actx, s.step_iscript_switch(actx)?)
        })
    }

    fn play_smk(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::PlaySmk, |s| {
            game_init::play_smk(actx, &s.function_finder())
        })
    }

    fn cache_game_init(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(&[ScMain, MainMenuEntryHook, GameLoop, RunMenus], &[ScMainState], |s| {
            let play_smk = s.play_smk(actx)?;
            let game = s.game(actx)?;
            let result = game_init::game_init(actx, play_smk, game, &s.function_finder());
            Some((
                [result.sc_main, result.mainmenu_entry_hook, result.game_loop, result.run_menus],
                [result.scmain_state],
            ))
        })
    }

    fn game_loop(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::GameLoop, |s| s.cache_game_init(actx))
    }

    fn run_menus(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::RunMenus, |s| s.cache_game_init(actx))
    }

    fn scmain_state(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::ScMainState, |s| s.cache_game_init(actx))
    }

    fn cache_misc_clientside(&mut self, actx: &AnalysisCtx<'e, E>) {
        use OperandAnalysis::*;
        self.cache_many(&[], &[IsPaused, IsPlacingBuilding, IsTargeting], |s| {
            let is_multiplayer = s.is_multiplayer(actx)?;
            let scmain_state = s.scmain_state(actx)?;
            let vtables = s.vtables(actx);
            let result =
                clientside::misc_clientside(actx, is_multiplayer, scmain_state, &vtables);
            Some(([], [result.is_paused, result.is_placing_building, result.is_targeting]))
        })
    }

    fn is_placing_building(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::IsPlacingBuilding, |s| s.cache_misc_clientside(actx))
    }

    fn is_targeting(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::IsTargeting, |s| s.cache_misc_clientside(actx))
    }

    fn cache_init_units(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[InitUnits, LoadDat], &[], |s| {
            let units_dat = s.dat_virtual_address(DatType::Units, actx)?;
            let orders_dat = s.dat_virtual_address(DatType::Orders, actx)?;
            let funcs = s.function_finder();
            let result = units::init_units(actx, units_dat, orders_dat, &funcs);
            Some(([result.init_units, result.load_dat], []))
        })
    }

    pub fn init_units(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::InitUnits, |s| s.cache_init_units(actx))
    }

    pub fn load_dat(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::LoadDat, |s| s.cache_init_units(actx))
    }

    pub fn units(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::Units, |s| {
            units::units(actx, s.init_units(actx)?)
        })
    }

    pub fn first_guard_ai(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::FirstGuardAi, |s| {
            let units_dat = s.dat_virtual_address(DatType::Units, actx)?;
            ai::first_guard_ai(actx, units_dat, &s.function_finder())
        })
    }

    pub fn player_ai_towns(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::PlayerAiTowns, |s| {
            let aiscript_switch = s.aiscript_switch_table(actx)?;
            ai::player_ai_towns(actx, aiscript_switch)
        })
    }

    pub fn player_ai(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::PlayerAi, |s| {
            ai::player_ai(actx, s.aiscript_hook(actx).as_ref()?)
        })
    }

    fn cache_init_game(&mut self, actx: &AnalysisCtx<'e, E>) {
        self.cache_many(&[AddressAnalysis::InitGame], &[OperandAnalysis::LoadedSave], |s| {
            let init_units = s.init_units(actx)?;
            let result = game_init::init_game(actx, init_units, &s.function_finder());
            Some(([result.init_game], [result.loaded_save]))
        })
    }

    fn init_game(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::InitGame, |s| s.cache_init_game(actx))
    }

    fn cache_sprites(&mut self, actx: &AnalysisCtx<'e, E>) {
        use OperandAnalysis::*;
        self.cache_many(&[AddressAnalysis::CreateLoneSprite], &[
            SpriteHlines, SpriteHlinesEnd, FirstFreeSprite, LastFreeSprite, FirstLoneSprite,
            LastLoneSprite, FirstFreeLoneSprite, LastFreeLoneSprite,
        ], |s| {
            let step_order = s.step_order(actx)?;
            let order_nuke_track = step_order::find_order_nuke_track(actx, step_order)?;
            let result = sprites::sprites(actx, order_nuke_track);
            s.sprite_x_position = result.sprite_x_position;
            s.sprite_y_position = result.sprite_y_position;
            Some(([result.create_lone_sprite], [
                result.sprite_hlines, result.sprite_hlines_end, result.first_free_sprite,
                result.last_free_sprite, result.first_lone, result.last_lone,
                result.first_free_lone, result.last_free_lone,
            ]))
        })
    }

    fn first_lone_sprite(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::FirstLoneSprite, |s| s.cache_sprites(actx))
    }

    fn first_free_sprite(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::FirstFreeSprite, |s| s.cache_sprites(actx))
    }

    fn last_free_sprite(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::LastFreeSprite, |s| s.cache_sprites(actx))
    }

    fn sprite_hlines_end(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::SpriteHlinesEnd, |s| s.cache_sprites(actx))
    }

    fn eud_table(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<EudTable<'e>> {
        if let Some(cached) = self.eud.cached() {
            return cached;
        }
        let result = eud::eud_table(actx, &self.function_finder());
        let result = Rc::new(result);
        self.eud.cache(&result);
        result
    }

    fn cache_map_tile_flags(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[UpdateVisibilityPoint], &[OperandAnalysis::MapTileFlags], |s| {
            let step_order = s.step_order(actx)?;
            let order_nuke_track = step_order::find_order_nuke_track(actx, step_order)?;
            let result = map::map_tile_flags(actx, order_nuke_track);
            Some(([result.update_visibility_point], [result.map_tile_flags]))
        })
    }

    fn cache_draw_game_layer(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[PrepareDrawImage, DrawImage], &[OperandAnalysis::CursorMarker], |s| {
            let draw_game_layer = s.draw_game_layer(actx)?;
            let sprite_size = s.sprite_array(actx)?.1;
            let result = renderer::analyze_draw_game_layer(actx, draw_game_layer, sprite_size);
            Some(([result.prepare_draw_image, result.draw_image], [result.cursor_marker]))
        })
    }

    fn draw_image(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::DrawImage, |s| s.cache_draw_game_layer(actx))
    }

    fn cache_bullet_creation(&mut self, actx: &AnalysisCtx<'e, E>) {
        use OperandAnalysis::*;
        self.cache_many(&[AddressAnalysis::CreateBullet], &[
            FirstActiveBullet, LastActiveBullet, FirstFreeBullet, LastFreeBullet,
            ActiveIscriptUnit,
        ], |s| {
            let result = bullets::bullet_creation(actx, s.step_iscript_switch(actx)?);
            Some(([result.create_bullet], [result.first_active_bullet, result.last_active_bullet,
                result.first_free_bullet, result.last_free_bullet, result.active_iscript_unit]))
        })
    }

    fn active_iscript_unit(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::ActiveIscriptUnit, |s| s.cache_bullet_creation(actx))
    }

    fn first_active_bullet(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::FirstActiveBullet, |s| s.cache_bullet_creation(actx))
    }

    fn cache_net_players(&mut self, actx: &AnalysisCtx<'e, E>) {
        self.cache_many(&[AddressAnalysis::InitNetPlayer], &[OperandAnalysis::NetPlayers], |s| {
            let switch = s.process_lobby_commands_switch(actx)?;
            let result = players::net_players(actx, &switch);
            s.net_player_size = result.net_players.map(|x| x.1).unwrap_or(0) as u16;
            Some(([result.init_net_player], [result.net_players.map(|x| x.0)]))
        })
    }

    fn campaigns(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::Campaigns, |_| {
            campaign::campaigns(actx)
        })
    }

    fn cache_run_dialog(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[RunDialog, GluCmpgnEventHandler], &[], |s| {
            let result = dialog::run_dialog(actx, &s.function_finder());
            Some(([result.run_dialog, result.glucmpgn_event_handler], []))
        })
    }

    fn run_dialog(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::RunDialog, |s| s.cache_run_dialog(actx))
    }

    fn glucmpgn_event_handler(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::GluCmpgnEventHandler, |s| s.cache_run_dialog(actx))
    }

    fn ai_update_attack_target(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::AiUpdateAttackTarget, |s| {
            let step_order = s.step_order(actx)?;
            let order_computer_return = step_order::find_order_function(actx, step_order, 0xa3)?;
            ai::ai_update_attack_target(actx, order_computer_return)
        })
    }

    fn is_outside_game_screen(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::IsOutsideGameScreen, |s| {
            let game_screen_rclick = s.game_screen_rclick(actx)?;
            clientside::is_outside_game_screen(actx, game_screen_rclick)
        })
    }

    fn cache_coord_conversion(&mut self, actx: &AnalysisCtx<'e, E>) {
        use OperandAnalysis::*;
        self.cache_many(&[], &[ScreenX, ScreenY, Zoom], |s| {
            let game_screen_rclick = s.game_screen_rclick(actx)?;
            let is_outside_game_screen = s.is_outside_game_screen(actx)?;
            let result = clientside::game_coord_conversion(
                actx,
                game_screen_rclick,
                is_outside_game_screen
            );
            Some(([], [result.screen_x, result.screen_y, result.scale]))
        })
    }

    fn cache_fow_sprites(&mut self, actx: &AnalysisCtx<'e, E>) {
        use OperandAnalysis::*;
        self.cache_many(&[], &[
            FirstFowSprite, LastFowSprite, FirstFreeFowSprite, LastFreeFowSprite,
        ], |s| {
            let step_objects = s.step_objects(actx)?;
            let first_lone = s.first_lone_sprite(actx)?;
            let result = sprites::fow_sprites(actx, step_objects, first_lone);
            Some(([], [
                result.first_active, result.last_active, result.first_free, result.last_free,
            ]))
        })
    }

    fn first_fow_sprite(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::FirstFowSprite, |s| s.cache_fow_sprites(actx))
    }

    fn first_free_fow_sprite(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::FirstFreeFowSprite, |s| s.cache_fow_sprites(actx))
    }

    fn spawn_dialog(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::SpawnDialog, |s| {
            dialog::spawn_dialog(actx, &s.function_finder())
        })
    }

    fn cache_unit_creation(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[CreateUnit, FinishUnitPre, FinishUnitPost], &[], |s| {
            let step_order = s.step_order(actx)?;
            let order_scan = step_order::find_order_function(actx, step_order, 0x8b)?;
            let result = units::unit_creation(actx, order_scan);
            Some(([result.create_unit, result.finish_unit_pre, result.finish_unit_post], []))
        })
    }

    fn finish_unit_pre(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::FinishUnitPre, |s| s.cache_unit_creation(actx))
    }

    fn fonts(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::Fonts, |s| {
            text::fonts(actx, &s.function_finder())
        })
    }

    fn cache_init_sprites(&mut self, actx: &AnalysisCtx<'e, E>) {
        self.cache_many(&[AddressAnalysis::InitSprites], &[OperandAnalysis::Sprites], |s| {
            let first_free = s.first_free_sprite(actx)?;
            let last_free = s.last_free_sprite(actx)?;
            let functions = s.function_finder();
            let result = sprites::init_sprites(actx, first_free, last_free, &functions);
            s.sprite_struct_size = result.sprites.map(|x| x.1 as u16).unwrap_or(0);
            Some(([result.init_sprites], [result.sprites.map(|x| x.0)]))
        })
    }

    fn init_sprites(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::InitSprites, |s| s.cache_init_sprites(actx))
    }

    fn sprite_array(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<(Operand<'e>, u32)> {
        self.cache_many_op(OperandAnalysis::Sprites, |s| s.cache_init_sprites(actx))
            .map(|x| (x, self.sprite_struct_size.into()))
    }

    fn cache_sprite_serialization(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[SerializeSprites, DeserializeSprites], &[], |s| {
            let hlines_end = s.sprite_hlines_end(actx)?;
            let sprite_array = s.sprite_array(actx)?;
            let init_sprites = s.init_sprites(actx)?;
            let game = s.game(actx)?;
            let funcs = s.function_finder();
            let result = save::sprite_serialization(
                actx,
                hlines_end,
                sprite_array,
                init_sprites,
                game,
                &funcs,
            );
            Some(([result.serialize_sprites, result.deserialize_sprites], []))
        })
    }

    fn limits(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Limits<'e, E::VirtualAddress>> {
        if let Some(cached) = self.limits.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let game_loop = self.game_loop(actx)?;
            Some(game::limits(actx, game_loop))
        }).unwrap_or_else(|| {
            Limits {
                set_limits: None,
                arrays: Vec::new(),
                smem_alloc: None,
                smem_free: None,
                allocator: None,
            }
        });
        let result = Rc::new(result);
        self.limits.cache(&result);
        result
    }

    fn cache_font_render(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[FontCacheRenderAscii, TtfCacheCharacter, TtfRenderSdf], &[], |s| {
            let result = text::font_render(actx, s.fonts(actx)?, &s.function_finder());
            Some(([
                result.font_cache_render_ascii, result.ttf_cache_character, result.ttf_render_sdf
            ], []))
        })
    }

    fn ttf_render_sdf(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::TtfRenderSdf, |s| s.cache_font_render(actx))
    }

    fn ttf_malloc(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::TtfMalloc, |s| {
            text::ttf_malloc(actx, s.ttf_render_sdf(actx)?)
        })
    }

    fn cache_select_map_entry_children(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(
            &[CreateGameMultiplayer, MapEntryLoadMap, MapEntryLoadReplay, MapEntryLoadSave],
            &[],
            |s| {
                let select_map_entry = s.select_map_entry(actx)?;
                let result = game_init::analyze_select_map_entry(actx, select_map_entry);
                s.create_game_dialog_vtbl_on_multiplayer_create =
                    result.create_game_dialog_vtbl_on_multiplayer_create;
                Some(([result.create_game_multiplayer, result.mde_load_map,
                        result.mde_load_replay, result.mde_load_save], []))
            },
        );
    }

    fn cache_tooltip_related(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(
            &[LayoutDrawText, DrawF10MenuTooltip, DrawTooltipLayer],
            &[TooltipDrawFunc, CurrentTooltipCtrl, GraphicLayers],
            |s| {
                let spawn_dialog = s.spawn_dialog(actx)?;
                let result = dialog::tooltip_related(actx, spawn_dialog, &s.function_finder());
                Some((
                    [result.layout_draw_text, result.draw_f10_menu_tooltip,
                    result.draw_tooltip_layer], [result.tooltip_draw_func,
                    result.current_tooltip_ctrl, result.graphic_layers],
                ))
            })
    }

    fn graphic_layers(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::GraphicLayers, |s| s.cache_tooltip_related(actx))
    }

    fn draw_graphic_layers(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::DrawGraphicLayers, |s| {
            dialog::draw_graphic_layers(actx, s.graphic_layers(actx)?, &s.function_finder())
        })
    }

    fn prism_shaders(&mut self, actx: &AnalysisCtx<'e, E>) -> PrismShaders<E::VirtualAddress> {
        if let Some(cached) = self.prism_shaders.cached() {
            return cached;
        }
        let vtables = self.vtables(actx);
        let result = renderer::prism_shaders(actx, &vtables);
        self.prism_shaders.cache(&result);
        result
    }

    fn prism_vertex_shaders(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Vec<E::VirtualAddress>> {
        self.prism_shaders(actx).vertex_shaders
    }

    fn prism_pixel_shaders(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Vec<E::VirtualAddress>> {
        self.prism_shaders(actx).pixel_shaders
    }

    fn ai_attack_prepare(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::AiAttackPrepare, |s| {
            let aiscript_switch = s.aiscript_switch_table(actx)?;
            ai::attack_prepare(actx, aiscript_switch)
        })
    }

    fn cache_ai_step_frame(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(
            &[AiStepRegion, AiSpendMoney, StepAiScript], &[FirstAiScript, Players],
            |s| {
                let step_objects = s.step_objects(actx)?;
                let game = s.game(actx)?;
                let result = ai::step_frame_funcs(actx, step_objects, game);
                s.aiscript_hook = result.hook;
                Some(([result.ai_step_region, result.ai_spend_money, result.step_ai_script],
                    [result.first_ai_script, result.players]))
            },
        )
    }

    pub fn ai_spend_money(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::AiSpendMoney, |s| s.cache_ai_step_frame(actx))
    }

    pub fn step_ai_script(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::StepAiScript, |s| s.cache_ai_step_frame(actx))
    }

    pub fn join_game(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::JoinGame, |s| {
            let local_storm_id = s.local_storm_player_id(actx)?;
            game_init::join_game(actx, local_storm_id, &s.function_finder())
        })
    }

    fn snet_initialize_provider(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::SnetInitializeProvider, |s| {
            game_init::snet_initialize_provider(actx, s.choose_snp(actx)?)
        })
    }

    fn set_status_screen_tooltip(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<E::VirtualAddress> {
        self.dat_patches(actx)?.set_status_screen_tooltip
    }

    fn dat_patches(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<Rc<DatPatches<'e, E::VirtualAddress>>> {
        if let Some(cached) = self.dat_patches.cached() {
            return cached;
        }
        let result = dat::dat_patches(self, actx).map(|x| Rc::new(x));
        self.dat_patches.cache(&result);
        result
    }

    fn cache_do_attack(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(&[DoAttack, DoAttackMain], &[LastBulletSpawner], |s| {
            let step_order = s.step_order(actx)?;
            let attack_order = step_order::find_order_function(actx, step_order, 0xa)?;
            let result = step_order::do_attack(actx, attack_order)?;
            Some(([Some(result.do_attack), Some(result.do_attack_main)],
                [Some(result.last_bullet_spawner)]))
        })
    }

    fn smem_alloc(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.limits(actx).smem_alloc
    }

    fn smem_free(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.limits(actx).smem_free
    }

    fn allocator(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.limits(actx).allocator
    }

    fn cache_cmdicons(&mut self, actx: &AnalysisCtx<'e, E>) {
        use OperandAnalysis::*;
        self.cache_many(&[], &[CmdIconsDdsGrp, CmdBtnsDdsGrp], |s| {
            let firegraft = s.firegraft_addresses(actx);
            let &status_arr = firegraft.unit_status_funcs.get(0)?;
            let result = dialog::button_ddsgrps(actx, status_arr);
            Some(([], [result.cmdicons, result.cmdbtns]))
        })
    }

    fn cache_mouse_xy(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(&[GetMouseX, GetMouseY], &[MouseX, MouseY], |s| {
            let run_dialog = s.run_dialog(actx)?;
            let result = dialog::mouse_xy(actx, run_dialog);
            Some(([result.x_func, result.y_func], [result.x_var, result.y_var]))
        })
    }

    fn status_screen_mode(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::StatusScreenMode, |s| {
            let firegraft = s.firegraft_addresses(actx);
            let &status_arr = firegraft.unit_status_funcs.get(0)?;
            dialog::status_screen_mode(actx, status_arr)
        })
    }

    fn cache_unit_requirements(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(&[CheckUnitRequirements], &[DatRequirementError], |s| {
            let units_dat = s.dat_virtual_address(DatType::Units, actx)?;
            let funcs = s.function_finder();
            let result = requirements::check_unit_requirements(actx, units_dat, &funcs)?;
            Some(([Some(result.check_unit_requirements)], [Some(result.requirement_error)]))
        })
    }

    fn check_dat_requirements(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::CheckDatRequirements, |s| {
            let techdata = s.dat_virtual_address(DatType::TechData, actx)?;
            let functions = s.function_finder();
            requirements::check_dat_requirements(actx, techdata, &functions)
        })
    }

    fn cheat_flags(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::CheatFlags, |s| {
            requirements::cheat_flags(actx, s.check_dat_requirements(actx)?)
        })
    }

    fn cache_unit_strength_etc(&mut self, actx: &AnalysisCtx<'e, E>) {
        use OperandAnalysis::*;
        self.cache_many(
            &[],
            &[UnitStrength, SpriteIncludeInVisionSync],
            |s| {
                let result = units::strength(actx, s.init_game(actx)?, s.init_units(actx)?);
                Some((
                    [],
                    [result.unit_strength, result.sprite_include_in_vision_sync],
                ))
            })
    }

    pub fn unit_strength(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::UnitStrength, |s| s.cache_unit_strength_etc(actx))
    }

    pub fn sprite_include_in_vision_sync(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<Operand<'e>> {
        self.cache_many_op(
            OperandAnalysis::SpriteIncludeInVisionSync,
            |s| s.cache_unit_strength_etc(actx),
        )
    }

    /// Smaller size wireframes, that is multiselection and transport
    /// (Fits multiple in status screen)
    /// Also relevant mostly for SD, HD always uses wirefram.ddsgrp for the drawing.
    fn cache_multi_wireframes(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(
            &[InitStatusScreen, StatusScreenEventHandler],
            &[GrpWireGrp, GrpWireDdsGrp, TranWireGrp, TranWireDdsGrp, StatusScreen],
            |s| {
                let spawn_dialog = s.spawn_dialog(actx)?;
                let result = dialog::multi_wireframes(actx, spawn_dialog, &s.function_finder());
                Some((
                    [result.init_status_screen, result.status_screen_event_handler],
                    [result.grpwire_grp, result.grpwire_ddsgrp, result.tranwire_grp,
                    result.tranwire_ddsgrp, result.status_screen]
                ))
            })
    }

    pub fn grpwire_grp(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::GrpWireGrp, |s| s.cache_multi_wireframes(actx))
    }

    pub fn grpwire_ddsgrp(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::GrpWireDdsGrp, |s| s.cache_multi_wireframes(actx))
    }

    pub fn tranwire_grp(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::TranWireGrp, |s| s.cache_multi_wireframes(actx))
    }

    pub fn tranwire_ddsgrp(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::TranWireDdsGrp, |s| s.cache_multi_wireframes(actx))
    }

    pub fn status_screen(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_many_op(OperandAnalysis::StatusScreen, |s| s.cache_multi_wireframes(actx))
    }

    pub fn status_screen_event_handler(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<E::VirtualAddress> {
        self.cache_many_addr(
            AddressAnalysis::StatusScreenEventHandler,
            |s| s.cache_multi_wireframes(actx),
        )
    }

    pub fn wirefram_ddsgrp(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::WireframDdsgrp, |s| {
            dialog::wirefram_ddsgrp(actx, s.status_screen_event_handler(actx)?)
        })
    }

    pub fn init_status_screen(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(
            AddressAnalysis::InitStatusScreen,
            |s| s.cache_multi_wireframes(actx),
        )
    }

    fn run_triggers(&mut self, actx: &AnalysisCtx<'e, E>) -> RunTriggers<E::VirtualAddress> {
        if let Some(cached) = self.run_triggers.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let rng_enable = self.rng_enable(actx)?;
            let step_objects = self.step_objects(actx)?;
            Some(map::run_triggers(actx, rng_enable, step_objects, &self.function_finder()))
        }).unwrap_or_else(|| RunTriggers::default());
        self.run_triggers.cache(&result);
        result
    }

    pub fn trigger_conditions(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.run_triggers(actx).conditions
    }

    pub fn trigger_actions(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.run_triggers(actx).actions
    }

    pub fn trigger_unit_count_caches(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> TriggerUnitCountCaches<'e> {
        if let Some(cached) = self.trigger_unit_count_caches.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let conditions = self.trigger_conditions(actx)?;
            let game = self.game(actx)?;
            Some(map::trigger_unit_count_caches(actx, conditions, game))
        }).unwrap_or_else(|| Default::default());
        self.trigger_unit_count_caches.cache(&result);
        result
    }

    pub fn trigger_completed_units_cache(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<Operand<'e>> {
        self.trigger_unit_count_caches(actx).completed_units
    }

    pub fn trigger_all_units_cache(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.trigger_unit_count_caches(actx).all_units
    }

    fn cache_snet_handle_packets(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[SnetSendPackets, SnetRecvPackets], &[], |s| {
            let vtables = s.vtables(actx);
            let result = network::snet_handle_packets(actx, &vtables);
            Some(([result.send_packets, result.recv_packets], []))
        })
    }

    fn chk_init_players(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::ChkInitPlayers, |s| {
            let chk_callbacks = s.map_init_chk_callbacks(actx)?;
            game_init::chk_init_players(actx, chk_callbacks)
        })
    }

    fn original_chk_player_types(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::OriginalChkPlayerTypes, |s| {
            let init_players = s.chk_init_players(actx)?;
            game_init::original_chk_player_types(actx, init_players, &s.function_finder())
        })
    }

    fn give_ai(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::GiveAi, |s| {
            let actions = s.trigger_actions(actx)?;
            let units_dat = s.dat_virtual_address(DatType::Units, actx)?;
            ai::give_ai(actx, actions, units_dat)
        })
    }

    fn play_sound(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::PlaySound, |s| {
            sound::play_sound(actx, s.step_iscript_switch(actx)?)
        })
    }

    fn ai_prepare_moving_to(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::AiPrepareMovingTo, |s| {
            let step_order = s.step_order(actx)?;
            let order_move = step_order::find_order_function(actx, step_order, 0x6)?;
            ai::ai_prepare_moving_to(actx, order_move)
        })
    }

    fn ai_transport_reachability_cached_region(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::AiTransportReachabilityCachedRegion, |s| {
            let prepare_moving = s.ai_prepare_moving_to(actx)?;
            ai::ai_transport_reachability_cached_region(actx, prepare_moving)
        })
    }

    fn player_unit_skins(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::PlayerUnitSkins, |s| {
            renderer::player_unit_skins(actx, s.draw_image(actx)?)
        })
    }

    fn replay_minimap_unexplored_fog_patch(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<Rc<Patch<E::VirtualAddress>>> {
        if let Some(cached) = self.replay_minimap_unexplored_fog_patch.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let first_fow_sprite = self.first_fow_sprite(actx)?;
            let is_replay = self.is_replay(actx)?;
            let funcs = self.function_finder();
            Some(minimap::unexplored_fog_minimap_patch(actx, first_fow_sprite, is_replay, &funcs))
        });
        let (patch, draw_minimap_units) = match result {
            Some(s) => (s.0.map(Rc::new), s.1),
            None => (None, None),
        };
        self.replay_minimap_unexplored_fog_patch.cache(&patch);
        self.cache_single_address(AddressAnalysis::DrawMinimapUnits, |_| draw_minimap_units);
        patch
    }

    fn draw_minimap_units(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        if self.address_results[AddressAnalysis::DrawMinimapUnits as usize] ==
            E::VirtualAddress::from_u64(0)
        {
            self.replay_minimap_unexplored_fog_patch(actx);
        }
        self.cache_single_address(AddressAnalysis::DrawMinimapUnits, |_| None)
    }

    fn step_replay_commands(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::StepReplayCommands, |s| {
            let process_commands = s.process_commands(actx)?;
            let game = s.game(actx)?;
            commands::step_replay_commands(actx, process_commands, game, &s.function_finder())
        })
    }

    fn replay_data(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::ReplayData, |s| {
            let switch = &s.process_commands_switch(actx)?;
            commands::replay_data(actx, &switch)
        })
    }

    fn ai_train_military(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::AiTrainMilitary, |s| {
            ai::train_military(actx, s.ai_spend_money(actx)?, s.game(actx)?)
        })
    }

    fn ai_add_military_to_region(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::AiAddMilitaryToRegion, |s| {
            let train_military = s.ai_train_military(actx)?;
            ai::add_military_to_region(actx, train_military, s.ai_regions(actx)?)
        })
    }

    fn vertex_buffer(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::VertexBuffer, |s| {
            let vtables = s.vtables(actx);
            renderer::vertex_buffer(actx, &vtables)
        })
    }

    fn crt_fastfail(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Vec<E::VirtualAddress>> {
        if let Some(cached) = self.crt_fastfail.cached() {
            return cached;
        }
        let result = Rc::new(crt::fastfail(actx));
        self.crt_fastfail.cache(&result);
        result
    }

    fn cache_ui_event_handlers(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(
            &[ResetUiEventHandlers, UiDefaultScrollHandler, TargetingLClick, TargetingRClick,
                BuildingPlacementLClick, BuildingPlacementRClick, GameScreenLClick,
                UiDefaultKeyDownHandler, UiDefaultKeyUpHandler, UiDefaultLeftDownHandler,
                UiDefaultLeftDoubleHandler, UiDefaultRightDownHandler,
                UiDefaultMiddleDownHandler, UiDefaultMiddleUpHandler, UiDefaultPeriodicHandler,
                UiDefaultCharHandler],
            &[GlobalEventHandlers, GameScreenLClickCallback, GameScreenRClickCallback],
            |s| {
                let game_screen_rclick = s.game_screen_rclick(actx)?;
                let is_targeting = s.is_targeting(actx)?;
                let is_placing_building = s.is_placing_building(actx)?;
                let result = dialog::ui_event_handlers(
                    actx,
                    game_screen_rclick,
                    is_targeting,
                    is_placing_building,
                    &s.function_finder(),
                );
                Some((
                    [result.reset_ui_event_handlers, result.default_scroll_handler,
                        result.targeting_lclick, result.targeting_rclick,
                        result.building_placement_lclick, result.building_placement_rclick,
                        result.game_screen_l_click, result.default_key_down_handler,
                        result.default_key_up_handler, result.default_left_down_handler,
                        result.default_left_double_handler, result.default_right_down_handler,
                        result.default_middle_down_handler, result.default_middle_up_handler,
                        result.default_periodic_handler, result.default_char_handler],
                    [result.global_event_handlers, result.game_screen_lclick_callback,
                        result.game_screen_rclick_callback],
                ))
            });
    }

    fn ui_default_scroll_handler(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(
            AddressAnalysis::UiDefaultScrollHandler,
            |s| s.cache_ui_event_handlers(actx),
        )
    }

    fn targeting_lclick(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(
            AddressAnalysis::TargetingLClick,
            |s| s.cache_ui_event_handlers(actx),
        )
    }

    fn clamp_zoom(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::ClampZoom, |s| {
            let scroll_handler = s.ui_default_scroll_handler(actx)?;
            let is_multiplayer = s.is_multiplayer(actx)?;
            dialog::clamp_zoom(actx, scroll_handler, is_multiplayer)
        })
    }

    fn cache_replay_visions(&mut self, actx: &AnalysisCtx<'e, E>) {
        use OperandAnalysis::*;
        self.cache_many(&[], &[ReplayVisions, ReplayShowEntireMap, FirstPlayerUnit], |s| {
            let draw_minimap_units = s.draw_minimap_units(actx)?;
            let is_replay = s.is_replay(actx)?;
            let result = minimap::replay_visions(actx, draw_minimap_units, is_replay);
            Some(([], [
                result.replay_visions, result.replay_show_entire_map, result.first_player_unit,
            ]))
        })
    }

    fn cache_menu_screens(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[SetBriefingMusic, PreMissionGlue, ShowMissionGlue], &[], |s| {
            let run_menus = s.run_menus(actx)?;
            let result = dialog::analyze_run_menus(actx, run_menus);
            Some(([result.set_music, result.pre_mission_glue, result.show_mission_glue], []))
        })
    }

    fn cache_glucmpgn_events(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(&[MenuSwishIn, MenuSwishOut], &[DialogReturnCode], |s| {
            let event_handler = s.glucmpgn_event_handler(actx)?;
            let result = dialog::analyze_glucmpgn_events(actx, event_handler);
            Some(([result.swish_in, result.swish_out], [result.dialog_return_code]))
        })
    }

    fn ai_spell_cast(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::AiSpellCast, |s| {
            let step_order = s.step_order(actx)?;
            let order_guard = step_order::find_order_function(actx, step_order, 0xa0)?;
            ai::ai_spell_cast(actx, order_guard)
        })
    }

    fn give_unit(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::GiveUnit, |s| {
            let actions = s.trigger_actions(actx)?;
            units::give_unit(actx, actions)
        })
    }

    fn set_unit_player(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::SetUnitPlayer, |s| {
            let give_unit = s.give_unit(actx)?;
            units::set_unit_player(actx, give_unit)
        })
    }

    fn cache_set_unit_player_fns(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[
            RemoveFromSelections,
            RemoveFromClientSelection,
            ClearBuildQueue,
            UnitChangingPlayer,
            PlayerGainedUpgrade,
        ], &[], |s| {
            let set_unit_player = s.set_unit_player(actx)?;
            let selections = s.selections(actx)?;
            let result = units::analyze_set_unit_player(actx, set_unit_player, selections);
            Some(([
                result.remove_from_selections, result.remove_from_client_selection,
                result.clear_build_queue, result.unit_changing_player,
                result.player_gained_upgrade,
            ], []))
        })
    }

    fn unit_changing_player(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(
            AddressAnalysis::UnitChangingPlayer,
            |s| s.cache_set_unit_player_fns(actx),
        )
    }

    fn cache_unit_speed(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(&[
            UnitApplySpeedUpgrades,
            UnitUpdateSpeed,
            UnitUpdateSpeedIscript,
            UnitBuffedFlingySpeed,
            UnitBuffedAcceleration,
            UnitBuffedTurnSpeed,
        ], &[], |s| {
            let unit_changing_player = s.unit_changing_player(actx)?;
            let step_iscript = s.step_iscript(actx)?;
            let units_dat = s.dat_virtual_address(DatType::Units, actx)?;
            let flingy_dat = s.dat_virtual_address(DatType::Flingy, actx)?;
            let result = units::unit_apply_speed_upgrades(
                actx,
                units_dat,
                flingy_dat,
                unit_changing_player,
                step_iscript,
            );
            Some(([
                result.apply_speed_upgrades, result.update_speed, result.update_speed_iscript,
                result.buffed_flingy_speed, result.buffed_acceleration, result.buffed_turn_speed,
            ], []))
        })
    }

    fn start_udp_server(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::StartUdpServer, |s| {
            network::start_udp_server(actx, &s.function_finder())
        })
    }

    fn cache_image_loading(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(&[
            OpenAnimSingleFile, OpenAnimMultiFile, InitSkins,
            AddAssetChangeCallback, AnimAssetChangeCb,
        ], &[
            BaseAnimSet, ImageGrps, ImageOverlays, FireOverlayMax,
        ], |s| {
            let load_images = s.load_images(actx)?;
            let load_dat = s.load_dat(actx)?;
            let images_dat = s.dat_virtual_address(DatType::Images, actx)?;
            let result = game_init::analyze_load_images(
                actx,
                load_images,
                load_dat,
                images_dat,
            );
            s.anim_struct_size = result.anim_struct_size;
            Some(([
                result.open_anim_single_file, result.open_anim_multi_file, result.init_skins,
                result.add_asset_change_cb, result.anim_asset_change_cb,
            ], [
                result.base_anim_set, result.image_grps,
                result.image_overlays, result.fire_overlay_max,
            ]))
        })
    }

    fn cache_step_objects(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(&[
            StepActiveUnitFrame, StepHiddenUnitFrame, StepBulletFrame, RevealUnitArea,
            UpdateUnitVisibility, UpdateCloakState,
        ], &[
            VisionUpdateCounter, VisionUpdated, FirstDyingUnit, FirstRevealer, FirstInvisibleUnit,
            ActiveIscriptFlingy, ActiveIscriptBullet,
        ], |s| {
            let step_objects = s.step_objects(actx)?;
            let game = s.game(actx)?;
            let first_active_unit = s.first_active_unit(actx)?;
            let first_hidden_unit = s.first_hidden_unit(actx)?;
            let first_active_bullet = s.first_active_bullet(actx)?;
            let active_iscript_unit = s.active_iscript_unit(actx)?;
            let result = game::analyze_step_objects(
                actx,
                step_objects,
                game,
                first_active_unit,
                first_hidden_unit,
                first_active_bullet,
                active_iscript_unit,
            );
            Some(([
                result.step_active_frame, result.step_hidden_frame, result.step_bullet_frame,
                result.reveal_area, result.update_unit_visibility, result.update_cloak_state,
            ], [
                result.vision_update_counter, result.vision_updated, result.first_dying_unit,
                result.first_revealer, result.first_invisible_unit, result.active_iscript_flingy,
                result.active_iscript_bullet,
            ]))
        })
    }

    fn step_active_unit_frame(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::StepActiveUnitFrame, |s| s.cache_step_objects(actx))
    }

    fn step_hidden_unit_frame(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::StepHiddenUnitFrame, |s| s.cache_step_objects(actx))
    }

    fn reveal_unit_area(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::RevealUnitArea, |s| s.cache_step_objects(actx))
    }

    fn update_unit_visibility(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(
            AddressAnalysis::UpdateUnitVisibility,
            |s| s.cache_step_objects(actx),
        )
    }

    fn cache_step_active_unit(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(&[StepUnitMovement], &[UnitShouldRevealArea], |s| {
            let step_active_unit = s.step_active_unit_frame(actx)?;
            let reveal_area = s.reveal_unit_area(actx)?;
            let result = units::analyze_step_active_unit(
                actx,
                step_active_unit,
                reveal_area
            );
            Some(([result.step_unit_movement], [result.should_vision_update]))
        })
    }

    fn draw_game_layer(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::DrawGameLayer, |s| {
            let draw_layers = s.graphic_layers(actx)?;
            renderer::draw_game_layer(actx, draw_layers, &s.function_finder())
        })
    }

    fn cache_game_loop(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(
            &[StepNetwork, RenderScreen, LoadPcx, SetMusic, StepGameLoop, ProcessEvents,
            StepGameLogic],
            &[MainPalette, PaletteSet, TfontGam, SyncActive, SyncData, MenuScreenId,
            ContinueGameLoop, AntiTroll, StepGameFrames, NextGameStepTick, ReplaySeekFrame],
            |s|
        {
            let game_loop = s.game_loop(actx)?;
            let game = s.game(actx)?;
            let result = game_init::analyze_game_loop(actx, game_loop, game);
            Some(([result.step_network, result.render_screen, result.load_pcx, result.set_music,
                result.step_game_loop, result.process_events, result.step_game_logic],
                [result.main_palette, result.palette_set, result.tfontgam, result.sync_active,
                result.sync_data, result.menu_screen_id, result.continue_game_loop,
                result.anti_troll, result.step_game_frames, result.next_game_step_tick,
                result.replay_seek_frame]))
        })
    }

    pub fn step_network(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::StepNetwork, |s| s.cache_game_loop(actx))
    }

    fn process_events(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::ProcessEvents, |s| s.cache_game_loop(actx))
    }

    fn cache_prepare_issue_order(&mut self, actx: &AnalysisCtx<'e, E>) {
        use OperandAnalysis::*;
        self.cache_many(
            &[],
            &[FirstFreeOrder, LastFreeOrder, AllocatedOrderCount, ReplayBfix, ReplayGcfg],
            |s|
        {
            let prepare_issue_order = s.prepare_issue_order(actx)?;
            let result = units::analyze_prepare_issue_order(actx, prepare_issue_order);
            Some(([], [result.first_free_order, result.last_free_order,
                result.allocated_order_count, result.replay_bfix, result.replay_gcfg]))
        })
    }

    fn cache_process_events(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(
            &[StepBnetController],
            &[BnetController],
            |s|
        {
            let process_events = s.process_events(actx)?;
            let result = game_init::analyze_process_events(actx, process_events);
            s.bnet_message_switch = result.bnet_message_switch;
            s.bnet_message_vtable_type = result.message_vtable_type;
            Some(([result.step_bnet_controller], [result.bnet_controller]))
        })
    }

    fn join_param_variant_type_offset(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<usize> {
        if self.join_param_variant_type_offset == u16::MAX {
            self.join_param_variant_type_offset = 0xfffe;
            let join_game = self.join_game(actx)?;
            if let Some(result) = game_init::join_param_variant_type_offset(actx, join_game) {
                self.join_param_variant_type_offset = result;
            }
        }
        Some(self.join_param_variant_type_offset).filter(|&x| x < 0xfffe).map(|x| x as usize)
    }

    fn cache_pylon_aura(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(&[AddPylonAura], &[FirstPylon, PylonAurasVisible, PylonRefresh], |s| {
            let step_order = s.step_order(actx)?;
            let order_pylon_init = step_order::find_order_function(actx, step_order, 0xa4)?;
            let result = units::pylon_aura(actx, order_pylon_init);
            Some((
                [result.add_pylon_aura],
                [result.first_pylon, result.pylon_auras_visible, result.pylon_refresh],
            ))
        })
    }

    fn cache_sp_map_end(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(&[SinglePlayerMapEnd], &[LocalGameResult], |s| {
            let is_multiplayer = s.is_multiplayer(actx)?;
            let run_dialog = s.run_dialog(actx)?;
            let funcs = s.function_finder();
            let result =
                game_init::single_player_map_end(actx, is_multiplayer, run_dialog, &funcs);
            Some((
                [result.single_player_map_end],
                [result.local_game_result],
            ))
        })
    }

    fn single_player_map_end(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(AddressAnalysis::SinglePlayerMapEnd, |s| s.cache_sp_map_end(actx))
    }

    fn cache_sp_map_end_analysis(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(
            &[SetScmainState, UnlockMission],
            &[IsCustomSinglePlayer, CurrentCampaignMission],
            |s|
        {
            let sp_map_end = s.single_player_map_end(actx)?;
            let result = game_init::single_player_map_end_analysis(actx, sp_map_end);
            Some((
                [result.set_scmain_state, result.unlock_mission],
                [result.is_custom_single_player, result.current_campaign_mission],
            ))
        })
    }

    fn cache_update_unit_visibility(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(
            &[CreateFowSprite, DuplicateSprite],
            &[LocalVisions, FirstFreeSelectionCircle, LastFreeSelectionCircle, UnitSkinMap,
            SpriteSkinMap],
            |s|
        {
            let update_unit_visibility = s.update_unit_visibility(actx)?;
            let units = s.units(actx)?;
            let sprites = s.sprite_array(actx)?.0;
            let first_free_fow = s.first_free_fow_sprite(actx)?;
            let result = units::update_unit_visibility_analysis(
                actx,
                update_unit_visibility,
                units,
                sprites,
                first_free_fow,
            );
            Some((
                [result.create_fow_sprite, result.duplicate_sprite],
                [result.local_visions, result.first_free_selection_circle,
                result.last_free_selection_circle, result.unit_skin_map, result.sprite_skin_map],
            ))
        })
    }

    fn cache_init_map_from_path(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(
            &[LoadReplayScenarioChk, SfileCloseArchive, OpenMapMpq, ReadWholeMpqFile,
                ReadWholeMpqFile2],
            &[ReplayScenarioChk, ReplayScenarioChkSize, MapMpq, MapHistory],
            |s|
        {
            let init_map_from_path = s.init_map_from_path(actx)?;
            let is_replay = s.is_replay(actx)?;
            let game = s.game(actx)?;
            let result = game_init::init_map_from_path_analysis(
                actx,
                init_map_from_path,
                is_replay,
                game,
            );
            Some((
                [result.load_replay_scenario_chk, result.sfile_close_archive,
                    result.open_map_mpq, result.read_whole_mpq_file, result.read_whole_mpq_file2],
                [result.replay_scenario_chk, result.replay_scenario_chk_size, result.map_mpq,
                    result.map_history],
            ))
        })
    }

    fn cache_start_targeting(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        use OperandAnalysis::*;
        self.cache_many(
            &[StartTargeting],
            &[TargetedOrderUnit, TargetedOrderGround, TargetedOrderFow, MinimapCursorType],
            |s| {
                let firegraft = s.firegraft_addresses(actx);
                let buttonsets = *firegraft.buttonsets.get(0)?;
                let result = clientside::start_targeting(actx, buttonsets);
                Some((
                    [result.start_targeting],
                    [result.targeted_order_unit, result.targeted_order_ground,
                        result.targeted_order_fow, result.minimap_cursor_type],
                ))
            });
    }

    fn cache_targeting_lclick(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(
            &[FindUnitForClick, FindFowSpriteForClick, HandleTargetedClick],
            &[],
            |s| {
                let lclick = s.targeting_lclick(actx)?;
                let result = clientside::analyze_targeting_lclick(actx, lclick);
                Some((
                    [result.find_unit_for_click, result.find_fow_sprite_for_click,
                        result.handle_targeted_click],
                    [],
                ))
            });
    }

    fn handle_targeted_click(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_many_addr(
            AddressAnalysis::HandleTargetedClick,
            |s| s.cache_targeting_lclick(actx),
        )
    }

    fn cache_handle_targeted_click(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(
            &[CheckWeaponTargetingFlags, CheckTechTargeting, CheckOrderTargeting,
                CheckFowOrderTargeting],
            &[],
            |s| {
                let click = s.handle_targeted_click(actx)?;
                let orders_dat = s.dat_virtual_address(DatType::Orders, actx)?;
                let result = clientside::analyze_handle_targeted_click(actx, click, orders_dat);
                Some((
                    [result.check_weapon_targeting_flags, result.check_tech_targeting,
                        result.check_order_targeting, result.check_fow_order_targeting],
                    [],
                ))
            });
    }

    fn cache_step_order(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(
            &[AiFocusDisabled, AiFocusAir],
            &[],
            |s| {
                let step_order = s.step_order(actx)?;
                let result = step_order::step_order_analysis(actx, step_order);
                Some((
                    [result.ai_focus_disabled, result.ai_focus_air],
                    [],
                ))
            });
    }

    fn cache_open_file(&mut self, actx: &AnalysisCtx<'e, E>) {
        use AddressAnalysis::*;
        self.cache_many(
            &[FileExists],
            &[],
            |s| {
                let open_file = s.open_file(actx)?;
                let result = file::open_file_analysis(actx, open_file);
                Some((
                    [result.file_exists],
                    [],
                ))
            });
    }
}

pub struct DatPatchesDebug<'e, Va: VirtualAddress> {
    pub warnings: Vec<(&'static str, u32, String)>,
    pub tables: fxhash::FxHashMap<DatType, DatTablePatchesDebug<Va>>,
    pub replaces: Vec<(Va, Vec<u8>)>,
    pub func_replaces: Vec<(Va, DatReplaceFunc)>,
    pub hooks: Vec<(Va, u8, Vec<u8>)>,
    pub two_step_hooks: Vec<(Va, Va, u8, Vec<u8>)>,
    pub ext_array_patches: Vec<(Va, Option<Va>, u8, u32, Operand<'e>)>,
    pub ext_array_args: Vec<(Va, Vec<(usize, u8)>)>,
    pub grp_index_hooks: Vec<Va>,
    pub grp_texture_hooks: Vec<(Va, u8, Operand<'e>, Operand<'e>, Operand<'e>)>,
}

pub struct DatTablePatchesDebug<Va: VirtualAddress> {
    pub array_patches: Vec<Vec<(Va, i32, u32)>>,
    pub entry_counts: Vec<Va>,
}

impl<Va: VirtualAddress> Default for DatTablePatchesDebug<Va> {
    fn default() -> Self {
        DatTablePatchesDebug {
            array_patches: Vec::new(),
            entry_counts: Vec::new(),
        }
    }
}