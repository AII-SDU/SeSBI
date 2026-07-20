theory SeSBI_Startup_Base
  imports SeSBI_PMP_BootSequence
begin

unbundle bit_operations_syntax

section \<open>Startup base.S cold-entry model\<close>

text \<open>
  This theory models the startup responsibilities implemented by
  @{text "SeSBI-code/sbi/base.S"} before control is handed to @{text sbi_main}.
  It is an S5-lite postcondition proof over the startup state, not a
  per-instruction Sail/ISA proof of the assembled binary.

  The covered labels are:
    @{text "_start"}, @{text "_base_select_stack"},
    @{text "_base_init_mscratch"}, @{text "_base_sanitize_csrs"},
    @{text "_base_clear_bss"}, @{text "_base_reset_boot_records"},
    @{text "_base_record_primary_hart"}, @{text "_base_append_event"},
    @{text "_base_init_stack_guard"}, @{text "_base_init_hart_scratch"},
    @{text "_base_record_memory_layout"},
    @{text "_base_record_csr_snapshot"}, @{text "_base_validate_stack"},
    @{text "_base_validate_dtb"}, @{text "_base_save_boot_state"},
    @{text "_base_compute_boot_checksum"},
    @{text "_base_init_boot_state"}, @{text "_base_finalize_boot_state"},
    @{text "_base_prepare_handoff"}, @{text "_base_record_secondary_hart"},
    and @{text "_base_wait_for_release"}.
\<close>

datatype StartupNext =
    StartupEnterSbiMain
  | StartupWaitForRelease

record StartupState =
  st_hartid :: "64 word"
  st_dtb :: "64 word"
  st_mie :: "64 word"
  st_mscratch :: "64 word"
  st_satp :: "64 word"
  st_mstatus :: "64 word"
  st_sp :: "64 word"
  st_hart_index :: "64 word"
  st_boot_hartid :: "64 word"
  st_boot_hart_mask :: "64 word"
  st_boot_dtb :: "64 word"
  st_boot_stack_top :: "64 word"
  st_boot_next_addr :: "64 word"
  st_boot_magic :: "64 word"
  st_boot_flags :: "64 word"
  st_text_span :: "64 word"
  st_stack_span :: "64 word"
  st_guard_span :: "64 word"
  st_bss_span :: "64 word"
  st_scratch_span :: "64 word"
  st_boot_checksum :: "64 word"
  st_bss_cleared :: bool
  st_events_ready :: bool
  st_stack_guard_ready :: bool
  st_scratch_ready :: bool
  st_layout_ready :: bool
  st_csr_snapshot_ready :: bool
  st_stack_valid :: bool
  st_dtb_valid :: bool
  st_checksum_ready :: bool
  st_boot_ready :: bool
  st_handoff_ready :: bool
  st_secondary_seen :: bool
  st_secondary_wait_ready :: bool
  st_next :: StartupNext

subsection \<open>Constants mirrored from base.S\<close>

definition SBI_BOOT_SCRATCH_MAGIC :: "64 word" where
  "SBI_BOOT_SCRATCH_MAGIC = 0x5345534249424f4f"

definition SBI_BOOT_FLAG_DTB_VALID :: "64 word" where
  "SBI_BOOT_FLAG_DTB_VALID = 0x1"

definition SBI_BOOT_FLAG_STACK_READY :: "64 word" where
  "SBI_BOOT_FLAG_STACK_READY = 0x2"

definition SBI_BOOT_FLAG_BSS_CLEARED :: "64 word" where
  "SBI_BOOT_FLAG_BSS_CLEARED = 0x4"

definition SBI_BOOT_FLAG_GUARD_READY :: "64 word" where
  "SBI_BOOT_FLAG_GUARD_READY = 0x8"

definition STARTUP_MSTATUS_MIE :: "64 word" where
  "STARTUP_MSTATUS_MIE = push_bit 3 (mask 1)"

definition cold_boot_flags :: "64 word \<Rightarrow> 64 word" where
  "cold_boot_flags dtb =
     SBI_BOOT_FLAG_STACK_READY OR
     SBI_BOOT_FLAG_BSS_CLEARED OR
     SBI_BOOT_FLAG_GUARD_READY OR
     (if dtb = 0 then 0 else SBI_BOOT_FLAG_DTB_VALID)"

subsection \<open>base.S label-level state transformers\<close>

definition base_entry_reset :: "StartupState \<Rightarrow> StartupState" where
  "base_entry_reset s = s\<lparr> st_mie := 0, st_mscratch := 0 \<rparr>"

definition base_sanitize_csrs :: "StartupState \<Rightarrow> StartupState" where
  "base_sanitize_csrs s =
     s\<lparr> st_mie := 0,
        st_satp := 0,
        st_mstatus := st_mstatus s AND NOT STARTUP_MSTATUS_MIE \<rparr>"

definition base_setup_stack :: "64 word \<Rightarrow> StartupState \<Rightarrow> StartupState" where
  "base_setup_stack stack_top s =
     s\<lparr> st_sp := stack_top, st_mscratch := stack_top \<rparr>"

definition base_select_stack ::
  "64 word \<Rightarrow> 64 word \<Rightarrow> StartupState \<Rightarrow> StartupState" where
  "base_select_stack hart_index stack_top s =
     s\<lparr> st_hart_index := hart_index, st_sp := stack_top \<rparr>"

definition base_init_mscratch :: "StartupState \<Rightarrow> StartupState" where
  "base_init_mscratch s =
     s\<lparr> st_mscratch := st_sp s,
        st_boot_stack_top := st_sp s,
        st_boot_flags := st_boot_flags s OR SBI_BOOT_FLAG_STACK_READY \<rparr>"

definition base_clear_bss :: "StartupState \<Rightarrow> StartupState" where
  "base_clear_bss s = s\<lparr> st_bss_cleared := True \<rparr>"

definition base_reset_boot_records :: "StartupState \<Rightarrow> StartupState" where
  "base_reset_boot_records s =
     s\<lparr> st_boot_flags := SBI_BOOT_FLAG_BSS_CLEARED,
        st_events_ready := False,
        st_scratch_ready := False,
        st_layout_ready := False,
        st_csr_snapshot_ready := False,
        st_checksum_ready := False,
        st_boot_ready := False,
        st_handoff_ready := False \<rparr>"

definition base_record_primary_hart ::
  "64 word \<Rightarrow> StartupState \<Rightarrow> StartupState" where
  "base_record_primary_hart hart_mask s =
     s\<lparr> st_boot_hartid := st_hartid s,
        st_boot_dtb := st_dtb s,
        st_boot_hart_mask := hart_mask \<rparr>"

definition base_append_event :: "StartupState \<Rightarrow> StartupState" where
  "base_append_event s = s\<lparr> st_events_ready := True \<rparr>"

definition base_init_stack_guard :: "StartupState \<Rightarrow> StartupState" where
  "base_init_stack_guard s = s\<lparr> st_stack_guard_ready := True \<rparr>"

definition base_init_hart_scratch :: "StartupState \<Rightarrow> StartupState" where
  "base_init_hart_scratch s = s\<lparr> st_scratch_ready := True \<rparr>"

definition base_record_memory_layout ::
  "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
   StartupState \<Rightarrow> StartupState" where
  "base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s =
     s\<lparr> st_layout_ready := True,
        st_text_span := text_span,
        st_stack_span := stack_span,
        st_guard_span := guard_span,
        st_bss_span := bss_span,
        st_scratch_span := scratch_span \<rparr>"

definition base_record_csr_snapshot :: "StartupState \<Rightarrow> StartupState" where
  "base_record_csr_snapshot s = s\<lparr> st_csr_snapshot_ready := True \<rparr>"

definition base_validate_stack :: "bool \<Rightarrow> StartupState \<Rightarrow> StartupState" where
  "base_validate_stack stack_ok s = s\<lparr> st_stack_valid := stack_ok \<rparr>"

definition base_validate_dtb :: "bool \<Rightarrow> StartupState \<Rightarrow> StartupState" where
  "base_validate_dtb dtb_ok s = s\<lparr> st_dtb_valid := dtb_ok \<rparr>"

definition base_save_boot_state :: "StartupState \<Rightarrow> StartupState" where
  "base_save_boot_state s =
     s\<lparr> st_boot_hartid := st_hartid s,
        st_boot_dtb := st_dtb s,
        st_boot_stack_top := st_sp s,
        st_boot_next_addr := FW_JUMP_ADDR,
        st_boot_magic := SBI_BOOT_SCRATCH_MAGIC,
        st_boot_flags := cold_boot_flags (st_dtb s) \<rparr>"

definition base_compute_boot_checksum ::
  "64 word \<Rightarrow> StartupState \<Rightarrow> StartupState" where
  "base_compute_boot_checksum checksum s =
     s\<lparr> st_boot_checksum := checksum, st_checksum_ready := True \<rparr>"

definition base_init_boot_state :: "StartupState \<Rightarrow> StartupState" where
  "base_init_boot_state s =
     s\<lparr> st_mie := 0,
        st_mstatus := st_mstatus s AND NOT MSTATUS_MPP \<rparr>"

definition base_finalize_boot_state :: "StartupState \<Rightarrow> StartupState" where
  "base_finalize_boot_state s = s\<lparr> st_boot_ready := True \<rparr>"

definition base_prepare_handoff :: "StartupState \<Rightarrow> StartupState" where
  "base_prepare_handoff s =
     s\<lparr> st_handoff_ready := True,
        st_boot_next_addr := FW_JUMP_ADDR \<rparr>"

definition base_enter_sbi_main :: "StartupState \<Rightarrow> StartupState" where
  "base_enter_sbi_main s = s\<lparr> st_next := StartupEnterSbiMain \<rparr>"

definition base_record_secondary_hart :: "StartupState \<Rightarrow> StartupState" where
  "base_record_secondary_hart s =
     s\<lparr> st_secondary_seen := True,
        st_boot_hartid := st_hartid s,
        st_boot_dtb := st_dtb s \<rparr>"

definition base_wait_for_release :: "StartupState \<Rightarrow> StartupState" where
  "base_wait_for_release s =
     s\<lparr> st_mie := 0,
        st_mscratch := 0,
        st_secondary_wait_ready := True,
        st_next := StartupWaitForRelease \<rparr>"

definition base_cold_path ::
  "64 word \<Rightarrow> StartupState \<Rightarrow> StartupState" where
  "base_cold_path stack_top s =
     base_enter_sbi_main
       (base_init_boot_state
         (base_save_boot_state
           (base_init_stack_guard
             (base_clear_bss
               (base_setup_stack stack_top
                 (base_sanitize_csrs
                   (base_entry_reset s)))))))"

definition base_secondary_path :: "StartupState \<Rightarrow> StartupState" where
  "base_secondary_path s = base_wait_for_release (base_entry_reset s)"

subsection \<open>Postconditions for the cold path\<close>

definition startup_cold_post ::
  "64 word \<Rightarrow> StartupState \<Rightarrow> StartupState \<Rightarrow> bool" where
  "startup_cold_post stack_top s0 s \<longleftrightarrow>
     st_next s = StartupEnterSbiMain \<and>
     st_mie s = 0 \<and>
     st_mscratch s = st_sp s \<and>
     st_sp s = stack_top \<and>
     st_satp s = 0 \<and>
     st_bss_cleared s \<and>
     st_stack_guard_ready s \<and>
     st_boot_hartid s = st_hartid s0 \<and>
     st_boot_dtb s = st_dtb s0 \<and>
     st_boot_stack_top s = stack_top \<and>
     st_boot_next_addr s = FW_JUMP_ADDR \<and>
     st_boot_magic s = SBI_BOOT_SCRATCH_MAGIC \<and>
   st_boot_flags s = cold_boot_flags (st_dtb s0)"

theorem base_sanitize_csrs_post:
  "st_mie (base_sanitize_csrs s) = 0 \<and>
   st_satp (base_sanitize_csrs s) = 0 \<and>
   st_mstatus (base_sanitize_csrs s) =
     st_mstatus s AND NOT STARTUP_MSTATUS_MIE"
  by (simp add: base_sanitize_csrs_def)

theorem base_sanitize_csrs_clears_mstatus_mie:
  "get_field (st_mstatus (base_sanitize_csrs s)) 3 1 = 0"
  apply (simp add: base_sanitize_csrs_def)
  apply (unfold get_field_def STARTUP_MSTATUS_MIE_def)
  apply (rule bit_word_eqI)
  apply (simp only: bit_simps possible_bit_word len64 comp_def bit_0_eq bot_fun_def)
  apply (simp; presburger)
  done

theorem base_setup_stack_mscratch:
  "st_sp (base_setup_stack stack_top s) = stack_top \<and>
   st_mscratch (base_setup_stack stack_top s) = stack_top"
  by (simp add: base_setup_stack_def)

theorem base_select_stack_post:
  "st_hart_index (base_select_stack hart_index stack_top s) = hart_index \<and>
   st_sp (base_select_stack hart_index stack_top s) = stack_top"
  by (simp add: base_select_stack_def)

theorem base_init_mscratch_post:
  "st_mscratch (base_init_mscratch s) = st_sp s \<and>
   st_boot_stack_top (base_init_mscratch s) = st_sp s \<and>
   st_boot_flags (base_init_mscratch s) =
     st_boot_flags s OR SBI_BOOT_FLAG_STACK_READY"
  by (simp add: base_init_mscratch_def)

theorem base_clear_bss_post:
  "st_bss_cleared (base_clear_bss s)"
  by (simp add: base_clear_bss_def)

theorem base_reset_boot_records_post:
  "st_boot_flags (base_reset_boot_records s) = SBI_BOOT_FLAG_BSS_CLEARED \<and>
   \<not> st_events_ready (base_reset_boot_records s) \<and>
   \<not> st_scratch_ready (base_reset_boot_records s) \<and>
   \<not> st_layout_ready (base_reset_boot_records s) \<and>
   \<not> st_csr_snapshot_ready (base_reset_boot_records s) \<and>
   \<not> st_checksum_ready (base_reset_boot_records s) \<and>
   \<not> st_boot_ready (base_reset_boot_records s) \<and>
   \<not> st_handoff_ready (base_reset_boot_records s)"
  by (simp add: base_reset_boot_records_def)

theorem base_record_primary_hart_post:
  "st_boot_hartid (base_record_primary_hart hart_mask s) = st_hartid s \<and>
   st_boot_dtb (base_record_primary_hart hart_mask s) = st_dtb s \<and>
   st_boot_hart_mask (base_record_primary_hart hart_mask s) = hart_mask"
  by (simp add: base_record_primary_hart_def)

theorem base_append_event_post:
  "st_events_ready (base_append_event s)"
  by (simp add: base_append_event_def)

theorem base_init_stack_guard_post:
  "st_stack_guard_ready (base_init_stack_guard s)"
  by (simp add: base_init_stack_guard_def)

theorem base_init_hart_scratch_post:
  "st_scratch_ready (base_init_hart_scratch s)"
  by (simp add: base_init_hart_scratch_def)

theorem base_record_memory_layout_post:
  "st_layout_ready
     (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) \<and>
   st_text_span
     (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) =
       text_span \<and>
   st_stack_span
     (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) =
       stack_span \<and>
   st_guard_span
     (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) =
       guard_span \<and>
   st_bss_span
     (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) =
       bss_span \<and>
   st_scratch_span
     (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) =
       scratch_span"
  by (simp add: base_record_memory_layout_def)

theorem base_record_csr_snapshot_post:
  "st_csr_snapshot_ready (base_record_csr_snapshot s)"
  by (simp add: base_record_csr_snapshot_def)

theorem base_validate_stack_post:
  "st_stack_valid (base_validate_stack stack_ok s) = stack_ok"
  by (simp add: base_validate_stack_def)

theorem base_validate_dtb_post:
  "st_dtb_valid (base_validate_dtb dtb_ok s) = dtb_ok"
  by (simp add: base_validate_dtb_def)

theorem base_save_boot_state_post:
  "st_boot_hartid (base_save_boot_state s) = st_hartid s \<and>
   st_boot_dtb (base_save_boot_state s) = st_dtb s \<and>
   st_boot_stack_top (base_save_boot_state s) = st_sp s \<and>
   st_boot_next_addr (base_save_boot_state s) = FW_JUMP_ADDR \<and>
   st_boot_magic (base_save_boot_state s) = SBI_BOOT_SCRATCH_MAGIC \<and>
   st_boot_flags (base_save_boot_state s) = cold_boot_flags (st_dtb s)"
  by (simp add: base_save_boot_state_def)

theorem base_compute_boot_checksum_post:
  "st_boot_checksum (base_compute_boot_checksum checksum s) = checksum \<and>
   st_checksum_ready (base_compute_boot_checksum checksum s)"
  by (simp add: base_compute_boot_checksum_def)

theorem base_init_boot_state_post:
  "st_mie (base_init_boot_state s) = 0 \<and>
   st_mstatus (base_init_boot_state s) = st_mstatus s AND NOT MSTATUS_MPP"
  by (simp add: base_init_boot_state_def)

theorem base_finalize_boot_state_post:
  "st_boot_ready (base_finalize_boot_state s)"
  by (simp add: base_finalize_boot_state_def)

theorem base_prepare_handoff_post:
  "st_handoff_ready (base_prepare_handoff s) \<and>
   st_boot_next_addr (base_prepare_handoff s) = FW_JUMP_ADDR"
  by (simp add: base_prepare_handoff_def)

theorem base_cold_path_post:
  "startup_cold_post stack_top s
     (base_cold_path stack_top s)"
  by (simp add: startup_cold_post_def base_cold_path_def
                base_entry_reset_def base_sanitize_csrs_def base_setup_stack_def
                base_clear_bss_def base_init_stack_guard_def
                base_save_boot_state_def base_init_boot_state_def
                base_enter_sbi_main_def)

theorem base_secondary_path_post:
  "st_next (base_secondary_path s) = StartupWaitForRelease \<and>
   st_mie (base_secondary_path s) = 0 \<and>
   st_mscratch (base_secondary_path s) = 0"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

theorem base_record_secondary_hart_post:
  "st_secondary_seen (base_record_secondary_hart s) \<and>
   st_boot_hartid (base_record_secondary_hart s) = st_hartid s \<and>
   st_boot_dtb (base_record_secondary_hart s) = st_dtb s"
  by (simp add: base_record_secondary_hart_def)

theorem base_wait_for_release_post:
  "st_next (base_wait_for_release s) = StartupWaitForRelease \<and>
   st_mie (base_wait_for_release s) = 0 \<and>
   st_mscratch (base_wait_for_release s) = 0 \<and>
   st_secondary_wait_ready (base_wait_for_release s)"
  by (simp add: base_wait_for_release_def)

theorem startup_handoff_then_current_boot_prepares_smode:
  "startup_cold_post stack_top s
     (base_cold_path stack_top s) \<and>
   smode_entry_setup (current_boot_state old_mstatus)"
  using current_boot_prepares_smode_entry base_cold_path_post by blast

theorem startup_handoff_then_corrected_boot_prepares_smode:
  "startup_cold_post stack_top s
     (base_cold_path stack_top s) \<and>
   smode_entry_setup (corrected_boot_state old_mstatus fw_start k rest)"
  using corrected_boot_prepares_smode_entry base_cold_path_post by blast

end
