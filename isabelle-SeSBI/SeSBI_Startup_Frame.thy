theory SeSBI_Startup_Frame
  imports SeSBI_Startup_Base
begin

section \<open>Startup base.S frame-condition inventory\<close>

definition base_full_cold_path ::
  "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
   bool \<Rightarrow> bool \<Rightarrow> 64 word \<Rightarrow> StartupState \<Rightarrow> StartupState" where
  "base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s =
     base_enter_sbi_main
       (base_prepare_handoff
         (base_append_event
           (base_finalize_boot_state
             (base_init_boot_state
               (base_compute_boot_checksum checksum
                 (base_append_event
                   (base_save_boot_state
                     (base_append_event
                       (base_validate_dtb dtb_ok
                         (base_validate_stack stack_ok
                           (base_append_event
                             (base_record_csr_snapshot
                               (base_append_event
                                 (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span
                                   (base_append_event
                                     (base_init_hart_scratch
                                       (base_append_event
                                         (base_init_stack_guard
                                           (base_append_event
                                             (base_append_event
                                               (base_append_event
                                                 (base_append_event
                                                   (base_append_event
                                                     (base_record_primary_hart hart_mask
                                                       (base_reset_boot_records
                                                         (base_clear_bss
                                                           (base_sanitize_csrs
                                                             (base_init_mscratch
                                                               (base_select_stack hart_index stack_top
                                                                 (base_entry_reset s))))))))))))))))))))))))))))))"

subsection \<open>Per-label field equations\<close>

lemma startup_frame_base_entry_reset_hartid:
  shows
    "st_hartid (base_entry_reset s) = st_hartid s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_dtb:
  shows
    "st_dtb (base_entry_reset s) = st_dtb s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_mie:
  shows
    "st_mie (base_entry_reset s) = 0"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_mscratch:
  shows
    "st_mscratch (base_entry_reset s) = 0"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_satp:
  shows
    "st_satp (base_entry_reset s) = st_satp s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_mstatus:
  shows
    "st_mstatus (base_entry_reset s) = st_mstatus s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_sp:
  shows
    "st_sp (base_entry_reset s) = st_sp s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_hart_index:
  shows
    "st_hart_index (base_entry_reset s) = st_hart_index s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_boot_hartid:
  shows
    "st_boot_hartid (base_entry_reset s) = st_boot_hartid s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_entry_reset s) = st_boot_hart_mask s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_boot_dtb:
  shows
    "st_boot_dtb (base_entry_reset s) = st_boot_dtb s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_boot_stack_top:
  shows
    "st_boot_stack_top (base_entry_reset s) = st_boot_stack_top s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_boot_next_addr:
  shows
    "st_boot_next_addr (base_entry_reset s) = st_boot_next_addr s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_boot_magic:
  shows
    "st_boot_magic (base_entry_reset s) = st_boot_magic s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_boot_flags:
  shows
    "st_boot_flags (base_entry_reset s) = st_boot_flags s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_text_span:
  shows
    "st_text_span (base_entry_reset s) = st_text_span s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_stack_span:
  shows
    "st_stack_span (base_entry_reset s) = st_stack_span s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_guard_span:
  shows
    "st_guard_span (base_entry_reset s) = st_guard_span s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_bss_span:
  shows
    "st_bss_span (base_entry_reset s) = st_bss_span s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_scratch_span:
  shows
    "st_scratch_span (base_entry_reset s) = st_scratch_span s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_boot_checksum:
  shows
    "st_boot_checksum (base_entry_reset s) = st_boot_checksum s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_bss_cleared:
  shows
    "st_bss_cleared (base_entry_reset s) = st_bss_cleared s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_events_ready:
  shows
    "st_events_ready (base_entry_reset s) = st_events_ready s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_entry_reset s) = st_stack_guard_ready s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_scratch_ready:
  shows
    "st_scratch_ready (base_entry_reset s) = st_scratch_ready s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_layout_ready:
  shows
    "st_layout_ready (base_entry_reset s) = st_layout_ready s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_entry_reset s) = st_csr_snapshot_ready s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_stack_valid:
  shows
    "st_stack_valid (base_entry_reset s) = st_stack_valid s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_dtb_valid:
  shows
    "st_dtb_valid (base_entry_reset s) = st_dtb_valid s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_checksum_ready:
  shows
    "st_checksum_ready (base_entry_reset s) = st_checksum_ready s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_boot_ready:
  shows
    "st_boot_ready (base_entry_reset s) = st_boot_ready s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_handoff_ready:
  shows
    "st_handoff_ready (base_entry_reset s) = st_handoff_ready s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_secondary_seen:
  shows
    "st_secondary_seen (base_entry_reset s) = st_secondary_seen s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_entry_reset s) = st_secondary_wait_ready s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_entry_reset_next:
  shows
    "st_next (base_entry_reset s) = st_next s"
  by (simp add: base_entry_reset_def)

lemma startup_frame_base_sanitize_csrs_hartid:
  shows
    "st_hartid (base_sanitize_csrs s) = st_hartid s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_dtb:
  shows
    "st_dtb (base_sanitize_csrs s) = st_dtb s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_mie:
  shows
    "st_mie (base_sanitize_csrs s) = 0"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_mscratch:
  shows
    "st_mscratch (base_sanitize_csrs s) = st_mscratch s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_satp:
  shows
    "st_satp (base_sanitize_csrs s) = 0"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_mstatus:
  shows
    "st_mstatus (base_sanitize_csrs s) = st_mstatus s AND NOT STARTUP_MSTATUS_MIE"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_sp:
  shows
    "st_sp (base_sanitize_csrs s) = st_sp s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_hart_index:
  shows
    "st_hart_index (base_sanitize_csrs s) = st_hart_index s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_boot_hartid:
  shows
    "st_boot_hartid (base_sanitize_csrs s) = st_boot_hartid s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_sanitize_csrs s) = st_boot_hart_mask s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_boot_dtb:
  shows
    "st_boot_dtb (base_sanitize_csrs s) = st_boot_dtb s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_boot_stack_top:
  shows
    "st_boot_stack_top (base_sanitize_csrs s) = st_boot_stack_top s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_boot_next_addr:
  shows
    "st_boot_next_addr (base_sanitize_csrs s) = st_boot_next_addr s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_boot_magic:
  shows
    "st_boot_magic (base_sanitize_csrs s) = st_boot_magic s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_boot_flags:
  shows
    "st_boot_flags (base_sanitize_csrs s) = st_boot_flags s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_text_span:
  shows
    "st_text_span (base_sanitize_csrs s) = st_text_span s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_stack_span:
  shows
    "st_stack_span (base_sanitize_csrs s) = st_stack_span s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_guard_span:
  shows
    "st_guard_span (base_sanitize_csrs s) = st_guard_span s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_bss_span:
  shows
    "st_bss_span (base_sanitize_csrs s) = st_bss_span s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_scratch_span:
  shows
    "st_scratch_span (base_sanitize_csrs s) = st_scratch_span s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_boot_checksum:
  shows
    "st_boot_checksum (base_sanitize_csrs s) = st_boot_checksum s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_bss_cleared:
  shows
    "st_bss_cleared (base_sanitize_csrs s) = st_bss_cleared s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_events_ready:
  shows
    "st_events_ready (base_sanitize_csrs s) = st_events_ready s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_sanitize_csrs s) = st_stack_guard_ready s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_scratch_ready:
  shows
    "st_scratch_ready (base_sanitize_csrs s) = st_scratch_ready s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_layout_ready:
  shows
    "st_layout_ready (base_sanitize_csrs s) = st_layout_ready s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_sanitize_csrs s) = st_csr_snapshot_ready s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_stack_valid:
  shows
    "st_stack_valid (base_sanitize_csrs s) = st_stack_valid s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_dtb_valid:
  shows
    "st_dtb_valid (base_sanitize_csrs s) = st_dtb_valid s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_checksum_ready:
  shows
    "st_checksum_ready (base_sanitize_csrs s) = st_checksum_ready s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_boot_ready:
  shows
    "st_boot_ready (base_sanitize_csrs s) = st_boot_ready s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_handoff_ready:
  shows
    "st_handoff_ready (base_sanitize_csrs s) = st_handoff_ready s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_secondary_seen:
  shows
    "st_secondary_seen (base_sanitize_csrs s) = st_secondary_seen s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_sanitize_csrs s) = st_secondary_wait_ready s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_sanitize_csrs_next:
  shows
    "st_next (base_sanitize_csrs s) = st_next s"
  by (simp add: base_sanitize_csrs_def)

lemma startup_frame_base_setup_stack_hartid:
  shows
    "st_hartid (base_setup_stack stack_top s) = st_hartid s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_dtb:
  shows
    "st_dtb (base_setup_stack stack_top s) = st_dtb s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_mie:
  shows
    "st_mie (base_setup_stack stack_top s) = st_mie s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_mscratch:
  shows
    "st_mscratch (base_setup_stack stack_top s) = stack_top"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_satp:
  shows
    "st_satp (base_setup_stack stack_top s) = st_satp s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_mstatus:
  shows
    "st_mstatus (base_setup_stack stack_top s) = st_mstatus s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_sp:
  shows
    "st_sp (base_setup_stack stack_top s) = stack_top"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_hart_index:
  shows
    "st_hart_index (base_setup_stack stack_top s) = st_hart_index s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_boot_hartid:
  shows
    "st_boot_hartid (base_setup_stack stack_top s) = st_boot_hartid s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_setup_stack stack_top s) = st_boot_hart_mask s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_boot_dtb:
  shows
    "st_boot_dtb (base_setup_stack stack_top s) = st_boot_dtb s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_boot_stack_top:
  shows
    "st_boot_stack_top (base_setup_stack stack_top s) = st_boot_stack_top s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_boot_next_addr:
  shows
    "st_boot_next_addr (base_setup_stack stack_top s) = st_boot_next_addr s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_boot_magic:
  shows
    "st_boot_magic (base_setup_stack stack_top s) = st_boot_magic s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_boot_flags:
  shows
    "st_boot_flags (base_setup_stack stack_top s) = st_boot_flags s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_text_span:
  shows
    "st_text_span (base_setup_stack stack_top s) = st_text_span s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_stack_span:
  shows
    "st_stack_span (base_setup_stack stack_top s) = st_stack_span s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_guard_span:
  shows
    "st_guard_span (base_setup_stack stack_top s) = st_guard_span s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_bss_span:
  shows
    "st_bss_span (base_setup_stack stack_top s) = st_bss_span s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_scratch_span:
  shows
    "st_scratch_span (base_setup_stack stack_top s) = st_scratch_span s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_boot_checksum:
  shows
    "st_boot_checksum (base_setup_stack stack_top s) = st_boot_checksum s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_bss_cleared:
  shows
    "st_bss_cleared (base_setup_stack stack_top s) = st_bss_cleared s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_events_ready:
  shows
    "st_events_ready (base_setup_stack stack_top s) = st_events_ready s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_setup_stack stack_top s) = st_stack_guard_ready s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_scratch_ready:
  shows
    "st_scratch_ready (base_setup_stack stack_top s) = st_scratch_ready s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_layout_ready:
  shows
    "st_layout_ready (base_setup_stack stack_top s) = st_layout_ready s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_setup_stack stack_top s) = st_csr_snapshot_ready s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_stack_valid:
  shows
    "st_stack_valid (base_setup_stack stack_top s) = st_stack_valid s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_dtb_valid:
  shows
    "st_dtb_valid (base_setup_stack stack_top s) = st_dtb_valid s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_checksum_ready:
  shows
    "st_checksum_ready (base_setup_stack stack_top s) = st_checksum_ready s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_boot_ready:
  shows
    "st_boot_ready (base_setup_stack stack_top s) = st_boot_ready s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_handoff_ready:
  shows
    "st_handoff_ready (base_setup_stack stack_top s) = st_handoff_ready s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_secondary_seen:
  shows
    "st_secondary_seen (base_setup_stack stack_top s) = st_secondary_seen s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_setup_stack stack_top s) = st_secondary_wait_ready s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_setup_stack_next:
  shows
    "st_next (base_setup_stack stack_top s) = st_next s"
  by (simp add: base_setup_stack_def)

lemma startup_frame_base_select_stack_hartid:
  shows
    "st_hartid (base_select_stack hart_index stack_top s) = st_hartid s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_dtb:
  shows
    "st_dtb (base_select_stack hart_index stack_top s) = st_dtb s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_mie:
  shows
    "st_mie (base_select_stack hart_index stack_top s) = st_mie s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_mscratch:
  shows
    "st_mscratch (base_select_stack hart_index stack_top s) = st_mscratch s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_satp:
  shows
    "st_satp (base_select_stack hart_index stack_top s) = st_satp s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_mstatus:
  shows
    "st_mstatus (base_select_stack hart_index stack_top s) = st_mstatus s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_sp:
  shows
    "st_sp (base_select_stack hart_index stack_top s) = stack_top"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_hart_index:
  shows
    "st_hart_index (base_select_stack hart_index stack_top s) = hart_index"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_boot_hartid:
  shows
    "st_boot_hartid (base_select_stack hart_index stack_top s) = st_boot_hartid s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_select_stack hart_index stack_top s) = st_boot_hart_mask s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_boot_dtb:
  shows
    "st_boot_dtb (base_select_stack hart_index stack_top s) = st_boot_dtb s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_boot_stack_top:
  shows
    "st_boot_stack_top (base_select_stack hart_index stack_top s) = st_boot_stack_top s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_boot_next_addr:
  shows
    "st_boot_next_addr (base_select_stack hart_index stack_top s) = st_boot_next_addr s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_boot_magic:
  shows
    "st_boot_magic (base_select_stack hart_index stack_top s) = st_boot_magic s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_boot_flags:
  shows
    "st_boot_flags (base_select_stack hart_index stack_top s) = st_boot_flags s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_text_span:
  shows
    "st_text_span (base_select_stack hart_index stack_top s) = st_text_span s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_stack_span:
  shows
    "st_stack_span (base_select_stack hart_index stack_top s) = st_stack_span s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_guard_span:
  shows
    "st_guard_span (base_select_stack hart_index stack_top s) = st_guard_span s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_bss_span:
  shows
    "st_bss_span (base_select_stack hart_index stack_top s) = st_bss_span s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_scratch_span:
  shows
    "st_scratch_span (base_select_stack hart_index stack_top s) = st_scratch_span s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_boot_checksum:
  shows
    "st_boot_checksum (base_select_stack hart_index stack_top s) = st_boot_checksum s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_bss_cleared:
  shows
    "st_bss_cleared (base_select_stack hart_index stack_top s) = st_bss_cleared s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_events_ready:
  shows
    "st_events_ready (base_select_stack hart_index stack_top s) = st_events_ready s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_select_stack hart_index stack_top s) = st_stack_guard_ready s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_scratch_ready:
  shows
    "st_scratch_ready (base_select_stack hart_index stack_top s) = st_scratch_ready s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_layout_ready:
  shows
    "st_layout_ready (base_select_stack hart_index stack_top s) = st_layout_ready s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_select_stack hart_index stack_top s) = st_csr_snapshot_ready s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_stack_valid:
  shows
    "st_stack_valid (base_select_stack hart_index stack_top s) = st_stack_valid s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_dtb_valid:
  shows
    "st_dtb_valid (base_select_stack hart_index stack_top s) = st_dtb_valid s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_checksum_ready:
  shows
    "st_checksum_ready (base_select_stack hart_index stack_top s) = st_checksum_ready s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_boot_ready:
  shows
    "st_boot_ready (base_select_stack hart_index stack_top s) = st_boot_ready s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_handoff_ready:
  shows
    "st_handoff_ready (base_select_stack hart_index stack_top s) = st_handoff_ready s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_secondary_seen:
  shows
    "st_secondary_seen (base_select_stack hart_index stack_top s) = st_secondary_seen s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_select_stack hart_index stack_top s) = st_secondary_wait_ready s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_select_stack_next:
  shows
    "st_next (base_select_stack hart_index stack_top s) = st_next s"
  by (simp add: base_select_stack_def)

lemma startup_frame_base_init_mscratch_hartid:
  shows
    "st_hartid (base_init_mscratch s) = st_hartid s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_dtb:
  shows
    "st_dtb (base_init_mscratch s) = st_dtb s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_mie:
  shows
    "st_mie (base_init_mscratch s) = st_mie s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_mscratch:
  shows
    "st_mscratch (base_init_mscratch s) = st_sp s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_satp:
  shows
    "st_satp (base_init_mscratch s) = st_satp s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_mstatus:
  shows
    "st_mstatus (base_init_mscratch s) = st_mstatus s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_sp:
  shows
    "st_sp (base_init_mscratch s) = st_sp s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_hart_index:
  shows
    "st_hart_index (base_init_mscratch s) = st_hart_index s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_boot_hartid:
  shows
    "st_boot_hartid (base_init_mscratch s) = st_boot_hartid s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_init_mscratch s) = st_boot_hart_mask s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_boot_dtb:
  shows
    "st_boot_dtb (base_init_mscratch s) = st_boot_dtb s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_boot_stack_top:
  shows
    "st_boot_stack_top (base_init_mscratch s) = st_sp s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_boot_next_addr:
  shows
    "st_boot_next_addr (base_init_mscratch s) = st_boot_next_addr s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_boot_magic:
  shows
    "st_boot_magic (base_init_mscratch s) = st_boot_magic s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_boot_flags:
  shows
    "st_boot_flags (base_init_mscratch s) = st_boot_flags s OR SBI_BOOT_FLAG_STACK_READY"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_text_span:
  shows
    "st_text_span (base_init_mscratch s) = st_text_span s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_stack_span:
  shows
    "st_stack_span (base_init_mscratch s) = st_stack_span s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_guard_span:
  shows
    "st_guard_span (base_init_mscratch s) = st_guard_span s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_bss_span:
  shows
    "st_bss_span (base_init_mscratch s) = st_bss_span s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_scratch_span:
  shows
    "st_scratch_span (base_init_mscratch s) = st_scratch_span s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_boot_checksum:
  shows
    "st_boot_checksum (base_init_mscratch s) = st_boot_checksum s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_bss_cleared:
  shows
    "st_bss_cleared (base_init_mscratch s) = st_bss_cleared s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_events_ready:
  shows
    "st_events_ready (base_init_mscratch s) = st_events_ready s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_init_mscratch s) = st_stack_guard_ready s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_scratch_ready:
  shows
    "st_scratch_ready (base_init_mscratch s) = st_scratch_ready s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_layout_ready:
  shows
    "st_layout_ready (base_init_mscratch s) = st_layout_ready s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_init_mscratch s) = st_csr_snapshot_ready s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_stack_valid:
  shows
    "st_stack_valid (base_init_mscratch s) = st_stack_valid s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_dtb_valid:
  shows
    "st_dtb_valid (base_init_mscratch s) = st_dtb_valid s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_checksum_ready:
  shows
    "st_checksum_ready (base_init_mscratch s) = st_checksum_ready s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_boot_ready:
  shows
    "st_boot_ready (base_init_mscratch s) = st_boot_ready s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_handoff_ready:
  shows
    "st_handoff_ready (base_init_mscratch s) = st_handoff_ready s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_secondary_seen:
  shows
    "st_secondary_seen (base_init_mscratch s) = st_secondary_seen s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_init_mscratch s) = st_secondary_wait_ready s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_init_mscratch_next:
  shows
    "st_next (base_init_mscratch s) = st_next s"
  by (simp add: base_init_mscratch_def)

lemma startup_frame_base_clear_bss_hartid:
  shows
    "st_hartid (base_clear_bss s) = st_hartid s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_dtb:
  shows
    "st_dtb (base_clear_bss s) = st_dtb s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_mie:
  shows
    "st_mie (base_clear_bss s) = st_mie s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_mscratch:
  shows
    "st_mscratch (base_clear_bss s) = st_mscratch s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_satp:
  shows
    "st_satp (base_clear_bss s) = st_satp s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_mstatus:
  shows
    "st_mstatus (base_clear_bss s) = st_mstatus s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_sp:
  shows
    "st_sp (base_clear_bss s) = st_sp s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_hart_index:
  shows
    "st_hart_index (base_clear_bss s) = st_hart_index s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_boot_hartid:
  shows
    "st_boot_hartid (base_clear_bss s) = st_boot_hartid s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_clear_bss s) = st_boot_hart_mask s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_boot_dtb:
  shows
    "st_boot_dtb (base_clear_bss s) = st_boot_dtb s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_boot_stack_top:
  shows
    "st_boot_stack_top (base_clear_bss s) = st_boot_stack_top s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_boot_next_addr:
  shows
    "st_boot_next_addr (base_clear_bss s) = st_boot_next_addr s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_boot_magic:
  shows
    "st_boot_magic (base_clear_bss s) = st_boot_magic s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_boot_flags:
  shows
    "st_boot_flags (base_clear_bss s) = st_boot_flags s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_text_span:
  shows
    "st_text_span (base_clear_bss s) = st_text_span s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_stack_span:
  shows
    "st_stack_span (base_clear_bss s) = st_stack_span s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_guard_span:
  shows
    "st_guard_span (base_clear_bss s) = st_guard_span s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_bss_span:
  shows
    "st_bss_span (base_clear_bss s) = st_bss_span s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_scratch_span:
  shows
    "st_scratch_span (base_clear_bss s) = st_scratch_span s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_boot_checksum:
  shows
    "st_boot_checksum (base_clear_bss s) = st_boot_checksum s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_bss_cleared:
  shows
    "st_bss_cleared (base_clear_bss s) = True"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_events_ready:
  shows
    "st_events_ready (base_clear_bss s) = st_events_ready s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_clear_bss s) = st_stack_guard_ready s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_scratch_ready:
  shows
    "st_scratch_ready (base_clear_bss s) = st_scratch_ready s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_layout_ready:
  shows
    "st_layout_ready (base_clear_bss s) = st_layout_ready s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_clear_bss s) = st_csr_snapshot_ready s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_stack_valid:
  shows
    "st_stack_valid (base_clear_bss s) = st_stack_valid s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_dtb_valid:
  shows
    "st_dtb_valid (base_clear_bss s) = st_dtb_valid s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_checksum_ready:
  shows
    "st_checksum_ready (base_clear_bss s) = st_checksum_ready s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_boot_ready:
  shows
    "st_boot_ready (base_clear_bss s) = st_boot_ready s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_handoff_ready:
  shows
    "st_handoff_ready (base_clear_bss s) = st_handoff_ready s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_secondary_seen:
  shows
    "st_secondary_seen (base_clear_bss s) = st_secondary_seen s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_clear_bss s) = st_secondary_wait_ready s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_clear_bss_next:
  shows
    "st_next (base_clear_bss s) = st_next s"
  by (simp add: base_clear_bss_def)

lemma startup_frame_base_reset_boot_records_hartid:
  shows
    "st_hartid (base_reset_boot_records s) = st_hartid s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_dtb:
  shows
    "st_dtb (base_reset_boot_records s) = st_dtb s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_mie:
  shows
    "st_mie (base_reset_boot_records s) = st_mie s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_mscratch:
  shows
    "st_mscratch (base_reset_boot_records s) = st_mscratch s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_satp:
  shows
    "st_satp (base_reset_boot_records s) = st_satp s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_mstatus:
  shows
    "st_mstatus (base_reset_boot_records s) = st_mstatus s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_sp:
  shows
    "st_sp (base_reset_boot_records s) = st_sp s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_hart_index:
  shows
    "st_hart_index (base_reset_boot_records s) = st_hart_index s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_boot_hartid:
  shows
    "st_boot_hartid (base_reset_boot_records s) = st_boot_hartid s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_reset_boot_records s) = st_boot_hart_mask s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_boot_dtb:
  shows
    "st_boot_dtb (base_reset_boot_records s) = st_boot_dtb s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_boot_stack_top:
  shows
    "st_boot_stack_top (base_reset_boot_records s) = st_boot_stack_top s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_boot_next_addr:
  shows
    "st_boot_next_addr (base_reset_boot_records s) = st_boot_next_addr s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_boot_magic:
  shows
    "st_boot_magic (base_reset_boot_records s) = st_boot_magic s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_boot_flags:
  shows
    "st_boot_flags (base_reset_boot_records s) = SBI_BOOT_FLAG_BSS_CLEARED"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_text_span:
  shows
    "st_text_span (base_reset_boot_records s) = st_text_span s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_stack_span:
  shows
    "st_stack_span (base_reset_boot_records s) = st_stack_span s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_guard_span:
  shows
    "st_guard_span (base_reset_boot_records s) = st_guard_span s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_bss_span:
  shows
    "st_bss_span (base_reset_boot_records s) = st_bss_span s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_scratch_span:
  shows
    "st_scratch_span (base_reset_boot_records s) = st_scratch_span s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_boot_checksum:
  shows
    "st_boot_checksum (base_reset_boot_records s) = st_boot_checksum s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_bss_cleared:
  shows
    "st_bss_cleared (base_reset_boot_records s) = st_bss_cleared s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_events_ready:
  shows
    "st_events_ready (base_reset_boot_records s) = False"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_reset_boot_records s) = st_stack_guard_ready s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_scratch_ready:
  shows
    "st_scratch_ready (base_reset_boot_records s) = False"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_layout_ready:
  shows
    "st_layout_ready (base_reset_boot_records s) = False"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_reset_boot_records s) = False"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_stack_valid:
  shows
    "st_stack_valid (base_reset_boot_records s) = st_stack_valid s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_dtb_valid:
  shows
    "st_dtb_valid (base_reset_boot_records s) = st_dtb_valid s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_checksum_ready:
  shows
    "st_checksum_ready (base_reset_boot_records s) = False"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_boot_ready:
  shows
    "st_boot_ready (base_reset_boot_records s) = False"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_handoff_ready:
  shows
    "st_handoff_ready (base_reset_boot_records s) = False"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_secondary_seen:
  shows
    "st_secondary_seen (base_reset_boot_records s) = st_secondary_seen s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_reset_boot_records s) = st_secondary_wait_ready s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_reset_boot_records_next:
  shows
    "st_next (base_reset_boot_records s) = st_next s"
  by (simp add: base_reset_boot_records_def)

lemma startup_frame_base_record_primary_hart_hartid:
  shows
    "st_hartid (base_record_primary_hart hart_mask s) = st_hartid s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_dtb:
  shows
    "st_dtb (base_record_primary_hart hart_mask s) = st_dtb s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_mie:
  shows
    "st_mie (base_record_primary_hart hart_mask s) = st_mie s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_mscratch:
  shows
    "st_mscratch (base_record_primary_hart hart_mask s) = st_mscratch s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_satp:
  shows
    "st_satp (base_record_primary_hart hart_mask s) = st_satp s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_mstatus:
  shows
    "st_mstatus (base_record_primary_hart hart_mask s) = st_mstatus s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_sp:
  shows
    "st_sp (base_record_primary_hart hart_mask s) = st_sp s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_hart_index:
  shows
    "st_hart_index (base_record_primary_hart hart_mask s) = st_hart_index s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_boot_hartid:
  shows
    "st_boot_hartid (base_record_primary_hart hart_mask s) = st_hartid s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_record_primary_hart hart_mask s) = hart_mask"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_boot_dtb:
  shows
    "st_boot_dtb (base_record_primary_hart hart_mask s) = st_dtb s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_boot_stack_top:
  shows
    "st_boot_stack_top (base_record_primary_hart hart_mask s) = st_boot_stack_top s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_boot_next_addr:
  shows
    "st_boot_next_addr (base_record_primary_hart hart_mask s) = st_boot_next_addr s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_boot_magic:
  shows
    "st_boot_magic (base_record_primary_hart hart_mask s) = st_boot_magic s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_boot_flags:
  shows
    "st_boot_flags (base_record_primary_hart hart_mask s) = st_boot_flags s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_text_span:
  shows
    "st_text_span (base_record_primary_hart hart_mask s) = st_text_span s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_stack_span:
  shows
    "st_stack_span (base_record_primary_hart hart_mask s) = st_stack_span s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_guard_span:
  shows
    "st_guard_span (base_record_primary_hart hart_mask s) = st_guard_span s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_bss_span:
  shows
    "st_bss_span (base_record_primary_hart hart_mask s) = st_bss_span s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_scratch_span:
  shows
    "st_scratch_span (base_record_primary_hart hart_mask s) = st_scratch_span s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_boot_checksum:
  shows
    "st_boot_checksum (base_record_primary_hart hart_mask s) = st_boot_checksum s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_bss_cleared:
  shows
    "st_bss_cleared (base_record_primary_hart hart_mask s) = st_bss_cleared s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_events_ready:
  shows
    "st_events_ready (base_record_primary_hart hart_mask s) = st_events_ready s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_record_primary_hart hart_mask s) = st_stack_guard_ready s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_scratch_ready:
  shows
    "st_scratch_ready (base_record_primary_hart hart_mask s) = st_scratch_ready s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_layout_ready:
  shows
    "st_layout_ready (base_record_primary_hart hart_mask s) = st_layout_ready s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_record_primary_hart hart_mask s) = st_csr_snapshot_ready s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_stack_valid:
  shows
    "st_stack_valid (base_record_primary_hart hart_mask s) = st_stack_valid s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_dtb_valid:
  shows
    "st_dtb_valid (base_record_primary_hart hart_mask s) = st_dtb_valid s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_checksum_ready:
  shows
    "st_checksum_ready (base_record_primary_hart hart_mask s) = st_checksum_ready s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_boot_ready:
  shows
    "st_boot_ready (base_record_primary_hart hart_mask s) = st_boot_ready s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_handoff_ready:
  shows
    "st_handoff_ready (base_record_primary_hart hart_mask s) = st_handoff_ready s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_secondary_seen:
  shows
    "st_secondary_seen (base_record_primary_hart hart_mask s) = st_secondary_seen s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_record_primary_hart hart_mask s) = st_secondary_wait_ready s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_record_primary_hart_next:
  shows
    "st_next (base_record_primary_hart hart_mask s) = st_next s"
  by (simp add: base_record_primary_hart_def)

lemma startup_frame_base_append_event_hartid:
  shows
    "st_hartid (base_append_event s) = st_hartid s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_dtb:
  shows
    "st_dtb (base_append_event s) = st_dtb s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_mie:
  shows
    "st_mie (base_append_event s) = st_mie s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_mscratch:
  shows
    "st_mscratch (base_append_event s) = st_mscratch s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_satp:
  shows
    "st_satp (base_append_event s) = st_satp s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_mstatus:
  shows
    "st_mstatus (base_append_event s) = st_mstatus s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_sp:
  shows
    "st_sp (base_append_event s) = st_sp s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_hart_index:
  shows
    "st_hart_index (base_append_event s) = st_hart_index s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_boot_hartid:
  shows
    "st_boot_hartid (base_append_event s) = st_boot_hartid s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_append_event s) = st_boot_hart_mask s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_boot_dtb:
  shows
    "st_boot_dtb (base_append_event s) = st_boot_dtb s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_boot_stack_top:
  shows
    "st_boot_stack_top (base_append_event s) = st_boot_stack_top s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_boot_next_addr:
  shows
    "st_boot_next_addr (base_append_event s) = st_boot_next_addr s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_boot_magic:
  shows
    "st_boot_magic (base_append_event s) = st_boot_magic s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_boot_flags:
  shows
    "st_boot_flags (base_append_event s) = st_boot_flags s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_text_span:
  shows
    "st_text_span (base_append_event s) = st_text_span s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_stack_span:
  shows
    "st_stack_span (base_append_event s) = st_stack_span s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_guard_span:
  shows
    "st_guard_span (base_append_event s) = st_guard_span s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_bss_span:
  shows
    "st_bss_span (base_append_event s) = st_bss_span s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_scratch_span:
  shows
    "st_scratch_span (base_append_event s) = st_scratch_span s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_boot_checksum:
  shows
    "st_boot_checksum (base_append_event s) = st_boot_checksum s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_bss_cleared:
  shows
    "st_bss_cleared (base_append_event s) = st_bss_cleared s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_events_ready:
  shows
    "st_events_ready (base_append_event s) = True"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_append_event s) = st_stack_guard_ready s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_scratch_ready:
  shows
    "st_scratch_ready (base_append_event s) = st_scratch_ready s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_layout_ready:
  shows
    "st_layout_ready (base_append_event s) = st_layout_ready s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_append_event s) = st_csr_snapshot_ready s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_stack_valid:
  shows
    "st_stack_valid (base_append_event s) = st_stack_valid s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_dtb_valid:
  shows
    "st_dtb_valid (base_append_event s) = st_dtb_valid s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_checksum_ready:
  shows
    "st_checksum_ready (base_append_event s) = st_checksum_ready s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_boot_ready:
  shows
    "st_boot_ready (base_append_event s) = st_boot_ready s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_handoff_ready:
  shows
    "st_handoff_ready (base_append_event s) = st_handoff_ready s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_secondary_seen:
  shows
    "st_secondary_seen (base_append_event s) = st_secondary_seen s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_append_event s) = st_secondary_wait_ready s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_append_event_next:
  shows
    "st_next (base_append_event s) = st_next s"
  by (simp add: base_append_event_def)

lemma startup_frame_base_init_stack_guard_hartid:
  shows
    "st_hartid (base_init_stack_guard s) = st_hartid s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_dtb:
  shows
    "st_dtb (base_init_stack_guard s) = st_dtb s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_mie:
  shows
    "st_mie (base_init_stack_guard s) = st_mie s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_mscratch:
  shows
    "st_mscratch (base_init_stack_guard s) = st_mscratch s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_satp:
  shows
    "st_satp (base_init_stack_guard s) = st_satp s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_mstatus:
  shows
    "st_mstatus (base_init_stack_guard s) = st_mstatus s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_sp:
  shows
    "st_sp (base_init_stack_guard s) = st_sp s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_hart_index:
  shows
    "st_hart_index (base_init_stack_guard s) = st_hart_index s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_boot_hartid:
  shows
    "st_boot_hartid (base_init_stack_guard s) = st_boot_hartid s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_init_stack_guard s) = st_boot_hart_mask s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_boot_dtb:
  shows
    "st_boot_dtb (base_init_stack_guard s) = st_boot_dtb s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_boot_stack_top:
  shows
    "st_boot_stack_top (base_init_stack_guard s) = st_boot_stack_top s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_boot_next_addr:
  shows
    "st_boot_next_addr (base_init_stack_guard s) = st_boot_next_addr s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_boot_magic:
  shows
    "st_boot_magic (base_init_stack_guard s) = st_boot_magic s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_boot_flags:
  shows
    "st_boot_flags (base_init_stack_guard s) = st_boot_flags s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_text_span:
  shows
    "st_text_span (base_init_stack_guard s) = st_text_span s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_stack_span:
  shows
    "st_stack_span (base_init_stack_guard s) = st_stack_span s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_guard_span:
  shows
    "st_guard_span (base_init_stack_guard s) = st_guard_span s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_bss_span:
  shows
    "st_bss_span (base_init_stack_guard s) = st_bss_span s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_scratch_span:
  shows
    "st_scratch_span (base_init_stack_guard s) = st_scratch_span s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_boot_checksum:
  shows
    "st_boot_checksum (base_init_stack_guard s) = st_boot_checksum s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_bss_cleared:
  shows
    "st_bss_cleared (base_init_stack_guard s) = st_bss_cleared s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_events_ready:
  shows
    "st_events_ready (base_init_stack_guard s) = st_events_ready s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_init_stack_guard s) = True"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_scratch_ready:
  shows
    "st_scratch_ready (base_init_stack_guard s) = st_scratch_ready s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_layout_ready:
  shows
    "st_layout_ready (base_init_stack_guard s) = st_layout_ready s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_init_stack_guard s) = st_csr_snapshot_ready s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_stack_valid:
  shows
    "st_stack_valid (base_init_stack_guard s) = st_stack_valid s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_dtb_valid:
  shows
    "st_dtb_valid (base_init_stack_guard s) = st_dtb_valid s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_checksum_ready:
  shows
    "st_checksum_ready (base_init_stack_guard s) = st_checksum_ready s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_boot_ready:
  shows
    "st_boot_ready (base_init_stack_guard s) = st_boot_ready s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_handoff_ready:
  shows
    "st_handoff_ready (base_init_stack_guard s) = st_handoff_ready s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_secondary_seen:
  shows
    "st_secondary_seen (base_init_stack_guard s) = st_secondary_seen s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_init_stack_guard s) = st_secondary_wait_ready s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_stack_guard_next:
  shows
    "st_next (base_init_stack_guard s) = st_next s"
  by (simp add: base_init_stack_guard_def)

lemma startup_frame_base_init_hart_scratch_hartid:
  shows
    "st_hartid (base_init_hart_scratch s) = st_hartid s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_dtb:
  shows
    "st_dtb (base_init_hart_scratch s) = st_dtb s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_mie:
  shows
    "st_mie (base_init_hart_scratch s) = st_mie s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_mscratch:
  shows
    "st_mscratch (base_init_hart_scratch s) = st_mscratch s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_satp:
  shows
    "st_satp (base_init_hart_scratch s) = st_satp s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_mstatus:
  shows
    "st_mstatus (base_init_hart_scratch s) = st_mstatus s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_sp:
  shows
    "st_sp (base_init_hart_scratch s) = st_sp s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_hart_index:
  shows
    "st_hart_index (base_init_hart_scratch s) = st_hart_index s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_boot_hartid:
  shows
    "st_boot_hartid (base_init_hart_scratch s) = st_boot_hartid s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_init_hart_scratch s) = st_boot_hart_mask s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_boot_dtb:
  shows
    "st_boot_dtb (base_init_hart_scratch s) = st_boot_dtb s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_boot_stack_top:
  shows
    "st_boot_stack_top (base_init_hart_scratch s) = st_boot_stack_top s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_boot_next_addr:
  shows
    "st_boot_next_addr (base_init_hart_scratch s) = st_boot_next_addr s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_boot_magic:
  shows
    "st_boot_magic (base_init_hart_scratch s) = st_boot_magic s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_boot_flags:
  shows
    "st_boot_flags (base_init_hart_scratch s) = st_boot_flags s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_text_span:
  shows
    "st_text_span (base_init_hart_scratch s) = st_text_span s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_stack_span:
  shows
    "st_stack_span (base_init_hart_scratch s) = st_stack_span s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_guard_span:
  shows
    "st_guard_span (base_init_hart_scratch s) = st_guard_span s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_bss_span:
  shows
    "st_bss_span (base_init_hart_scratch s) = st_bss_span s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_scratch_span:
  shows
    "st_scratch_span (base_init_hart_scratch s) = st_scratch_span s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_boot_checksum:
  shows
    "st_boot_checksum (base_init_hart_scratch s) = st_boot_checksum s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_bss_cleared:
  shows
    "st_bss_cleared (base_init_hart_scratch s) = st_bss_cleared s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_events_ready:
  shows
    "st_events_ready (base_init_hart_scratch s) = st_events_ready s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_init_hart_scratch s) = st_stack_guard_ready s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_scratch_ready:
  shows
    "st_scratch_ready (base_init_hart_scratch s) = True"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_layout_ready:
  shows
    "st_layout_ready (base_init_hart_scratch s) = st_layout_ready s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_init_hart_scratch s) = st_csr_snapshot_ready s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_stack_valid:
  shows
    "st_stack_valid (base_init_hart_scratch s) = st_stack_valid s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_dtb_valid:
  shows
    "st_dtb_valid (base_init_hart_scratch s) = st_dtb_valid s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_checksum_ready:
  shows
    "st_checksum_ready (base_init_hart_scratch s) = st_checksum_ready s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_boot_ready:
  shows
    "st_boot_ready (base_init_hart_scratch s) = st_boot_ready s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_handoff_ready:
  shows
    "st_handoff_ready (base_init_hart_scratch s) = st_handoff_ready s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_secondary_seen:
  shows
    "st_secondary_seen (base_init_hart_scratch s) = st_secondary_seen s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_init_hart_scratch s) = st_secondary_wait_ready s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_init_hart_scratch_next:
  shows
    "st_next (base_init_hart_scratch s) = st_next s"
  by (simp add: base_init_hart_scratch_def)

lemma startup_frame_base_record_memory_layout_hartid:
  shows
    "st_hartid (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_hartid s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_dtb:
  shows
    "st_dtb (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_dtb s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_mie:
  shows
    "st_mie (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_mie s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_mscratch:
  shows
    "st_mscratch (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_mscratch s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_satp:
  shows
    "st_satp (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_satp s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_mstatus:
  shows
    "st_mstatus (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_mstatus s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_sp:
  shows
    "st_sp (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_sp s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_hart_index:
  shows
    "st_hart_index (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_hart_index s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_boot_hartid:
  shows
    "st_boot_hartid (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_boot_hartid s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_boot_hart_mask s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_boot_dtb:
  shows
    "st_boot_dtb (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_boot_dtb s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_boot_stack_top:
  shows
    "st_boot_stack_top (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_boot_stack_top s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_boot_next_addr:
  shows
    "st_boot_next_addr (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_boot_next_addr s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_boot_magic:
  shows
    "st_boot_magic (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_boot_magic s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_boot_flags:
  shows
    "st_boot_flags (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_boot_flags s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_text_span:
  shows
    "st_text_span (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = text_span"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_stack_span:
  shows
    "st_stack_span (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = stack_span"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_guard_span:
  shows
    "st_guard_span (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = guard_span"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_bss_span:
  shows
    "st_bss_span (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = bss_span"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_scratch_span:
  shows
    "st_scratch_span (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = scratch_span"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_boot_checksum:
  shows
    "st_boot_checksum (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_boot_checksum s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_bss_cleared:
  shows
    "st_bss_cleared (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_bss_cleared s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_events_ready:
  shows
    "st_events_ready (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_events_ready s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_stack_guard_ready s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_scratch_ready:
  shows
    "st_scratch_ready (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_scratch_ready s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_layout_ready:
  shows
    "st_layout_ready (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = True"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_csr_snapshot_ready s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_stack_valid:
  shows
    "st_stack_valid (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_stack_valid s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_dtb_valid:
  shows
    "st_dtb_valid (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_dtb_valid s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_checksum_ready:
  shows
    "st_checksum_ready (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_checksum_ready s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_boot_ready:
  shows
    "st_boot_ready (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_boot_ready s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_handoff_ready:
  shows
    "st_handoff_ready (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_handoff_ready s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_secondary_seen:
  shows
    "st_secondary_seen (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_secondary_seen s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_secondary_wait_ready s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_memory_layout_next:
  shows
    "st_next (base_record_memory_layout text_span stack_span guard_span bss_span scratch_span s) = st_next s"
  by (simp add: base_record_memory_layout_def)

lemma startup_frame_base_record_csr_snapshot_hartid:
  shows
    "st_hartid (base_record_csr_snapshot s) = st_hartid s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_dtb:
  shows
    "st_dtb (base_record_csr_snapshot s) = st_dtb s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_mie:
  shows
    "st_mie (base_record_csr_snapshot s) = st_mie s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_mscratch:
  shows
    "st_mscratch (base_record_csr_snapshot s) = st_mscratch s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_satp:
  shows
    "st_satp (base_record_csr_snapshot s) = st_satp s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_mstatus:
  shows
    "st_mstatus (base_record_csr_snapshot s) = st_mstatus s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_sp:
  shows
    "st_sp (base_record_csr_snapshot s) = st_sp s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_hart_index:
  shows
    "st_hart_index (base_record_csr_snapshot s) = st_hart_index s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_boot_hartid:
  shows
    "st_boot_hartid (base_record_csr_snapshot s) = st_boot_hartid s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_record_csr_snapshot s) = st_boot_hart_mask s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_boot_dtb:
  shows
    "st_boot_dtb (base_record_csr_snapshot s) = st_boot_dtb s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_boot_stack_top:
  shows
    "st_boot_stack_top (base_record_csr_snapshot s) = st_boot_stack_top s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_boot_next_addr:
  shows
    "st_boot_next_addr (base_record_csr_snapshot s) = st_boot_next_addr s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_boot_magic:
  shows
    "st_boot_magic (base_record_csr_snapshot s) = st_boot_magic s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_boot_flags:
  shows
    "st_boot_flags (base_record_csr_snapshot s) = st_boot_flags s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_text_span:
  shows
    "st_text_span (base_record_csr_snapshot s) = st_text_span s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_stack_span:
  shows
    "st_stack_span (base_record_csr_snapshot s) = st_stack_span s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_guard_span:
  shows
    "st_guard_span (base_record_csr_snapshot s) = st_guard_span s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_bss_span:
  shows
    "st_bss_span (base_record_csr_snapshot s) = st_bss_span s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_scratch_span:
  shows
    "st_scratch_span (base_record_csr_snapshot s) = st_scratch_span s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_boot_checksum:
  shows
    "st_boot_checksum (base_record_csr_snapshot s) = st_boot_checksum s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_bss_cleared:
  shows
    "st_bss_cleared (base_record_csr_snapshot s) = st_bss_cleared s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_events_ready:
  shows
    "st_events_ready (base_record_csr_snapshot s) = st_events_ready s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_record_csr_snapshot s) = st_stack_guard_ready s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_scratch_ready:
  shows
    "st_scratch_ready (base_record_csr_snapshot s) = st_scratch_ready s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_layout_ready:
  shows
    "st_layout_ready (base_record_csr_snapshot s) = st_layout_ready s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_record_csr_snapshot s) = True"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_stack_valid:
  shows
    "st_stack_valid (base_record_csr_snapshot s) = st_stack_valid s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_dtb_valid:
  shows
    "st_dtb_valid (base_record_csr_snapshot s) = st_dtb_valid s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_checksum_ready:
  shows
    "st_checksum_ready (base_record_csr_snapshot s) = st_checksum_ready s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_boot_ready:
  shows
    "st_boot_ready (base_record_csr_snapshot s) = st_boot_ready s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_handoff_ready:
  shows
    "st_handoff_ready (base_record_csr_snapshot s) = st_handoff_ready s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_secondary_seen:
  shows
    "st_secondary_seen (base_record_csr_snapshot s) = st_secondary_seen s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_record_csr_snapshot s) = st_secondary_wait_ready s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_record_csr_snapshot_next:
  shows
    "st_next (base_record_csr_snapshot s) = st_next s"
  by (simp add: base_record_csr_snapshot_def)

lemma startup_frame_base_validate_stack_hartid:
  shows
    "st_hartid (base_validate_stack stack_ok s) = st_hartid s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_dtb:
  shows
    "st_dtb (base_validate_stack stack_ok s) = st_dtb s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_mie:
  shows
    "st_mie (base_validate_stack stack_ok s) = st_mie s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_mscratch:
  shows
    "st_mscratch (base_validate_stack stack_ok s) = st_mscratch s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_satp:
  shows
    "st_satp (base_validate_stack stack_ok s) = st_satp s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_mstatus:
  shows
    "st_mstatus (base_validate_stack stack_ok s) = st_mstatus s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_sp:
  shows
    "st_sp (base_validate_stack stack_ok s) = st_sp s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_hart_index:
  shows
    "st_hart_index (base_validate_stack stack_ok s) = st_hart_index s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_boot_hartid:
  shows
    "st_boot_hartid (base_validate_stack stack_ok s) = st_boot_hartid s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_validate_stack stack_ok s) = st_boot_hart_mask s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_boot_dtb:
  shows
    "st_boot_dtb (base_validate_stack stack_ok s) = st_boot_dtb s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_boot_stack_top:
  shows
    "st_boot_stack_top (base_validate_stack stack_ok s) = st_boot_stack_top s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_boot_next_addr:
  shows
    "st_boot_next_addr (base_validate_stack stack_ok s) = st_boot_next_addr s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_boot_magic:
  shows
    "st_boot_magic (base_validate_stack stack_ok s) = st_boot_magic s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_boot_flags:
  shows
    "st_boot_flags (base_validate_stack stack_ok s) = st_boot_flags s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_text_span:
  shows
    "st_text_span (base_validate_stack stack_ok s) = st_text_span s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_stack_span:
  shows
    "st_stack_span (base_validate_stack stack_ok s) = st_stack_span s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_guard_span:
  shows
    "st_guard_span (base_validate_stack stack_ok s) = st_guard_span s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_bss_span:
  shows
    "st_bss_span (base_validate_stack stack_ok s) = st_bss_span s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_scratch_span:
  shows
    "st_scratch_span (base_validate_stack stack_ok s) = st_scratch_span s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_boot_checksum:
  shows
    "st_boot_checksum (base_validate_stack stack_ok s) = st_boot_checksum s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_bss_cleared:
  shows
    "st_bss_cleared (base_validate_stack stack_ok s) = st_bss_cleared s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_events_ready:
  shows
    "st_events_ready (base_validate_stack stack_ok s) = st_events_ready s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_validate_stack stack_ok s) = st_stack_guard_ready s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_scratch_ready:
  shows
    "st_scratch_ready (base_validate_stack stack_ok s) = st_scratch_ready s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_layout_ready:
  shows
    "st_layout_ready (base_validate_stack stack_ok s) = st_layout_ready s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_validate_stack stack_ok s) = st_csr_snapshot_ready s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_stack_valid:
  shows
    "st_stack_valid (base_validate_stack stack_ok s) = stack_ok"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_dtb_valid:
  shows
    "st_dtb_valid (base_validate_stack stack_ok s) = st_dtb_valid s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_checksum_ready:
  shows
    "st_checksum_ready (base_validate_stack stack_ok s) = st_checksum_ready s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_boot_ready:
  shows
    "st_boot_ready (base_validate_stack stack_ok s) = st_boot_ready s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_handoff_ready:
  shows
    "st_handoff_ready (base_validate_stack stack_ok s) = st_handoff_ready s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_secondary_seen:
  shows
    "st_secondary_seen (base_validate_stack stack_ok s) = st_secondary_seen s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_validate_stack stack_ok s) = st_secondary_wait_ready s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_stack_next:
  shows
    "st_next (base_validate_stack stack_ok s) = st_next s"
  by (simp add: base_validate_stack_def)

lemma startup_frame_base_validate_dtb_hartid:
  shows
    "st_hartid (base_validate_dtb dtb_ok s) = st_hartid s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_dtb:
  shows
    "st_dtb (base_validate_dtb dtb_ok s) = st_dtb s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_mie:
  shows
    "st_mie (base_validate_dtb dtb_ok s) = st_mie s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_mscratch:
  shows
    "st_mscratch (base_validate_dtb dtb_ok s) = st_mscratch s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_satp:
  shows
    "st_satp (base_validate_dtb dtb_ok s) = st_satp s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_mstatus:
  shows
    "st_mstatus (base_validate_dtb dtb_ok s) = st_mstatus s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_sp:
  shows
    "st_sp (base_validate_dtb dtb_ok s) = st_sp s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_hart_index:
  shows
    "st_hart_index (base_validate_dtb dtb_ok s) = st_hart_index s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_boot_hartid:
  shows
    "st_boot_hartid (base_validate_dtb dtb_ok s) = st_boot_hartid s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_validate_dtb dtb_ok s) = st_boot_hart_mask s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_boot_dtb:
  shows
    "st_boot_dtb (base_validate_dtb dtb_ok s) = st_boot_dtb s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_boot_stack_top:
  shows
    "st_boot_stack_top (base_validate_dtb dtb_ok s) = st_boot_stack_top s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_boot_next_addr:
  shows
    "st_boot_next_addr (base_validate_dtb dtb_ok s) = st_boot_next_addr s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_boot_magic:
  shows
    "st_boot_magic (base_validate_dtb dtb_ok s) = st_boot_magic s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_boot_flags:
  shows
    "st_boot_flags (base_validate_dtb dtb_ok s) = st_boot_flags s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_text_span:
  shows
    "st_text_span (base_validate_dtb dtb_ok s) = st_text_span s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_stack_span:
  shows
    "st_stack_span (base_validate_dtb dtb_ok s) = st_stack_span s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_guard_span:
  shows
    "st_guard_span (base_validate_dtb dtb_ok s) = st_guard_span s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_bss_span:
  shows
    "st_bss_span (base_validate_dtb dtb_ok s) = st_bss_span s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_scratch_span:
  shows
    "st_scratch_span (base_validate_dtb dtb_ok s) = st_scratch_span s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_boot_checksum:
  shows
    "st_boot_checksum (base_validate_dtb dtb_ok s) = st_boot_checksum s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_bss_cleared:
  shows
    "st_bss_cleared (base_validate_dtb dtb_ok s) = st_bss_cleared s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_events_ready:
  shows
    "st_events_ready (base_validate_dtb dtb_ok s) = st_events_ready s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_validate_dtb dtb_ok s) = st_stack_guard_ready s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_scratch_ready:
  shows
    "st_scratch_ready (base_validate_dtb dtb_ok s) = st_scratch_ready s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_layout_ready:
  shows
    "st_layout_ready (base_validate_dtb dtb_ok s) = st_layout_ready s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_validate_dtb dtb_ok s) = st_csr_snapshot_ready s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_stack_valid:
  shows
    "st_stack_valid (base_validate_dtb dtb_ok s) = st_stack_valid s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_dtb_valid:
  shows
    "st_dtb_valid (base_validate_dtb dtb_ok s) = dtb_ok"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_checksum_ready:
  shows
    "st_checksum_ready (base_validate_dtb dtb_ok s) = st_checksum_ready s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_boot_ready:
  shows
    "st_boot_ready (base_validate_dtb dtb_ok s) = st_boot_ready s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_handoff_ready:
  shows
    "st_handoff_ready (base_validate_dtb dtb_ok s) = st_handoff_ready s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_secondary_seen:
  shows
    "st_secondary_seen (base_validate_dtb dtb_ok s) = st_secondary_seen s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_validate_dtb dtb_ok s) = st_secondary_wait_ready s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_validate_dtb_next:
  shows
    "st_next (base_validate_dtb dtb_ok s) = st_next s"
  by (simp add: base_validate_dtb_def)

lemma startup_frame_base_save_boot_state_hartid:
  shows
    "st_hartid (base_save_boot_state s) = st_hartid s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_dtb:
  shows
    "st_dtb (base_save_boot_state s) = st_dtb s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_mie:
  shows
    "st_mie (base_save_boot_state s) = st_mie s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_mscratch:
  shows
    "st_mscratch (base_save_boot_state s) = st_mscratch s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_satp:
  shows
    "st_satp (base_save_boot_state s) = st_satp s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_mstatus:
  shows
    "st_mstatus (base_save_boot_state s) = st_mstatus s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_sp:
  shows
    "st_sp (base_save_boot_state s) = st_sp s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_hart_index:
  shows
    "st_hart_index (base_save_boot_state s) = st_hart_index s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_boot_hartid:
  shows
    "st_boot_hartid (base_save_boot_state s) = st_hartid s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_save_boot_state s) = st_boot_hart_mask s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_boot_dtb:
  shows
    "st_boot_dtb (base_save_boot_state s) = st_dtb s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_boot_stack_top:
  shows
    "st_boot_stack_top (base_save_boot_state s) = st_sp s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_boot_next_addr:
  shows
    "st_boot_next_addr (base_save_boot_state s) = FW_JUMP_ADDR"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_boot_magic:
  shows
    "st_boot_magic (base_save_boot_state s) = SBI_BOOT_SCRATCH_MAGIC"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_boot_flags:
  shows
    "st_boot_flags (base_save_boot_state s) = cold_boot_flags (st_dtb s)"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_text_span:
  shows
    "st_text_span (base_save_boot_state s) = st_text_span s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_stack_span:
  shows
    "st_stack_span (base_save_boot_state s) = st_stack_span s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_guard_span:
  shows
    "st_guard_span (base_save_boot_state s) = st_guard_span s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_bss_span:
  shows
    "st_bss_span (base_save_boot_state s) = st_bss_span s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_scratch_span:
  shows
    "st_scratch_span (base_save_boot_state s) = st_scratch_span s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_boot_checksum:
  shows
    "st_boot_checksum (base_save_boot_state s) = st_boot_checksum s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_bss_cleared:
  shows
    "st_bss_cleared (base_save_boot_state s) = st_bss_cleared s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_events_ready:
  shows
    "st_events_ready (base_save_boot_state s) = st_events_ready s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_save_boot_state s) = st_stack_guard_ready s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_scratch_ready:
  shows
    "st_scratch_ready (base_save_boot_state s) = st_scratch_ready s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_layout_ready:
  shows
    "st_layout_ready (base_save_boot_state s) = st_layout_ready s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_save_boot_state s) = st_csr_snapshot_ready s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_stack_valid:
  shows
    "st_stack_valid (base_save_boot_state s) = st_stack_valid s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_dtb_valid:
  shows
    "st_dtb_valid (base_save_boot_state s) = st_dtb_valid s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_checksum_ready:
  shows
    "st_checksum_ready (base_save_boot_state s) = st_checksum_ready s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_boot_ready:
  shows
    "st_boot_ready (base_save_boot_state s) = st_boot_ready s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_handoff_ready:
  shows
    "st_handoff_ready (base_save_boot_state s) = st_handoff_ready s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_secondary_seen:
  shows
    "st_secondary_seen (base_save_boot_state s) = st_secondary_seen s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_save_boot_state s) = st_secondary_wait_ready s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_save_boot_state_next:
  shows
    "st_next (base_save_boot_state s) = st_next s"
  by (simp add: base_save_boot_state_def)

lemma startup_frame_base_compute_boot_checksum_hartid:
  shows
    "st_hartid (base_compute_boot_checksum checksum s) = st_hartid s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_dtb:
  shows
    "st_dtb (base_compute_boot_checksum checksum s) = st_dtb s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_mie:
  shows
    "st_mie (base_compute_boot_checksum checksum s) = st_mie s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_mscratch:
  shows
    "st_mscratch (base_compute_boot_checksum checksum s) = st_mscratch s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_satp:
  shows
    "st_satp (base_compute_boot_checksum checksum s) = st_satp s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_mstatus:
  shows
    "st_mstatus (base_compute_boot_checksum checksum s) = st_mstatus s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_sp:
  shows
    "st_sp (base_compute_boot_checksum checksum s) = st_sp s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_hart_index:
  shows
    "st_hart_index (base_compute_boot_checksum checksum s) = st_hart_index s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_boot_hartid:
  shows
    "st_boot_hartid (base_compute_boot_checksum checksum s) = st_boot_hartid s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_compute_boot_checksum checksum s) = st_boot_hart_mask s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_boot_dtb:
  shows
    "st_boot_dtb (base_compute_boot_checksum checksum s) = st_boot_dtb s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_boot_stack_top:
  shows
    "st_boot_stack_top (base_compute_boot_checksum checksum s) = st_boot_stack_top s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_boot_next_addr:
  shows
    "st_boot_next_addr (base_compute_boot_checksum checksum s) = st_boot_next_addr s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_boot_magic:
  shows
    "st_boot_magic (base_compute_boot_checksum checksum s) = st_boot_magic s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_boot_flags:
  shows
    "st_boot_flags (base_compute_boot_checksum checksum s) = st_boot_flags s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_text_span:
  shows
    "st_text_span (base_compute_boot_checksum checksum s) = st_text_span s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_stack_span:
  shows
    "st_stack_span (base_compute_boot_checksum checksum s) = st_stack_span s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_guard_span:
  shows
    "st_guard_span (base_compute_boot_checksum checksum s) = st_guard_span s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_bss_span:
  shows
    "st_bss_span (base_compute_boot_checksum checksum s) = st_bss_span s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_scratch_span:
  shows
    "st_scratch_span (base_compute_boot_checksum checksum s) = st_scratch_span s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_boot_checksum:
  shows
    "st_boot_checksum (base_compute_boot_checksum checksum s) = checksum"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_bss_cleared:
  shows
    "st_bss_cleared (base_compute_boot_checksum checksum s) = st_bss_cleared s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_events_ready:
  shows
    "st_events_ready (base_compute_boot_checksum checksum s) = st_events_ready s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_compute_boot_checksum checksum s) = st_stack_guard_ready s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_scratch_ready:
  shows
    "st_scratch_ready (base_compute_boot_checksum checksum s) = st_scratch_ready s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_layout_ready:
  shows
    "st_layout_ready (base_compute_boot_checksum checksum s) = st_layout_ready s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_compute_boot_checksum checksum s) = st_csr_snapshot_ready s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_stack_valid:
  shows
    "st_stack_valid (base_compute_boot_checksum checksum s) = st_stack_valid s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_dtb_valid:
  shows
    "st_dtb_valid (base_compute_boot_checksum checksum s) = st_dtb_valid s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_checksum_ready:
  shows
    "st_checksum_ready (base_compute_boot_checksum checksum s) = True"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_boot_ready:
  shows
    "st_boot_ready (base_compute_boot_checksum checksum s) = st_boot_ready s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_handoff_ready:
  shows
    "st_handoff_ready (base_compute_boot_checksum checksum s) = st_handoff_ready s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_secondary_seen:
  shows
    "st_secondary_seen (base_compute_boot_checksum checksum s) = st_secondary_seen s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_compute_boot_checksum checksum s) = st_secondary_wait_ready s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_compute_boot_checksum_next:
  shows
    "st_next (base_compute_boot_checksum checksum s) = st_next s"
  by (simp add: base_compute_boot_checksum_def)

lemma startup_frame_base_init_boot_state_hartid:
  shows
    "st_hartid (base_init_boot_state s) = st_hartid s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_dtb:
  shows
    "st_dtb (base_init_boot_state s) = st_dtb s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_mie:
  shows
    "st_mie (base_init_boot_state s) = 0"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_mscratch:
  shows
    "st_mscratch (base_init_boot_state s) = st_mscratch s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_satp:
  shows
    "st_satp (base_init_boot_state s) = st_satp s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_mstatus:
  shows
    "st_mstatus (base_init_boot_state s) = st_mstatus s AND NOT MSTATUS_MPP"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_sp:
  shows
    "st_sp (base_init_boot_state s) = st_sp s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_hart_index:
  shows
    "st_hart_index (base_init_boot_state s) = st_hart_index s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_boot_hartid:
  shows
    "st_boot_hartid (base_init_boot_state s) = st_boot_hartid s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_init_boot_state s) = st_boot_hart_mask s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_boot_dtb:
  shows
    "st_boot_dtb (base_init_boot_state s) = st_boot_dtb s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_boot_stack_top:
  shows
    "st_boot_stack_top (base_init_boot_state s) = st_boot_stack_top s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_boot_next_addr:
  shows
    "st_boot_next_addr (base_init_boot_state s) = st_boot_next_addr s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_boot_magic:
  shows
    "st_boot_magic (base_init_boot_state s) = st_boot_magic s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_boot_flags:
  shows
    "st_boot_flags (base_init_boot_state s) = st_boot_flags s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_text_span:
  shows
    "st_text_span (base_init_boot_state s) = st_text_span s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_stack_span:
  shows
    "st_stack_span (base_init_boot_state s) = st_stack_span s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_guard_span:
  shows
    "st_guard_span (base_init_boot_state s) = st_guard_span s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_bss_span:
  shows
    "st_bss_span (base_init_boot_state s) = st_bss_span s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_scratch_span:
  shows
    "st_scratch_span (base_init_boot_state s) = st_scratch_span s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_boot_checksum:
  shows
    "st_boot_checksum (base_init_boot_state s) = st_boot_checksum s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_bss_cleared:
  shows
    "st_bss_cleared (base_init_boot_state s) = st_bss_cleared s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_events_ready:
  shows
    "st_events_ready (base_init_boot_state s) = st_events_ready s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_init_boot_state s) = st_stack_guard_ready s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_scratch_ready:
  shows
    "st_scratch_ready (base_init_boot_state s) = st_scratch_ready s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_layout_ready:
  shows
    "st_layout_ready (base_init_boot_state s) = st_layout_ready s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_init_boot_state s) = st_csr_snapshot_ready s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_stack_valid:
  shows
    "st_stack_valid (base_init_boot_state s) = st_stack_valid s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_dtb_valid:
  shows
    "st_dtb_valid (base_init_boot_state s) = st_dtb_valid s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_checksum_ready:
  shows
    "st_checksum_ready (base_init_boot_state s) = st_checksum_ready s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_boot_ready:
  shows
    "st_boot_ready (base_init_boot_state s) = st_boot_ready s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_handoff_ready:
  shows
    "st_handoff_ready (base_init_boot_state s) = st_handoff_ready s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_secondary_seen:
  shows
    "st_secondary_seen (base_init_boot_state s) = st_secondary_seen s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_init_boot_state s) = st_secondary_wait_ready s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_init_boot_state_next:
  shows
    "st_next (base_init_boot_state s) = st_next s"
  by (simp add: base_init_boot_state_def)

lemma startup_frame_base_finalize_boot_state_hartid:
  shows
    "st_hartid (base_finalize_boot_state s) = st_hartid s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_dtb:
  shows
    "st_dtb (base_finalize_boot_state s) = st_dtb s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_mie:
  shows
    "st_mie (base_finalize_boot_state s) = st_mie s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_mscratch:
  shows
    "st_mscratch (base_finalize_boot_state s) = st_mscratch s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_satp:
  shows
    "st_satp (base_finalize_boot_state s) = st_satp s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_mstatus:
  shows
    "st_mstatus (base_finalize_boot_state s) = st_mstatus s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_sp:
  shows
    "st_sp (base_finalize_boot_state s) = st_sp s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_hart_index:
  shows
    "st_hart_index (base_finalize_boot_state s) = st_hart_index s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_boot_hartid:
  shows
    "st_boot_hartid (base_finalize_boot_state s) = st_boot_hartid s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_finalize_boot_state s) = st_boot_hart_mask s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_boot_dtb:
  shows
    "st_boot_dtb (base_finalize_boot_state s) = st_boot_dtb s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_boot_stack_top:
  shows
    "st_boot_stack_top (base_finalize_boot_state s) = st_boot_stack_top s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_boot_next_addr:
  shows
    "st_boot_next_addr (base_finalize_boot_state s) = st_boot_next_addr s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_boot_magic:
  shows
    "st_boot_magic (base_finalize_boot_state s) = st_boot_magic s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_boot_flags:
  shows
    "st_boot_flags (base_finalize_boot_state s) = st_boot_flags s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_text_span:
  shows
    "st_text_span (base_finalize_boot_state s) = st_text_span s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_stack_span:
  shows
    "st_stack_span (base_finalize_boot_state s) = st_stack_span s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_guard_span:
  shows
    "st_guard_span (base_finalize_boot_state s) = st_guard_span s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_bss_span:
  shows
    "st_bss_span (base_finalize_boot_state s) = st_bss_span s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_scratch_span:
  shows
    "st_scratch_span (base_finalize_boot_state s) = st_scratch_span s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_boot_checksum:
  shows
    "st_boot_checksum (base_finalize_boot_state s) = st_boot_checksum s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_bss_cleared:
  shows
    "st_bss_cleared (base_finalize_boot_state s) = st_bss_cleared s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_events_ready:
  shows
    "st_events_ready (base_finalize_boot_state s) = st_events_ready s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_finalize_boot_state s) = st_stack_guard_ready s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_scratch_ready:
  shows
    "st_scratch_ready (base_finalize_boot_state s) = st_scratch_ready s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_layout_ready:
  shows
    "st_layout_ready (base_finalize_boot_state s) = st_layout_ready s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_finalize_boot_state s) = st_csr_snapshot_ready s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_stack_valid:
  shows
    "st_stack_valid (base_finalize_boot_state s) = st_stack_valid s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_dtb_valid:
  shows
    "st_dtb_valid (base_finalize_boot_state s) = st_dtb_valid s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_checksum_ready:
  shows
    "st_checksum_ready (base_finalize_boot_state s) = st_checksum_ready s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_boot_ready:
  shows
    "st_boot_ready (base_finalize_boot_state s) = True"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_handoff_ready:
  shows
    "st_handoff_ready (base_finalize_boot_state s) = st_handoff_ready s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_secondary_seen:
  shows
    "st_secondary_seen (base_finalize_boot_state s) = st_secondary_seen s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_finalize_boot_state s) = st_secondary_wait_ready s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_finalize_boot_state_next:
  shows
    "st_next (base_finalize_boot_state s) = st_next s"
  by (simp add: base_finalize_boot_state_def)

lemma startup_frame_base_prepare_handoff_hartid:
  shows
    "st_hartid (base_prepare_handoff s) = st_hartid s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_dtb:
  shows
    "st_dtb (base_prepare_handoff s) = st_dtb s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_mie:
  shows
    "st_mie (base_prepare_handoff s) = st_mie s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_mscratch:
  shows
    "st_mscratch (base_prepare_handoff s) = st_mscratch s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_satp:
  shows
    "st_satp (base_prepare_handoff s) = st_satp s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_mstatus:
  shows
    "st_mstatus (base_prepare_handoff s) = st_mstatus s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_sp:
  shows
    "st_sp (base_prepare_handoff s) = st_sp s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_hart_index:
  shows
    "st_hart_index (base_prepare_handoff s) = st_hart_index s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_boot_hartid:
  shows
    "st_boot_hartid (base_prepare_handoff s) = st_boot_hartid s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_prepare_handoff s) = st_boot_hart_mask s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_boot_dtb:
  shows
    "st_boot_dtb (base_prepare_handoff s) = st_boot_dtb s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_boot_stack_top:
  shows
    "st_boot_stack_top (base_prepare_handoff s) = st_boot_stack_top s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_boot_next_addr:
  shows
    "st_boot_next_addr (base_prepare_handoff s) = FW_JUMP_ADDR"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_boot_magic:
  shows
    "st_boot_magic (base_prepare_handoff s) = st_boot_magic s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_boot_flags:
  shows
    "st_boot_flags (base_prepare_handoff s) = st_boot_flags s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_text_span:
  shows
    "st_text_span (base_prepare_handoff s) = st_text_span s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_stack_span:
  shows
    "st_stack_span (base_prepare_handoff s) = st_stack_span s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_guard_span:
  shows
    "st_guard_span (base_prepare_handoff s) = st_guard_span s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_bss_span:
  shows
    "st_bss_span (base_prepare_handoff s) = st_bss_span s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_scratch_span:
  shows
    "st_scratch_span (base_prepare_handoff s) = st_scratch_span s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_boot_checksum:
  shows
    "st_boot_checksum (base_prepare_handoff s) = st_boot_checksum s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_bss_cleared:
  shows
    "st_bss_cleared (base_prepare_handoff s) = st_bss_cleared s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_events_ready:
  shows
    "st_events_ready (base_prepare_handoff s) = st_events_ready s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_prepare_handoff s) = st_stack_guard_ready s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_scratch_ready:
  shows
    "st_scratch_ready (base_prepare_handoff s) = st_scratch_ready s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_layout_ready:
  shows
    "st_layout_ready (base_prepare_handoff s) = st_layout_ready s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_prepare_handoff s) = st_csr_snapshot_ready s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_stack_valid:
  shows
    "st_stack_valid (base_prepare_handoff s) = st_stack_valid s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_dtb_valid:
  shows
    "st_dtb_valid (base_prepare_handoff s) = st_dtb_valid s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_checksum_ready:
  shows
    "st_checksum_ready (base_prepare_handoff s) = st_checksum_ready s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_boot_ready:
  shows
    "st_boot_ready (base_prepare_handoff s) = st_boot_ready s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_handoff_ready:
  shows
    "st_handoff_ready (base_prepare_handoff s) = True"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_secondary_seen:
  shows
    "st_secondary_seen (base_prepare_handoff s) = st_secondary_seen s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_prepare_handoff s) = st_secondary_wait_ready s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_prepare_handoff_next:
  shows
    "st_next (base_prepare_handoff s) = st_next s"
  by (simp add: base_prepare_handoff_def)

lemma startup_frame_base_enter_sbi_main_hartid:
  shows
    "st_hartid (base_enter_sbi_main s) = st_hartid s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_dtb:
  shows
    "st_dtb (base_enter_sbi_main s) = st_dtb s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_mie:
  shows
    "st_mie (base_enter_sbi_main s) = st_mie s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_mscratch:
  shows
    "st_mscratch (base_enter_sbi_main s) = st_mscratch s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_satp:
  shows
    "st_satp (base_enter_sbi_main s) = st_satp s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_mstatus:
  shows
    "st_mstatus (base_enter_sbi_main s) = st_mstatus s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_sp:
  shows
    "st_sp (base_enter_sbi_main s) = st_sp s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_hart_index:
  shows
    "st_hart_index (base_enter_sbi_main s) = st_hart_index s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_boot_hartid:
  shows
    "st_boot_hartid (base_enter_sbi_main s) = st_boot_hartid s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_enter_sbi_main s) = st_boot_hart_mask s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_boot_dtb:
  shows
    "st_boot_dtb (base_enter_sbi_main s) = st_boot_dtb s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_boot_stack_top:
  shows
    "st_boot_stack_top (base_enter_sbi_main s) = st_boot_stack_top s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_boot_next_addr:
  shows
    "st_boot_next_addr (base_enter_sbi_main s) = st_boot_next_addr s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_boot_magic:
  shows
    "st_boot_magic (base_enter_sbi_main s) = st_boot_magic s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_boot_flags:
  shows
    "st_boot_flags (base_enter_sbi_main s) = st_boot_flags s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_text_span:
  shows
    "st_text_span (base_enter_sbi_main s) = st_text_span s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_stack_span:
  shows
    "st_stack_span (base_enter_sbi_main s) = st_stack_span s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_guard_span:
  shows
    "st_guard_span (base_enter_sbi_main s) = st_guard_span s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_bss_span:
  shows
    "st_bss_span (base_enter_sbi_main s) = st_bss_span s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_scratch_span:
  shows
    "st_scratch_span (base_enter_sbi_main s) = st_scratch_span s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_boot_checksum:
  shows
    "st_boot_checksum (base_enter_sbi_main s) = st_boot_checksum s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_bss_cleared:
  shows
    "st_bss_cleared (base_enter_sbi_main s) = st_bss_cleared s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_events_ready:
  shows
    "st_events_ready (base_enter_sbi_main s) = st_events_ready s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_enter_sbi_main s) = st_stack_guard_ready s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_scratch_ready:
  shows
    "st_scratch_ready (base_enter_sbi_main s) = st_scratch_ready s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_layout_ready:
  shows
    "st_layout_ready (base_enter_sbi_main s) = st_layout_ready s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_enter_sbi_main s) = st_csr_snapshot_ready s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_stack_valid:
  shows
    "st_stack_valid (base_enter_sbi_main s) = st_stack_valid s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_dtb_valid:
  shows
    "st_dtb_valid (base_enter_sbi_main s) = st_dtb_valid s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_checksum_ready:
  shows
    "st_checksum_ready (base_enter_sbi_main s) = st_checksum_ready s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_boot_ready:
  shows
    "st_boot_ready (base_enter_sbi_main s) = st_boot_ready s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_handoff_ready:
  shows
    "st_handoff_ready (base_enter_sbi_main s) = st_handoff_ready s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_secondary_seen:
  shows
    "st_secondary_seen (base_enter_sbi_main s) = st_secondary_seen s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_enter_sbi_main s) = st_secondary_wait_ready s"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_enter_sbi_main_next:
  shows
    "st_next (base_enter_sbi_main s) = StartupEnterSbiMain"
  by (simp add: base_enter_sbi_main_def)

lemma startup_frame_base_record_secondary_hart_hartid:
  shows
    "st_hartid (base_record_secondary_hart s) = st_hartid s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_dtb:
  shows
    "st_dtb (base_record_secondary_hart s) = st_dtb s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_mie:
  shows
    "st_mie (base_record_secondary_hart s) = st_mie s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_mscratch:
  shows
    "st_mscratch (base_record_secondary_hart s) = st_mscratch s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_satp:
  shows
    "st_satp (base_record_secondary_hart s) = st_satp s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_mstatus:
  shows
    "st_mstatus (base_record_secondary_hart s) = st_mstatus s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_sp:
  shows
    "st_sp (base_record_secondary_hart s) = st_sp s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_hart_index:
  shows
    "st_hart_index (base_record_secondary_hart s) = st_hart_index s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_boot_hartid:
  shows
    "st_boot_hartid (base_record_secondary_hart s) = st_hartid s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_record_secondary_hart s) = st_boot_hart_mask s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_boot_dtb:
  shows
    "st_boot_dtb (base_record_secondary_hart s) = st_dtb s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_boot_stack_top:
  shows
    "st_boot_stack_top (base_record_secondary_hart s) = st_boot_stack_top s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_boot_next_addr:
  shows
    "st_boot_next_addr (base_record_secondary_hart s) = st_boot_next_addr s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_boot_magic:
  shows
    "st_boot_magic (base_record_secondary_hart s) = st_boot_magic s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_boot_flags:
  shows
    "st_boot_flags (base_record_secondary_hart s) = st_boot_flags s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_text_span:
  shows
    "st_text_span (base_record_secondary_hart s) = st_text_span s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_stack_span:
  shows
    "st_stack_span (base_record_secondary_hart s) = st_stack_span s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_guard_span:
  shows
    "st_guard_span (base_record_secondary_hart s) = st_guard_span s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_bss_span:
  shows
    "st_bss_span (base_record_secondary_hart s) = st_bss_span s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_scratch_span:
  shows
    "st_scratch_span (base_record_secondary_hart s) = st_scratch_span s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_boot_checksum:
  shows
    "st_boot_checksum (base_record_secondary_hart s) = st_boot_checksum s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_bss_cleared:
  shows
    "st_bss_cleared (base_record_secondary_hart s) = st_bss_cleared s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_events_ready:
  shows
    "st_events_ready (base_record_secondary_hart s) = st_events_ready s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_record_secondary_hart s) = st_stack_guard_ready s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_scratch_ready:
  shows
    "st_scratch_ready (base_record_secondary_hart s) = st_scratch_ready s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_layout_ready:
  shows
    "st_layout_ready (base_record_secondary_hart s) = st_layout_ready s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_record_secondary_hart s) = st_csr_snapshot_ready s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_stack_valid:
  shows
    "st_stack_valid (base_record_secondary_hart s) = st_stack_valid s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_dtb_valid:
  shows
    "st_dtb_valid (base_record_secondary_hart s) = st_dtb_valid s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_checksum_ready:
  shows
    "st_checksum_ready (base_record_secondary_hart s) = st_checksum_ready s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_boot_ready:
  shows
    "st_boot_ready (base_record_secondary_hart s) = st_boot_ready s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_handoff_ready:
  shows
    "st_handoff_ready (base_record_secondary_hart s) = st_handoff_ready s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_secondary_seen:
  shows
    "st_secondary_seen (base_record_secondary_hart s) = True"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_record_secondary_hart s) = st_secondary_wait_ready s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_record_secondary_hart_next:
  shows
    "st_next (base_record_secondary_hart s) = st_next s"
  by (simp add: base_record_secondary_hart_def)

lemma startup_frame_base_wait_for_release_hartid:
  shows
    "st_hartid (base_wait_for_release s) = st_hartid s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_dtb:
  shows
    "st_dtb (base_wait_for_release s) = st_dtb s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_mie:
  shows
    "st_mie (base_wait_for_release s) = 0"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_mscratch:
  shows
    "st_mscratch (base_wait_for_release s) = 0"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_satp:
  shows
    "st_satp (base_wait_for_release s) = st_satp s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_mstatus:
  shows
    "st_mstatus (base_wait_for_release s) = st_mstatus s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_sp:
  shows
    "st_sp (base_wait_for_release s) = st_sp s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_hart_index:
  shows
    "st_hart_index (base_wait_for_release s) = st_hart_index s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_boot_hartid:
  shows
    "st_boot_hartid (base_wait_for_release s) = st_boot_hartid s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_wait_for_release s) = st_boot_hart_mask s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_boot_dtb:
  shows
    "st_boot_dtb (base_wait_for_release s) = st_boot_dtb s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_boot_stack_top:
  shows
    "st_boot_stack_top (base_wait_for_release s) = st_boot_stack_top s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_boot_next_addr:
  shows
    "st_boot_next_addr (base_wait_for_release s) = st_boot_next_addr s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_boot_magic:
  shows
    "st_boot_magic (base_wait_for_release s) = st_boot_magic s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_boot_flags:
  shows
    "st_boot_flags (base_wait_for_release s) = st_boot_flags s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_text_span:
  shows
    "st_text_span (base_wait_for_release s) = st_text_span s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_stack_span:
  shows
    "st_stack_span (base_wait_for_release s) = st_stack_span s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_guard_span:
  shows
    "st_guard_span (base_wait_for_release s) = st_guard_span s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_bss_span:
  shows
    "st_bss_span (base_wait_for_release s) = st_bss_span s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_scratch_span:
  shows
    "st_scratch_span (base_wait_for_release s) = st_scratch_span s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_boot_checksum:
  shows
    "st_boot_checksum (base_wait_for_release s) = st_boot_checksum s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_bss_cleared:
  shows
    "st_bss_cleared (base_wait_for_release s) = st_bss_cleared s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_events_ready:
  shows
    "st_events_ready (base_wait_for_release s) = st_events_ready s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_wait_for_release s) = st_stack_guard_ready s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_scratch_ready:
  shows
    "st_scratch_ready (base_wait_for_release s) = st_scratch_ready s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_layout_ready:
  shows
    "st_layout_ready (base_wait_for_release s) = st_layout_ready s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_wait_for_release s) = st_csr_snapshot_ready s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_stack_valid:
  shows
    "st_stack_valid (base_wait_for_release s) = st_stack_valid s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_dtb_valid:
  shows
    "st_dtb_valid (base_wait_for_release s) = st_dtb_valid s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_checksum_ready:
  shows
    "st_checksum_ready (base_wait_for_release s) = st_checksum_ready s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_boot_ready:
  shows
    "st_boot_ready (base_wait_for_release s) = st_boot_ready s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_handoff_ready:
  shows
    "st_handoff_ready (base_wait_for_release s) = st_handoff_ready s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_secondary_seen:
  shows
    "st_secondary_seen (base_wait_for_release s) = st_secondary_seen s"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_wait_for_release s) = True"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_wait_for_release_next:
  shows
    "st_next (base_wait_for_release s) = StartupWaitForRelease"
  by (simp add: base_wait_for_release_def)

lemma startup_frame_base_secondary_path_hartid:
  shows
    "st_hartid (base_secondary_path s) = st_hartid s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_dtb:
  shows
    "st_dtb (base_secondary_path s) = st_dtb s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_mie:
  shows
    "st_mie (base_secondary_path s) = 0"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_mscratch:
  shows
    "st_mscratch (base_secondary_path s) = 0"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_satp:
  shows
    "st_satp (base_secondary_path s) = st_satp s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_mstatus:
  shows
    "st_mstatus (base_secondary_path s) = st_mstatus s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_sp:
  shows
    "st_sp (base_secondary_path s) = st_sp s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_hart_index:
  shows
    "st_hart_index (base_secondary_path s) = st_hart_index s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_boot_hartid:
  shows
    "st_boot_hartid (base_secondary_path s) = st_boot_hartid s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_secondary_path s) = st_boot_hart_mask s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_boot_dtb:
  shows
    "st_boot_dtb (base_secondary_path s) = st_boot_dtb s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_boot_stack_top:
  shows
    "st_boot_stack_top (base_secondary_path s) = st_boot_stack_top s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_boot_next_addr:
  shows
    "st_boot_next_addr (base_secondary_path s) = st_boot_next_addr s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_boot_magic:
  shows
    "st_boot_magic (base_secondary_path s) = st_boot_magic s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_boot_flags:
  shows
    "st_boot_flags (base_secondary_path s) = st_boot_flags s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_text_span:
  shows
    "st_text_span (base_secondary_path s) = st_text_span s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_stack_span:
  shows
    "st_stack_span (base_secondary_path s) = st_stack_span s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_guard_span:
  shows
    "st_guard_span (base_secondary_path s) = st_guard_span s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_bss_span:
  shows
    "st_bss_span (base_secondary_path s) = st_bss_span s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_scratch_span:
  shows
    "st_scratch_span (base_secondary_path s) = st_scratch_span s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_boot_checksum:
  shows
    "st_boot_checksum (base_secondary_path s) = st_boot_checksum s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_bss_cleared:
  shows
    "st_bss_cleared (base_secondary_path s) = st_bss_cleared s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_events_ready:
  shows
    "st_events_ready (base_secondary_path s) = st_events_ready s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_secondary_path s) = st_stack_guard_ready s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_scratch_ready:
  shows
    "st_scratch_ready (base_secondary_path s) = st_scratch_ready s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_layout_ready:
  shows
    "st_layout_ready (base_secondary_path s) = st_layout_ready s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_secondary_path s) = st_csr_snapshot_ready s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_stack_valid:
  shows
    "st_stack_valid (base_secondary_path s) = st_stack_valid s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_dtb_valid:
  shows
    "st_dtb_valid (base_secondary_path s) = st_dtb_valid s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_checksum_ready:
  shows
    "st_checksum_ready (base_secondary_path s) = st_checksum_ready s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_boot_ready:
  shows
    "st_boot_ready (base_secondary_path s) = st_boot_ready s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_handoff_ready:
  shows
    "st_handoff_ready (base_secondary_path s) = st_handoff_ready s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_secondary_seen:
  shows
    "st_secondary_seen (base_secondary_path s) = st_secondary_seen s"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_secondary_path s) = True"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_secondary_path_next:
  shows
    "st_next (base_secondary_path s) = StartupWaitForRelease"
  by (simp add: base_secondary_path_def base_wait_for_release_def base_entry_reset_def)

lemma startup_frame_base_full_cold_path_hartid:
  shows
    "st_hartid (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = st_hartid s"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_dtb:
  shows
    "st_dtb (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = st_dtb s"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_mie:
  shows
    "st_mie (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = 0"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_mscratch:
  shows
    "st_mscratch (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = stack_top"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_satp:
  shows
    "st_satp (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = 0"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_mstatus:
  shows
    "st_mstatus (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = (st_mstatus s AND NOT STARTUP_MSTATUS_MIE) AND NOT MSTATUS_MPP"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_sp:
  shows
    "st_sp (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = stack_top"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_hart_index:
  shows
    "st_hart_index (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = hart_index"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_boot_hartid:
  shows
    "st_boot_hartid (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = st_hartid s"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = hart_mask"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_boot_dtb:
  shows
    "st_boot_dtb (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = st_dtb s"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_boot_stack_top:
  shows
    "st_boot_stack_top (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = stack_top"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_boot_next_addr:
  shows
    "st_boot_next_addr (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = FW_JUMP_ADDR"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_boot_magic:
  shows
    "st_boot_magic (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = SBI_BOOT_SCRATCH_MAGIC"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_boot_flags:
  shows
    "st_boot_flags (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = cold_boot_flags (st_dtb s)"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_text_span:
  shows
    "st_text_span (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = text_span"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_stack_span:
  shows
    "st_stack_span (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = stack_span"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_guard_span:
  shows
    "st_guard_span (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = guard_span"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_bss_span:
  shows
    "st_bss_span (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = bss_span"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_scratch_span:
  shows
    "st_scratch_span (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = scratch_span"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_boot_checksum:
  shows
    "st_boot_checksum (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = checksum"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_bss_cleared:
  shows
    "st_bss_cleared (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_events_ready:
  shows
    "st_events_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_scratch_ready:
  shows
    "st_scratch_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_layout_ready:
  shows
    "st_layout_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_stack_valid:
  shows
    "st_stack_valid (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = stack_ok"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_dtb_valid:
  shows
    "st_dtb_valid (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = dtb_ok"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_checksum_ready:
  shows
    "st_checksum_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_boot_ready:
  shows
    "st_boot_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_handoff_ready:
  shows
    "st_handoff_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_secondary_seen:
  shows
    "st_secondary_seen (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = st_secondary_seen s"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = st_secondary_wait_ready s"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

lemma startup_frame_base_full_cold_path_next:
  shows
    "st_next (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = StartupEnterSbiMain"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

subsection \<open>Full startup path conjunctions\<close>

theorem base_full_cold_path_post:
  shows
    "st_hartid (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = st_hartid s \<and>
     st_dtb (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = st_dtb s \<and>
     st_mie (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = 0 \<and>
     st_mscratch (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = stack_top \<and>
     st_satp (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = 0 \<and>
     st_mstatus (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = (st_mstatus s AND NOT STARTUP_MSTATUS_MIE) AND NOT MSTATUS_MPP \<and>
     st_sp (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = stack_top \<and>
     st_hart_index (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = hart_index \<and>
     st_boot_hartid (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = st_hartid s \<and>
     st_boot_hart_mask (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = hart_mask \<and>
     st_boot_dtb (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = st_dtb s \<and>
     st_boot_stack_top (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = stack_top \<and>
     st_boot_next_addr (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = FW_JUMP_ADDR \<and>
     st_boot_magic (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = SBI_BOOT_SCRATCH_MAGIC \<and>
     st_boot_flags (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = cold_boot_flags (st_dtb s) \<and>
     st_text_span (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = text_span \<and>
     st_stack_span (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = stack_span \<and>
     st_guard_span (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = guard_span \<and>
     st_bss_span (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = bss_span \<and>
     st_scratch_span (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = scratch_span \<and>
     st_boot_checksum (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = checksum \<and>
     st_bss_cleared (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True \<and>
     st_events_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True \<and>
     st_stack_guard_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True \<and>
     st_scratch_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True \<and>
     st_layout_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True \<and>
     st_csr_snapshot_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True \<and>
     st_stack_valid (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = stack_ok \<and>
     st_dtb_valid (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = dtb_ok \<and>
     st_checksum_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True \<and>
     st_boot_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True \<and>
     st_handoff_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = True \<and>
     st_secondary_seen (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = st_secondary_seen s \<and>
     st_secondary_wait_ready (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = st_secondary_wait_ready s \<and>
     st_next (base_full_cold_path hart_index stack_top hart_mask text_span stack_span guard_span bss_span scratch_span stack_ok dtb_ok checksum s) = StartupEnterSbiMain"
  by (simp add: base_full_cold_path_def base_entry_reset_def base_select_stack_def base_init_mscratch_def base_sanitize_csrs_def base_clear_bss_def base_reset_boot_records_def base_record_primary_hart_def base_append_event_def base_init_stack_guard_def base_init_hart_scratch_def base_record_memory_layout_def base_record_csr_snapshot_def base_validate_stack_def base_validate_dtb_def base_save_boot_state_def base_compute_boot_checksum_def base_init_boot_state_def base_finalize_boot_state_def base_prepare_handoff_def base_enter_sbi_main_def)

subsection \<open>Cold-prefix invariant samples\<close>

lemma startup_prefix_select_stack_hartid:
  shows
    "st_hartid (base_select_stack hart_index stack_top (base_entry_reset s)) = st_hartid s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_dtb:
  shows
    "st_dtb (base_select_stack hart_index stack_top (base_entry_reset s)) = st_dtb s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_mie:
  shows
    "st_mie (base_select_stack hart_index stack_top (base_entry_reset s)) = 0"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_mscratch:
  shows
    "st_mscratch (base_select_stack hart_index stack_top (base_entry_reset s)) = 0"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_satp:
  shows
    "st_satp (base_select_stack hart_index stack_top (base_entry_reset s)) = st_satp s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_mstatus:
  shows
    "st_mstatus (base_select_stack hart_index stack_top (base_entry_reset s)) = st_mstatus s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_sp:
  shows
    "st_sp (base_select_stack hart_index stack_top (base_entry_reset s)) = stack_top"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_hart_index:
  shows
    "st_hart_index (base_select_stack hart_index stack_top (base_entry_reset s)) = hart_index"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_boot_hartid:
  shows
    "st_boot_hartid (base_select_stack hart_index stack_top (base_entry_reset s)) = st_boot_hartid s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_select_stack hart_index stack_top (base_entry_reset s)) = st_boot_hart_mask s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_boot_dtb:
  shows
    "st_boot_dtb (base_select_stack hart_index stack_top (base_entry_reset s)) = st_boot_dtb s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_boot_stack_top:
  shows
    "st_boot_stack_top (base_select_stack hart_index stack_top (base_entry_reset s)) = st_boot_stack_top s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_boot_next_addr:
  shows
    "st_boot_next_addr (base_select_stack hart_index stack_top (base_entry_reset s)) = st_boot_next_addr s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_boot_magic:
  shows
    "st_boot_magic (base_select_stack hart_index stack_top (base_entry_reset s)) = st_boot_magic s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_boot_flags:
  shows
    "st_boot_flags (base_select_stack hart_index stack_top (base_entry_reset s)) = st_boot_flags s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_text_span:
  shows
    "st_text_span (base_select_stack hart_index stack_top (base_entry_reset s)) = st_text_span s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_stack_span:
  shows
    "st_stack_span (base_select_stack hart_index stack_top (base_entry_reset s)) = st_stack_span s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_guard_span:
  shows
    "st_guard_span (base_select_stack hart_index stack_top (base_entry_reset s)) = st_guard_span s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_bss_span:
  shows
    "st_bss_span (base_select_stack hart_index stack_top (base_entry_reset s)) = st_bss_span s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_scratch_span:
  shows
    "st_scratch_span (base_select_stack hart_index stack_top (base_entry_reset s)) = st_scratch_span s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_boot_checksum:
  shows
    "st_boot_checksum (base_select_stack hart_index stack_top (base_entry_reset s)) = st_boot_checksum s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_bss_cleared:
  shows
    "st_bss_cleared (base_select_stack hart_index stack_top (base_entry_reset s)) = st_bss_cleared s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_events_ready:
  shows
    "st_events_ready (base_select_stack hart_index stack_top (base_entry_reset s)) = st_events_ready s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_stack_guard_ready:
  shows
    "st_stack_guard_ready (base_select_stack hart_index stack_top (base_entry_reset s)) = st_stack_guard_ready s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_scratch_ready:
  shows
    "st_scratch_ready (base_select_stack hart_index stack_top (base_entry_reset s)) = st_scratch_ready s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_layout_ready:
  shows
    "st_layout_ready (base_select_stack hart_index stack_top (base_entry_reset s)) = st_layout_ready s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_csr_snapshot_ready:
  shows
    "st_csr_snapshot_ready (base_select_stack hart_index stack_top (base_entry_reset s)) = st_csr_snapshot_ready s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_stack_valid:
  shows
    "st_stack_valid (base_select_stack hart_index stack_top (base_entry_reset s)) = st_stack_valid s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_dtb_valid:
  shows
    "st_dtb_valid (base_select_stack hart_index stack_top (base_entry_reset s)) = st_dtb_valid s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_checksum_ready:
  shows
    "st_checksum_ready (base_select_stack hart_index stack_top (base_entry_reset s)) = st_checksum_ready s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_boot_ready:
  shows
    "st_boot_ready (base_select_stack hart_index stack_top (base_entry_reset s)) = st_boot_ready s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_handoff_ready:
  shows
    "st_handoff_ready (base_select_stack hart_index stack_top (base_entry_reset s)) = st_handoff_ready s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_secondary_seen:
  shows
    "st_secondary_seen (base_select_stack hart_index stack_top (base_entry_reset s)) = st_secondary_seen s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_secondary_wait_ready:
  shows
    "st_secondary_wait_ready (base_select_stack hart_index stack_top (base_entry_reset s)) = st_secondary_wait_ready s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_select_stack_next:
  shows
    "st_next (base_select_stack hart_index stack_top (base_entry_reset s)) = st_next s"
  by (simp add: base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_hartid:
  shows
    "st_hartid (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = st_hartid s"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_dtb:
  shows
    "st_dtb (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = st_dtb s"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_mie:
  shows
    "st_mie (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = 0"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_mscratch:
  shows
    "st_mscratch (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = stack_top"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_satp:
  shows
    "st_satp (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = st_satp s"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_mstatus:
  shows
    "st_mstatus (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = st_mstatus s"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_sp:
  shows
    "st_sp (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = stack_top"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_hart_index:
  shows
    "st_hart_index (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = hart_index"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_boot_hartid:
  shows
    "st_boot_hartid (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = st_boot_hartid s"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_boot_hart_mask:
  shows
    "st_boot_hart_mask (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = st_boot_hart_mask s"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_boot_dtb:
  shows
    "st_boot_dtb (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = st_boot_dtb s"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_boot_stack_top:
  shows
    "st_boot_stack_top (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = stack_top"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_boot_next_addr:
  shows
    "st_boot_next_addr (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = st_boot_next_addr s"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_boot_magic:
  shows
    "st_boot_magic (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = st_boot_magic s"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_boot_flags:
  shows
    "st_boot_flags (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = st_boot_flags s OR SBI_BOOT_FLAG_STACK_READY"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_text_span:
  shows
    "st_text_span (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = st_text_span s"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_stack_span:
  shows
    "st_stack_span (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = st_stack_span s"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_guard_span:
  shows
    "st_guard_span (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = st_guard_span s"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_bss_span:
  shows
    "st_bss_span (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = st_bss_span s"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_scratch_span:
  shows
    "st_scratch_span (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = st_scratch_span s"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)

lemma startup_prefix_init_mscratch_boot_checksum:
  shows
    "st_boot_checksum (base_init_mscratch (base_select_stack hart_index stack_top (base_entry_reset s))) = st_boot_checksum s"
  by (simp add: base_init_mscratch_def base_select_stack_def base_entry_reset_def)


end
