theory SeSBI_PMP_RawTable
  imports SeSBI_PMP_RawDecode
begin

unbundle bit_operations_syntax

section \<open>Raw PMP table decode bridge\<close>

text \<open>
  Experiment 14 lifts the single-entry raw decoder to a raw PMP table decoder.
  The decoder scans @{text pmpaddr} values and cfg bytes in entry-index order,
  so the resulting @{typ PmpEntry} list preserves PMP priority order.

  TOR uses the immediately previous raw @{text pmpaddr} value, even when the
  previous entry is OFF.  Therefore the recursive decoder carries the previous
  raw address separately from the decoded entry list.
\<close>

definition pmpaddr_zero :: xlenbits where
  "pmpaddr_zero = 0"

fun decode_raw_pmp_table_from_prev ::
  "xlenbits \<Rightarrow> xlenbits list \<Rightarrow> 8 word list \<Rightarrow> PmpEntry list" where
  "decode_raw_pmp_table_from_prev prev [] cfgs = []"
| "decode_raw_pmp_table_from_prev prev (pa # pas) [] = []"
| "decode_raw_pmp_table_from_prev prev (pa # pas) (cfg # cfgs) =
     prepend_decoded_raw_entry prev pa cfg
       (decode_raw_pmp_table_from_prev pa pas cfgs)"

definition decode_raw_pmp_table ::
  "xlenbits list \<Rightarrow> 8 word list \<Rightarrow> PmpEntry list" where
  "decode_raw_pmp_table pas cfgs =
     decode_raw_pmp_table_from_prev pmpaddr_zero pas cfgs"

subsection \<open>Basic table facts\<close>

theorem decode_raw_pmp_table_cons_some:
  assumes "decode_raw_pmp_entry prev pa cfg = Some e"
  shows "decode_raw_pmp_table_from_prev prev (pa # pas) (cfg # cfgs) =
         e # decode_raw_pmp_table_from_prev pa pas cfgs"
  using assms by (simp add: prepend_decoded_raw_entry_def)

theorem decode_raw_pmp_table_cons_none:
  assumes "decode_raw_pmp_entry prev pa cfg = None"
  shows "decode_raw_pmp_table_from_prev prev (pa # pas) (cfg # cfgs) =
         decode_raw_pmp_table_from_prev pa pas cfgs"
  using assms by (simp add: prepend_decoded_raw_entry_def)

theorem decode_raw_pmp_table_OFF_skips_and_advances_prev:
  assumes "cfg_A_field cfg = PMP_A_OFF"
  shows "decode_raw_pmp_table_from_prev prev (pa # pas) (cfg # cfgs) =
         decode_raw_pmp_table_from_prev pa pas cfgs"
  using decode_raw_OFF_none[OF assms, of prev pa]
  by (simp add: prepend_decoded_raw_entry_def)

theorem decode_raw_pmp_table_head_priority:
  assumes "decode_raw_pmp_entry prev pa cfg = Some e"
  shows "pmp_check_scope
           (decode_raw_pmp_table_from_prev prev (pa # pas) (cfg # cfgs))
           p kind addr width =
         (case pmp_entry_check_scope e p kind addr width of
            PMP_Continue \<Rightarrow>
              pmp_check_scope
                (decode_raw_pmp_table_from_prev pa pas cfgs)
                p kind addr width
          | PMP_Allow \<Rightarrow> PMP_Allow
          | PMP_Fault \<Rightarrow> PMP_Fault)"
  using assms by (simp add: prepend_decoded_raw_entry_def)

theorem decode_raw_pmp_table_head_fault_priority:
  assumes dec: "decode_raw_pmp_entry prev pa cfg = Some e"
      and fault: "pmp_entry_check_scope e p kind addr width = PMP_Fault"
  shows "pmp_check_scope
           (decode_raw_pmp_table_from_prev prev (pa # pas) (cfg # cfgs))
           p kind addr width = PMP_Fault"
  using dec fault by (simp add: prepend_decoded_raw_entry_def)

theorem decode_raw_pmp_table_head_allow_priority:
  assumes dec: "decode_raw_pmp_entry prev pa cfg = Some e"
      and allow: "pmp_entry_check_scope e p kind addr width = PMP_Allow"
  shows "pmp_check_scope
           (decode_raw_pmp_table_from_prev prev (pa # pas) (cfg # cfgs))
           p kind addr width = PMP_Allow"
  using dec allow by (simp add: prepend_decoded_raw_entry_def)

lemma length_decode_raw_pmp_table_from_prev_le_addrs:
  "length (decode_raw_pmp_table_from_prev prev pas cfgs) \<le> length pas"
  by (induction prev pas cfgs rule: decode_raw_pmp_table_from_prev.induct)
     (auto simp: prepend_decoded_raw_entry_def split: option.splits)

lemma length_decode_raw_pmp_table_from_prev_le_cfgs:
  "length (decode_raw_pmp_table_from_prev prev pas cfgs) \<le> length cfgs"
  by (induction prev pas cfgs rule: decode_raw_pmp_table_from_prev.induct)
     (auto simp: prepend_decoded_raw_entry_def split: option.splits)

subsection \<open>TOR predecessor behavior\<close>

theorem decode_raw_pmp_table_TOR_head_uses_initial_prev:
  assumes "cfg_A_field cfg = PMP_A_TOR"
  shows "decode_raw_pmp_table_from_prev prev (pa # pas) (cfg # cfgs) =
         \<lparr> pmp_bgn = pmpaddr_addr prev, pmp_en = pmpaddr_addr pa,
           pmp_R = cfg_R cfg, pmp_W = cfg_W cfg,
           pmp_X = cfg_X cfg, pmp_L = cfg_L cfg \<rparr>
         # decode_raw_pmp_table_from_prev pa pas cfgs"
  using decode_raw_TOR_entry[OF assms, of prev pa]
  by (simp add: prepend_decoded_raw_entry_def)

theorem decode_raw_pmp_table_TOR_after_OFF_uses_skipped_pmpaddr:
  assumes off: "cfg_A_field off_cfg = PMP_A_OFF"
      and tor: "cfg_A_field tor_cfg = PMP_A_TOR"
  shows "decode_raw_pmp_table_from_prev prev
           (pa0 # pa1 # pas) (off_cfg # tor_cfg # cfgs) =
         \<lparr> pmp_bgn = pmpaddr_addr pa0, pmp_en = pmpaddr_addr pa1,
           pmp_R = cfg_R tor_cfg, pmp_W = cfg_W tor_cfg,
           pmp_X = cfg_X tor_cfg, pmp_L = cfg_L tor_cfg \<rparr>
         # decode_raw_pmp_table_from_prev pa1 pas cfgs"
  using decode_raw_pmp_table_OFF_skips_and_advances_prev[OF off, of prev pa0 "pa1 # pas" "tor_cfg # cfgs"]
        decode_raw_pmp_table_TOR_head_uses_initial_prev[OF tor, of pa0 pa1 pas cfgs]
  by simp

subsection \<open>SeSBI current and corrected raw boot tables\<close>

definition current_boot_raw_pmpaddrs :: "xlenbits list" where
  "current_boot_raw_pmpaddrs =
     [pmpaddr_all_ones, pmp_encode_napot PAYLOAD_START 18]"

definition current_boot_raw_pmpcfgs :: "8 word list" where
  "current_boot_raw_pmpcfgs =
     [sbi_pmpcfg_byte PMP_RWX, sbi_pmpcfg_byte PMP_RWX]"

definition corrected_boot_raw_pmpaddrs ::
  "xlenbits \<Rightarrow> nat \<Rightarrow> xlenbits list" where
  "corrected_boot_raw_pmpaddrs fw_start k =
     [pmp_encode_napot fw_start k, pmpaddr_all_ones]"

definition corrected_boot_raw_pmpcfgs :: "8 word list" where
  "corrected_boot_raw_pmpcfgs =
     [sbi_pmpcfg_byte 0, sbi_pmpcfg_byte PMP_RWX]"

theorem decode_current_boot_raw_table_eq_current_boot_entries:
  "decode_raw_pmp_table current_boot_raw_pmpaddrs current_boot_raw_pmpcfgs =
   current_boot_entries"
  by (simp add: decode_raw_pmp_table_def current_boot_raw_pmpaddrs_def
                current_boot_raw_pmpcfgs_def current_boot_entries_def
                pmpaddr_zero_def prepend_decoded_raw_entry_def
                decode_raw_xlen_allow_all_eq_allow_l0_entry
                decode_raw_sbi_napot_eq_installed_entry)

theorem raw_table_current_boot_allows_low_priv_no_mprv:
  assumes low: "low_priv p"
      and inside: "addr + width \<le> (2::nat)^64"
      and nonempty: "0 < width"
  shows "pmp_check_scope_effective
           (decode_raw_pmp_table current_boot_raw_pmpaddrs current_boot_raw_pmpcfgs)
           p False mpp kind addr width = PMP_Allow"
  using current_boot_scope_allows_any_low_priv_access_inside_phys_no_mprv[
          OF low inside nonempty, of mpp kind]
  by (simp add: decode_current_boot_raw_table_eq_current_boot_entries)

theorem decode_corrected_boot_raw_table_eq_entries:
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
  shows "decode_raw_pmp_table
           (corrected_boot_raw_pmpaddrs fw_start k)
           corrected_boot_raw_pmpcfgs =
         corrected_boot_entries fw_start k [allow_l0_entry 0 ((2::nat)^64)]"
  using decode_raw_sbi_napot_eq_installed_entry[
          where prev=pmpaddr_zero and start=fw_start and prot=0, OF k_lo k_hi]
  by (simp add: decode_raw_pmp_table_def corrected_boot_raw_pmpaddrs_def
                corrected_boot_raw_pmpcfgs_def corrected_boot_entries_def
                pmpaddr_zero_def prepend_decoded_raw_entry_def
                decode_raw_xlen_allow_all_eq_allow_l0_entry)

theorem raw_table_corrected_boot_isolates_effective_low_priv:
  fixes fw_start :: xlenbits and k :: nat
  defines "fw_base \<equiv> unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4"
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
      and eff_low: "low_priv (effective_privilege kind mprv mpp priv)"
      and ov: "ranges_overlap fw_base (fw_base + 2 ^ k) addr width"
  shows "pmp_check_scope_effective
           (decode_raw_pmp_table
              (corrected_boot_raw_pmpaddrs fw_start k)
              corrected_boot_raw_pmpcfgs)
           priv mprv mpp kind addr width = PMP_Fault"
proof -
  have table:
    "decode_raw_pmp_table
       (corrected_boot_raw_pmpaddrs fw_start k)
       corrected_boot_raw_pmpcfgs =
     corrected_boot_entries fw_start k [allow_l0_entry 0 ((2::nat)^64)]"
    by (rule decode_corrected_boot_raw_table_eq_entries[OF k_lo k_hi])
  have entries:
    "corrected_boot_entries fw_start k [allow_l0_entry 0 ((2::nat)^64)] =
     bs_entries
       (corrected_boot_state 0 fw_start k [allow_l0_entry 0 ((2::nat)^64)])"
    by (simp add: corrected_boot_state_def)
  have fault:
    "pmp_check_scope_effective
       (bs_entries
         (corrected_boot_state 0 fw_start k [allow_l0_entry 0 ((2::nat)^64)]))
       priv mprv mpp kind addr width = PMP_Fault"
  proof -
    have ov':
      "ranges_overlap
        (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4)
        (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4 + 2 ^ k)
        addr width"
      using ov by (simp add: fw_base_def)
    show ?thesis
      by (rule corrected_boot_scope_isolates_effective_low_priv[OF k_lo k_hi eff_low ov'])
  qed
  show ?thesis using table entries fault by simp
qed

end
