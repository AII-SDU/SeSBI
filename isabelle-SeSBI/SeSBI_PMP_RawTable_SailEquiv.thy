theory SeSBI_PMP_RawTable_SailEquiv
  imports
    SeSBI_PMP_RawTable
    "sail-generated/Pmp_raw_table_mw"
begin

section \<open>Generated Sail bridge for the raw PMP table subset\<close>

text \<open>
  This theory connects the local raw-table PMP decoder/check model to a
  Sail/Lem-generated subset from \<open>sail-generated/pmp_raw_table_mw.sail\<close>.

  The generated subset covers raw table scanning, OFF skipping, TOR predecessor
  propagation, NAPOT interval decoding, the SeSBI all-ones allow-all branch, and
  the same Sail-shaped PMP-check control flow used in Experiment 10.  It still
  does not claim the complete official sail-riscv register-state PMP machine.
\<close>

definition sail_rt_match_of ::
  "PmpMatch \<Rightarrow> Pmp_raw_table_mw_types.pmpAddrMatch" where
  "sail_rt_match_of m =
     (case m of
        SeSBI_PMP_NAPOT.PMP_NoMatch \<Rightarrow> Pmp_raw_table_mw_types.PMP_NoMatch
      | SeSBI_PMP_NAPOT.PMP_PartialMatch \<Rightarrow> Pmp_raw_table_mw_types.PMP_PartialMatch
      | SeSBI_PMP_NAPOT.PMP_Match \<Rightarrow> Pmp_raw_table_mw_types.PMP_Match)"

definition sail_rt_raw_mode_of ::
  "RawPmpAddrMode \<Rightarrow> Pmp_raw_table_mw_types.PmpRawMode" where
  "sail_rt_raw_mode_of m =
     (case m of
        SeSBI_PMP_RawDecode.Raw_OFF \<Rightarrow> Pmp_raw_table_mw_types.Raw_OFF
      | SeSBI_PMP_RawDecode.Raw_TOR \<Rightarrow> Pmp_raw_table_mw_types.Raw_TOR
      | SeSBI_PMP_RawDecode.Raw_NA4 \<Rightarrow> Pmp_raw_table_mw_types.Raw_NA4
      | SeSBI_PMP_RawDecode.Raw_NAPOT \<Rightarrow> Pmp_raw_table_mw_types.Raw_NAPOT)"

definition sail_rt_priv_of ::
  "PrivMode \<Rightarrow> Pmp_raw_table_mw_types.PmpScopePriv" where
  "sail_rt_priv_of p =
     (case p of
        User \<Rightarrow> Pmp_raw_table_mw_types.Scope_User
      | Supervisor \<Rightarrow> Pmp_raw_table_mw_types.Scope_Supervisor
      | Machine \<Rightarrow> Pmp_raw_table_mw_types.Scope_Machine)"

definition sail_rt_access_of ::
  "AccessKind \<Rightarrow> Pmp_raw_table_mw_types.PmpScopeAccess" where
  "sail_rt_access_of kind =
     (case kind of
        Read \<Rightarrow> Pmp_raw_table_mw_types.Scope_Read
      | Write \<Rightarrow> Pmp_raw_table_mw_types.Scope_Write
      | Execute \<Rightarrow> Pmp_raw_table_mw_types.Scope_Execute)"

definition sail_rt_decision_of ::
  "PmpDecision \<Rightarrow> Pmp_raw_table_mw_types.PmpScopeDecision" where
  "sail_rt_decision_of d =
     (case d of
        PMP_Continue \<Rightarrow> Pmp_raw_table_mw_types.Scope_Continue
      | PMP_Allow \<Rightarrow> Pmp_raw_table_mw_types.Scope_Allow
      | PMP_Fault \<Rightarrow> Pmp_raw_table_mw_types.Scope_Fault)"

definition sail_rt_raw_cfg_of ::
  "8 word \<Rightarrow> Pmp_raw_table_mw_types.PmpRawCfg" where
  "sail_rt_raw_cfg_of cfg =
     \<lparr> PmpRawCfg_raw_mode = sail_rt_raw_mode_of (cfg_addr_mode cfg),
       PmpRawCfg_raw_R = cfg_R cfg,
       PmpRawCfg_raw_W = cfg_W cfg,
       PmpRawCfg_raw_X = cfg_X cfg,
       PmpRawCfg_raw_L = cfg_L cfg \<rparr>"

definition sail_rt_raw_entry_of ::
  "xlenbits \<Rightarrow> 8 word \<Rightarrow> Pmp_raw_table_mw_types.PmpRawEntry" where
  "sail_rt_raw_entry_of pa cfg =
     \<lparr> PmpRawEntry_raw_addr = pa,
       PmpRawEntry_raw_cfg = sail_rt_raw_cfg_of cfg,
       PmpRawEntry_raw_all_ones = (pa = pmpaddr_all_ones) \<rparr>"

fun sail_rt_raw_entries_of ::
  "xlenbits list \<Rightarrow> 8 word list \<Rightarrow> Pmp_raw_table_mw_types.PmpRawEntry list" where
  "sail_rt_raw_entries_of [] cfgs = []"
| "sail_rt_raw_entries_of (pa # pas) [] = []"
| "sail_rt_raw_entries_of (pa # pas) (cfg # cfgs) =
     sail_rt_raw_entry_of pa cfg # sail_rt_raw_entries_of pas cfgs"

definition sail_rt_entry_of ::
  "PmpEntry \<Rightarrow> Pmp_raw_table_mw_types.PmpScopeEntry" where
  "sail_rt_entry_of e =
     \<lparr> PmpScopeEntry_scope_bgn = int (pmp_bgn e),
       PmpScopeEntry_scope_en = int (pmp_en e),
       PmpScopeEntry_scope_R = pmp_R e,
       PmpScopeEntry_scope_W = pmp_W e,
       PmpScopeEntry_scope_X = pmp_X e,
       PmpScopeEntry_scope_L = pmp_L e \<rparr>"

lemma add_vec_int_one_rt:
  "add_vec_int (a :: 64 word) 1 = a + 1"
proof -
  have "add_vec_int a (1::int) =
        word_of_int (uint a + uint (word_of_int 1 :: 64 word))"
    unfolding add_vec_int_def arith_op_bv_int_def
              instance_Sail2_values_Bitvector_Machine_word_mword_dict_def
              int_of_mword_def
    by simp
  thus ?thesis by (simp add: word_of_int_uint)
qed

lemma pmpaddrAddr_matches:
  "Pmp_raw_table_mw.pmpaddrAddr pa = int (pmpaddr_addr pa)"
proof -
  have uint_eq: "uint pa = int (unat pa)"
    by (simp only: uint_nat)
  show ?thesis
    by (simp only: Pmp_raw_table_mw.pmpaddrAddr_def pmpaddr_addr_def
                   uint_eq of_nat_mult of_nat_numeral)
qed

lemma napotRegion_matches:
  "Pmp_raw_table_mw.napotRegion pa =
   (int (fst (napot_region pa)), int (snd (napot_region pa)))"
proof -
  have add1: "add_vec_int pa ((1 :: int)::ii) = pa + 1"
    by (simp add: add_vec_int_one_rt)
  define m where "m = (pa XOR (pa + 1) :: xlenbits)"
  define b where "b = (pa AND NOT m :: xlenbits)"
  have gen:
    "Pmp_raw_table_mw.napotRegion pa =
     (uint b * 4, (uint b + uint m + 1) * 4)"
    unfolding Pmp_raw_table_mw.napotRegion_def Let_def
    by (simp only: add1 xor_vec_def and_vec_def not_vec_def m_def b_def)
  have loc:
    "napot_region pa = (unat b * 4, (unat b + unat m + 1) * 4)"
    unfolding napot_region_def Let_def m_def b_def by simp
  have uint_b: "uint b = int (unat b)"
    by (simp only: uint_nat)
  have uint_m: "uint m = int (unat m)"
    by (simp only: uint_nat)
  show ?thesis
    using gen loc uint_b uint_m
    by (simp only: fst_conv snd_conv of_nat_add of_nat_mult
                   of_nat_1 of_nat_numeral)
qed

lemma pmpRangeMatch_matches_sail_rt:
  "Pmp_raw_table_mw.pmpRangeMatch (int bgn) (int en) (int addr) (int width) =
   sail_rt_match_of (SeSBI_PMP_NAPOT.pmpRangeMatch bgn en addr width)"
  by (auto simp: Pmp_raw_table_mw.pmpRangeMatch_def
                 SeSBI_PMP_NAPOT.pmpRangeMatch_def
                 sail_rt_match_of_def)

lemma rawEntryOfRegion_matches:
  "Pmp_raw_table_mw.rawEntryOfRegion (sail_rt_raw_cfg_of cfg) (int bgn) (int en) =
   sail_rt_entry_of (raw_entry_of_region cfg (bgn, en))"
  by (simp add: Pmp_raw_table_mw.rawEntryOfRegion_def
                sail_rt_raw_cfg_of_def sail_rt_entry_of_def
                raw_entry_of_region_def)

lemma decodeRawPmpEntry_matches:
  "Pmp_raw_table_mw.decodeRawPmpEntry prev (sail_rt_raw_entry_of pa cfg) =
   map_option sail_rt_entry_of (decode_raw_pmp_entry prev pa cfg)"
proof (cases "cfg_addr_mode cfg")
  case Raw_OFF
  then show ?thesis
    by (simp add: Pmp_raw_table_mw.decodeRawPmpEntry_def
                  sail_rt_raw_entry_of_def sail_rt_raw_cfg_of_def
                  sail_rt_raw_mode_of_def decode_raw_pmp_entry_def
                  raw_region_of_def)
next
  case Raw_TOR
  then show ?thesis
    by (simp add: Pmp_raw_table_mw.decodeRawPmpEntry_def
                  sail_rt_raw_entry_of_def sail_rt_raw_cfg_of_def
                  sail_rt_raw_mode_of_def decode_raw_pmp_entry_def
                  raw_region_of_def pmpaddrAddr_matches
                  Pmp_raw_table_mw.rawEntryOfRegion_def
                  sail_rt_entry_of_def raw_entry_of_region_def)
next
  case Raw_NA4
  then show ?thesis
    by (simp add: Pmp_raw_table_mw.decodeRawPmpEntry_def
                  sail_rt_raw_entry_of_def sail_rt_raw_cfg_of_def
                  sail_rt_raw_mode_of_def decode_raw_pmp_entry_def
                  raw_region_of_def pmpaddrAddr_matches
                  Pmp_raw_table_mw.rawEntryOfRegion_def
                  sail_rt_entry_of_def raw_entry_of_region_def)
next
  case Raw_NAPOT
  then show ?thesis
    by (cases "pa = pmpaddr_all_ones")
       (simp_all add: Pmp_raw_table_mw.decodeRawPmpEntry_def
                      sail_rt_raw_entry_of_def sail_rt_raw_cfg_of_def
                      sail_rt_raw_mode_of_def decode_raw_pmp_entry_def
                      raw_region_of_def napotRegion_matches
                      Pmp_raw_table_mw.rawEntryOfRegion_def
                      sail_rt_entry_of_def raw_entry_of_region_def)
qed

termination Pmp_raw_table_mw.decodeRawPmpTableFromPrev
  by lexicographic_order

theorem decodeRawPmpTableFromPrev_matches:
  "Pmp_raw_table_mw.decodeRawPmpTableFromPrev prev
     (sail_rt_raw_entries_of pas cfgs) =
   map sail_rt_entry_of (decode_raw_pmp_table_from_prev prev pas cfgs)"
proof (induction pas arbitrary: prev cfgs)
  case Nil
  then show ?case by simp
next
  case (Cons pa pas)
  show ?case
  proof (cases cfgs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons cfg cfgs')
    have IH:
      "Pmp_raw_table_mw.decodeRawPmpTableFromPrev pa
         (sail_rt_raw_entries_of pas cfgs') =
       map sail_rt_entry_of (decode_raw_pmp_table_from_prev pa pas cfgs')"
      using Cons.IH by simp
    have dec:
      "Pmp_raw_table_mw.decodeRawPmpEntry prev (sail_rt_raw_entry_of pa cfg) =
       map_option sail_rt_entry_of (decode_raw_pmp_entry prev pa cfg)"
      by (rule decodeRawPmpEntry_matches)
    show ?thesis
    proof (cases "decode_raw_pmp_entry prev pa cfg")
      case None
      then show ?thesis
        using Cons IH dec
        by (simp add: prepend_decoded_raw_entry_def sail_rt_raw_entry_of_def)
    next
      case (Some e)
      then show ?thesis
        using Cons IH dec
        by (simp add: prepend_decoded_raw_entry_def sail_rt_raw_entry_of_def)
    qed
  qed
qed

lemma decodeRawPmpTable_matches:
  "Pmp_raw_table_mw.decodeRawPmpTableFromPrev 0
     (sail_rt_raw_entries_of pas cfgs) =
   map sail_rt_entry_of (decode_raw_pmp_table pas cfgs)"
  by (simp add: decodeRawPmpTableFromPrev_matches
                decode_raw_pmp_table_def pmpaddr_zero_def)

lemma pmpCheckRWX_scope_matches_entry_allows_rt:
  "Pmp_raw_table_mw.pmpCheckRWX_scope
     (sail_rt_entry_of e) (sail_rt_access_of kind) =
   entry_allows e kind"
  by (cases kind)
     (simp_all add: sail_rt_entry_of_def sail_rt_access_of_def entry_allows_def)

lemma pmpLocked_scope_matches_rt:
  "Pmp_raw_table_mw.pmpLocked_scope (sail_rt_entry_of e) = pmp_L e"
  by (simp add: sail_rt_entry_of_def Pmp_raw_table_mw.pmpLocked_scope_def)

lemma effective_privilege_matches_sail_rt:
  "Pmp_raw_table_mw.effectivePrivilegeScope
     (sail_rt_access_of kind) mprv (sail_rt_priv_of mpp) (sail_rt_priv_of priv) =
   sail_rt_priv_of (effective_privilege kind mprv mpp priv)"
  by (cases kind; cases mprv)
     (simp_all add: effective_privilege_def is_fetch_def
                    sail_rt_access_of_def sail_rt_priv_of_def)

lemma pmp_entry_check_scope_matches_sail_rt:
  "Pmp_raw_table_mw.pmpEntryCheckScope
     (sail_rt_entry_of e) (sail_rt_priv_of p) (sail_rt_access_of kind)
     (int addr) (int width) =
   sail_rt_decision_of (pmp_entry_check_scope e p kind addr width)"
proof -
  have range:
    "Pmp_raw_table_mw.pmpRangeMatch
       (PmpScopeEntry_scope_bgn (sail_rt_entry_of e))
       (PmpScopeEntry_scope_en (sail_rt_entry_of e))
       (int addr) (int width) =
     sail_rt_match_of
       (SeSBI_PMP_NAPOT.pmpRangeMatch (pmp_bgn e) (pmp_en e) addr width)"
    by (simp add: sail_rt_entry_of_def pmpRangeMatch_matches_sail_rt)
  show ?thesis
    using range
    by (cases "SeSBI_PMP_NAPOT.pmpRangeMatch (pmp_bgn e) (pmp_en e) addr width";
        cases p; cases kind)
       (simp_all add: Pmp_raw_table_mw.pmpEntryCheckScope_def
                      pmp_entry_check_scope_def sail_rt_match_of_def
                      sail_rt_priv_of_def sail_rt_access_of_def
                      sail_rt_decision_of_def sail_rt_entry_of_def
                      Pmp_raw_table_mw.pmpLocked_scope_def
                      pmpCheckRWX_scope_matches_entry_allows_rt
                      pmpLocked_scope_matches_rt entry_allows_def)
qed

termination Pmp_raw_table_mw.pmpCheckScope
  by lexicographic_order

theorem pmp_check_scope_matches_sail_rt:
  "Pmp_raw_table_mw.pmpCheckScope
     (map sail_rt_entry_of es) (sail_rt_priv_of p) (sail_rt_access_of kind)
     (int addr) (int width) =
   sail_rt_decision_of (pmp_check_scope es p kind addr width)"
proof (induction es)
  case Nil
  show ?case
    by (cases p) (simp_all add: sail_rt_priv_of_def sail_rt_decision_of_def)
next
  case (Cons e es)
  show ?case
    by (cases "pmp_entry_check_scope e p kind addr width")
       (simp_all add: Cons.IH pmp_entry_check_scope_matches_sail_rt
                      sail_rt_decision_of_def)
qed

theorem pmp_check_raw_table_effective_matches_sail:
  "Pmp_raw_table_mw.pmpCheckRawTableEffective
     (sail_rt_raw_entries_of pas cfgs)
     (sail_rt_priv_of priv) mprv (sail_rt_priv_of mpp)
     (sail_rt_access_of kind) (int addr) (int width) =
   sail_rt_decision_of
     (pmp_check_scope_effective
       (decode_raw_pmp_table pas cfgs)
       priv mprv mpp kind addr width)"
  by (simp add: Pmp_raw_table_mw.pmpCheckRawTableEffective_def
                decodeRawPmpTable_matches
                pmp_check_scope_effective_def
                effective_privilege_matches_sail_rt
                pmp_check_scope_matches_sail_rt)

corollary raw_table_current_boot_sail_allows_low_priv_no_mprv:
  assumes low: "low_priv p"
      and inside: "addr + width \<le> (2::nat) ^ 64"
      and nonempty: "0 < width"
  shows "Pmp_raw_table_mw.pmpCheckRawTableEffective
           (sail_rt_raw_entries_of
             current_boot_raw_pmpaddrs current_boot_raw_pmpcfgs)
           (sail_rt_priv_of p) False (sail_rt_priv_of mpp)
           (sail_rt_access_of kind) (int addr) (int width) =
         Pmp_raw_table_mw_types.Scope_Allow"
  using raw_table_current_boot_allows_low_priv_no_mprv
          [OF low inside nonempty, of mpp kind]
  by (simp add: pmp_check_raw_table_effective_matches_sail
                sail_rt_decision_of_def)

corollary raw_table_corrected_boot_sail_isolates_effective_low_priv:
  fixes fw_start :: xlenbits and k :: nat
  defines "fw_base \<equiv> unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4"
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
      and eff_low: "low_priv (effective_privilege kind mprv mpp priv)"
      and ov: "ranges_overlap fw_base (fw_base + 2 ^ k) addr width"
  shows "Pmp_raw_table_mw.pmpCheckRawTableEffective
           (sail_rt_raw_entries_of
             (corrected_boot_raw_pmpaddrs fw_start k)
             corrected_boot_raw_pmpcfgs)
           (sail_rt_priv_of priv) mprv (sail_rt_priv_of mpp)
           (sail_rt_access_of kind) (int addr) (int width) =
         Pmp_raw_table_mw_types.Scope_Fault"
proof -
  have ov':
    "ranges_overlap
       (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4)
       (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4 + 2 ^ k)
       addr width"
    using ov by (simp add: fw_base_def)
  have fault:
    "pmp_check_scope_effective
       (decode_raw_pmp_table
          (corrected_boot_raw_pmpaddrs fw_start k)
          corrected_boot_raw_pmpcfgs)
       priv mprv mpp kind addr width = PMP_Fault"
    by (rule raw_table_corrected_boot_isolates_effective_low_priv[
        OF k_lo k_hi eff_low ov'])
  show ?thesis
    using fault
    by (simp add: pmp_check_raw_table_effective_matches_sail
                  sail_rt_decision_of_def)
qed

end
