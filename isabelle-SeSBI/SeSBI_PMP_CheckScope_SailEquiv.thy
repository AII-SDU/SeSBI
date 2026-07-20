theory SeSBI_PMP_CheckScope_SailEquiv
  imports
    SeSBI_PMP_CheckScope
    "sail-generated/Pmp_check_scope_mw"
begin

section \<open>Generated Sail bridge for the PMP-check scope\<close>

text \<open>
  This theory connects the local interval-entry PMP-check model from
  SeSBI_PMP_CheckScope to a Sail/Lem-generated definition produced from
  \<open>sail-generated/pmp_check_scope_mw.sail\<close>.

  The generated Sail source is intentionally a pure subset: it keeps the
  priority order, partial-match fault, RWX permission test, unlocked Machine
  bypass, no-match behavior, and MPRV effective-privilege rule, but it takes
  already-decoded interval entries.  Raw PMP address modes and the full
  sail-riscv register state remain outside this bridge.
\<close>

definition sail_match_of ::
  "PmpMatch \<Rightarrow> Pmp_check_scope_mw_types.pmpAddrMatch" where
  "sail_match_of m =
     (case m of
        SeSBI_PMP_NAPOT.PMP_NoMatch \<Rightarrow> Pmp_check_scope_mw_types.PMP_NoMatch
      | SeSBI_PMP_NAPOT.PMP_PartialMatch \<Rightarrow> Pmp_check_scope_mw_types.PMP_PartialMatch
      | SeSBI_PMP_NAPOT.PMP_Match \<Rightarrow> Pmp_check_scope_mw_types.PMP_Match)"

definition sail_priv_of ::
  "PrivMode \<Rightarrow> Pmp_check_scope_mw_types.PmpScopePriv" where
  "sail_priv_of p =
     (case p of
        User \<Rightarrow> Scope_User
      | Supervisor \<Rightarrow> Scope_Supervisor
      | Machine \<Rightarrow> Scope_Machine)"

definition sail_access_of ::
  "AccessKind \<Rightarrow> Pmp_check_scope_mw_types.PmpScopeAccess" where
  "sail_access_of kind =
     (case kind of
        Read \<Rightarrow> Scope_Read
      | Write \<Rightarrow> Scope_Write
      | Execute \<Rightarrow> Scope_Execute)"

definition sail_decision_of ::
  "PmpDecision \<Rightarrow> Pmp_check_scope_mw_types.PmpScopeDecision" where
  "sail_decision_of d =
     (case d of
        PMP_Continue \<Rightarrow> Scope_Continue
      | PMP_Allow \<Rightarrow> Scope_Allow
      | PMP_Fault \<Rightarrow> Scope_Fault)"

definition sail_entry_of ::
  "PmpEntry \<Rightarrow> Pmp_check_scope_mw_types.PmpScopeEntry" where
  "sail_entry_of e =
     \<lparr> PmpScopeEntry_scope_bgn = int (pmp_bgn e),
       PmpScopeEntry_scope_en = int (pmp_en e),
       PmpScopeEntry_scope_R = pmp_R e,
       PmpScopeEntry_scope_W = pmp_W e,
       PmpScopeEntry_scope_X = pmp_X e,
       PmpScopeEntry_scope_L = pmp_L e \<rparr>"

lemma pmpRangeMatch_matches_sail:
  "Pmp_check_scope_mw.pmpRangeMatch (int bgn) (int en) (int addr) (int width) =
   sail_match_of (SeSBI_PMP_NAPOT.pmpRangeMatch bgn en addr width)"
  by (auto simp: Pmp_check_scope_mw.pmpRangeMatch_def
                 SeSBI_PMP_NAPOT.pmpRangeMatch_def
                 sail_match_of_def)

lemma pmpCheckRWX_scope_matches_entry_allows:
  "Pmp_check_scope_mw.pmpCheckRWX_scope (sail_entry_of e) (sail_access_of kind) =
   entry_allows e kind"
  by (cases kind)
     (simp_all add: sail_entry_of_def sail_access_of_def entry_allows_def)

lemma pmpLocked_scope_matches:
  "Pmp_check_scope_mw.pmpLocked_scope (sail_entry_of e) = pmp_L e"
  by (simp add: sail_entry_of_def Pmp_check_scope_mw.pmpLocked_scope_def)

lemma effective_privilege_matches_sail:
  "Pmp_check_scope_mw.effectivePrivilegeScope
     (sail_access_of kind) mprv (sail_priv_of mpp) (sail_priv_of priv) =
   sail_priv_of (effective_privilege kind mprv mpp priv)"
  by (cases kind; cases mprv)
     (simp_all add: effective_privilege_def is_fetch_def
                    sail_access_of_def sail_priv_of_def)

lemma pmp_entry_check_scope_matches_sail:
  "Pmp_check_scope_mw.pmpEntryCheckScope
     (sail_entry_of e) (sail_priv_of p) (sail_access_of kind) (int addr) (int width) =
   sail_decision_of (pmp_entry_check_scope e p kind addr width)"
proof -
  have range:
    "Pmp_check_scope_mw.pmpRangeMatch
       (PmpScopeEntry_scope_bgn (sail_entry_of e))
       (PmpScopeEntry_scope_en (sail_entry_of e))
       (int addr) (int width) =
     sail_match_of (SeSBI_PMP_NAPOT.pmpRangeMatch (pmp_bgn e) (pmp_en e) addr width)"
    by (simp add: sail_entry_of_def pmpRangeMatch_matches_sail)
  show ?thesis
    using range
    by (cases "SeSBI_PMP_NAPOT.pmpRangeMatch (pmp_bgn e) (pmp_en e) addr width";
        cases p; cases kind)
       (simp_all add: Pmp_check_scope_mw.pmpEntryCheckScope_def
                      pmp_entry_check_scope_def sail_match_of_def
                      sail_priv_of_def sail_access_of_def sail_decision_of_def
                      sail_entry_of_def
                      Pmp_check_scope_mw.pmpLocked_scope_def
                      pmpCheckRWX_scope_matches_entry_allows
                      pmpLocked_scope_matches entry_allows_def)
qed

termination Pmp_check_scope_mw.pmpCheckScope
  by lexicographic_order

theorem pmp_check_scope_matches_sail:
  "Pmp_check_scope_mw.pmpCheckScope
     (map sail_entry_of es) (sail_priv_of p) (sail_access_of kind) (int addr) (int width) =
   sail_decision_of (pmp_check_scope es p kind addr width)"
proof (induction es)
  case Nil
  show ?case by (cases p) (simp_all add: sail_priv_of_def sail_decision_of_def)
next
  case (Cons e es)
  show ?case
    by (cases "pmp_entry_check_scope e p kind addr width")
       (simp_all add: Cons.IH pmp_entry_check_scope_matches_sail
                      sail_decision_of_def)
qed

theorem pmp_check_scope_effective_matches_sail:
  "Pmp_check_scope_mw.pmpCheckScopeEffective
     (map sail_entry_of es) (sail_priv_of priv) mprv (sail_priv_of mpp)
     (sail_access_of kind) (int addr) (int width) =
   sail_decision_of (pmp_check_scope_effective es priv mprv mpp kind addr width)"
  by (simp add: Pmp_check_scope_mw.pmpCheckScopeEffective_def
                pmp_check_scope_effective_def
                effective_privilege_matches_sail
                pmp_check_scope_matches_sail)

corollary current_boot_sail_scope_allows_any_low_priv_access_inside_phys_no_mprv:
  assumes low: "low_priv p"
      and inside: "addr + width \<le> (2::nat) ^ 64"
      and nonempty: "0 < width"
  shows "Pmp_check_scope_mw.pmpCheckScopeEffective
           (map sail_entry_of current_boot_entries)
           (sail_priv_of p) False (sail_priv_of mpp)
           (sail_access_of kind) (int addr) (int width) = Scope_Allow"
  using current_boot_scope_allows_any_low_priv_access_inside_phys_no_mprv
          [OF low inside nonempty, of mpp kind]
  by (simp add: pmp_check_scope_effective_matches_sail sail_decision_of_def)

corollary corrected_boot_sail_scope_isolates_effective_low_priv:
  fixes fw_start :: xlenbits and k :: nat
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
      and eff_low: "low_priv (effective_privilege kind mprv mpp priv)"
      and ov: "ranges_overlap
                 (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4)
                 (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4 + 2 ^ k)
                 addr width"
  shows "Pmp_check_scope_mw.pmpCheckScopeEffective
           (map sail_entry_of (bs_entries (corrected_boot_state old_mstatus fw_start k rest)))
           (sail_priv_of priv) mprv (sail_priv_of mpp)
           (sail_access_of kind) (int addr) (int width) = Scope_Fault"
  using corrected_boot_scope_isolates_effective_low_priv[OF k_lo k_hi eff_low ov,
          of old_mstatus rest]
  by (simp add: pmp_check_scope_effective_matches_sail sail_decision_of_def)

end
