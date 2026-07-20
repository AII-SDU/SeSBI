theory SeSBI_PMP_CheckScope
  imports SeSBI_PMP_BootSequence
begin

section \<open>Full-enough local PMP-check scope\<close>

text \<open>
  This theory upgrades the local PMP access-check model to match the key control
  flow of the official Sail @{text pmpCheck} function:

    * entries are checked in priority order;
    * @{const PMP_PartialMatch} faults immediately;
    * full @{const PMP_Match} allows iff RWX permits the access, or the effective
      privilege is Machine and the entry is not locked;
    * if no entry matches, Machine is allowed and S/U fault.

  It also adds the effective-privilege layer relevant to MPRV:

    * instruction fetch ignores MPRV;
    * data accesses use MPP as the effective privilege when MPRV is set.

  This remains a local model, not a theorem over the generated Sail
  @{text pmpCheck} definition.  The purpose is to make the local proof scope
  explicit and closer to Sail before attempting a generated-definition bridge.
\<close>

subsection \<open>Effective privilege, including MPRV\<close>

definition is_fetch :: "AccessKind \<Rightarrow> bool" where
  "is_fetch kind \<longleftrightarrow> kind = Execute"

definition effective_privilege ::
  "AccessKind \<Rightarrow> bool \<Rightarrow> PrivMode \<Rightarrow> PrivMode \<Rightarrow> PrivMode" where
  "effective_privilege kind mprv mpp priv =
     (if \<not> is_fetch kind \<and> mprv then mpp else priv)"

lemma effective_privilege_no_mprv:
  "effective_privilege kind False mpp priv = priv"
  by (simp add: effective_privilege_def)

lemma effective_privilege_fetch:
  "effective_privilege Execute mprv mpp priv = priv"
  by (simp add: effective_privilege_def is_fetch_def)

lemma effective_privilege_data_mprv:
  "kind \<noteq> Execute \<Longrightarrow> effective_privilege kind True mpp priv = mpp"
  by (cases kind) (simp_all add: effective_privilege_def is_fetch_def)

subsection \<open>Sail-shaped local pmpCheck\<close>

definition pmp_entry_check_scope ::
  "PmpEntry \<Rightarrow> PrivMode \<Rightarrow> AccessKind \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> PmpDecision" where
  "pmp_entry_check_scope e p kind addr width =
     (case pmpRangeMatch (pmp_bgn e) (pmp_en e) addr width of
        PMP_NoMatch \<Rightarrow> PMP_Continue
      | PMP_PartialMatch \<Rightarrow> PMP_Fault
      | PMP_Match \<Rightarrow>
          (if entry_allows e kind \<or> (p = Machine \<and> \<not> pmp_L e)
           then PMP_Allow else PMP_Fault))"

fun pmp_check_scope ::
  "PmpEntry list \<Rightarrow> PrivMode \<Rightarrow> AccessKind \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> PmpDecision" where
  "pmp_check_scope [] p _ _ _ = (if p = Machine then PMP_Allow else PMP_Fault)"
| "pmp_check_scope (e # es) p kind addr width =
     (case pmp_entry_check_scope e p kind addr width of
        PMP_Continue \<Rightarrow> pmp_check_scope es p kind addr width
      | PMP_Allow \<Rightarrow> PMP_Allow
      | PMP_Fault \<Rightarrow> PMP_Fault)"

definition pmp_check_scope_effective ::
  "PmpEntry list \<Rightarrow> PrivMode \<Rightarrow> bool \<Rightarrow> PrivMode \<Rightarrow>
   AccessKind \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> PmpDecision" where
  "pmp_check_scope_effective es priv mprv mpp kind addr width =
     pmp_check_scope es (effective_privilege kind mprv mpp priv) kind addr width"

subsection \<open>Key pmpCheck clauses\<close>

theorem scope_partial_match_fault_head:
  assumes "pmpRangeMatch (pmp_bgn e) (pmp_en e) addr width = PMP_PartialMatch"
  shows "pmp_check_scope (e # es) p kind addr width = PMP_Fault"
  using assms by (simp add: pmp_entry_check_scope_def)

theorem scope_machine_unlocked_full_match_allows:
  assumes unlocked: "\<not> pmp_L e"
      and match: "pmpRangeMatch (pmp_bgn e) (pmp_en e) addr width = PMP_Match"
  shows "pmp_check_scope (e # es) Machine kind addr width = PMP_Allow"
  using unlocked match by (simp add: pmp_entry_check_scope_def)

theorem scope_locked_disallowed_full_match_faults:
  assumes locked: "pmp_L e"
      and disallow: "\<not> entry_allows e kind"
      and match: "pmpRangeMatch (pmp_bgn e) (pmp_en e) addr width = PMP_Match"
  shows "pmp_check_scope (e # es) p kind addr width = PMP_Fault"
  using locked disallow match by (cases p) (simp_all add: pmp_entry_check_scope_def)

theorem scope_allow_entry_permits:
  assumes inside: "bgn \<le> addr" "addr + width \<le> en"
      and nonempty: "0 < width"
  shows "pmp_check_scope (allow_l0_entry bgn en # rest) p kind addr width = PMP_Allow"
proof -
  have match: "pmpRangeMatch bgn en addr width = PMP_Match"
    using inside nonempty by (simp add: pmpRangeMatch_Match_iff)
  show ?thesis
    using match by (cases kind)
       (simp_all add: pmp_entry_check_scope_def allow_l0_entry_def entry_allows_def)
qed

theorem scope_deny_l0_faults_effective_low_priv_overlap:
  assumes low: "low_priv p"
      and ov: "ranges_overlap bgn en addr width"
  shows "pmp_check_scope (deny_l0_entry bgn en # rest) p kind addr width = PMP_Fault"
  using low ov
  by (cases p; cases kind; cases "pmpRangeMatch bgn en addr width")
     (auto simp: pmp_entry_check_scope_def deny_l0_entry_def entry_allows_def
                 pmpRangeMatch_NoMatch_iff low_priv_def)

lemma all_entries_no_overlap_Cons:
  assumes "\<forall>e \<in> set (x # xs). \<not> ranges_overlap (pmp_bgn e) (pmp_en e) addr width"
  shows "\<not> ranges_overlap (pmp_bgn x) (pmp_en x) addr width"
    and "\<forall>e \<in> set xs. \<not> ranges_overlap (pmp_bgn e) (pmp_en e) addr width"
  using assms by auto

theorem scope_unmatched_low_priv_fault:
  assumes none: "\<forall>e \<in> set es. \<not> ranges_overlap (pmp_bgn e) (pmp_en e) addr width"
      and low: "low_priv p"
  shows "pmp_check_scope es p kind addr width = PMP_Fault"
  using none low
proof (induction es)
  case Nil
  then show ?case by (auto simp: low_priv_def)
next
  case (Cons e es)
  have head: "\<not> ranges_overlap (pmp_bgn e) (pmp_en e) addr width"
    using Cons.prems(1) by auto
  have tail: "\<forall>e\<in>set es. \<not> ranges_overlap (pmp_bgn e) (pmp_en e) addr width"
    using Cons.prems(1) by auto
  have no: "pmpRangeMatch (pmp_bgn e) (pmp_en e) addr width = PMP_NoMatch"
    using head by (simp add: pmpRangeMatch_NoMatch_iff)
  show ?case
    using Cons.IH[OF tail Cons.prems(2)] no
    by (simp add: pmp_entry_check_scope_def)
qed

theorem scope_unmatched_machine_allows:
  assumes none: "\<forall>e \<in> set es. \<not> ranges_overlap (pmp_bgn e) (pmp_en e) addr width"
  shows "pmp_check_scope es Machine kind addr width = PMP_Allow"
  using none
proof (induction es)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  have head: "\<not> ranges_overlap (pmp_bgn e) (pmp_en e) addr width"
    using Cons.prems by auto
  have tail: "\<forall>e\<in>set es. \<not> ranges_overlap (pmp_bgn e) (pmp_en e) addr width"
    using Cons.prems by auto
  have no: "pmpRangeMatch (pmp_bgn e) (pmp_en e) addr width = PMP_NoMatch"
    using head by (simp add: pmpRangeMatch_NoMatch_iff)
  show ?case
    using Cons.IH[OF tail] no by (simp add: pmp_entry_check_scope_def)
qed

subsection \<open>Boot-sequence corollaries in the upgraded scope\<close>

theorem current_boot_scope_allows_any_low_priv_access_inside_phys_no_mprv:
  assumes low: "low_priv p"
      and inside: "addr + width \<le> (2::nat) ^ 64"
      and nonempty: "0 < width"
  shows "pmp_check_scope_effective current_boot_entries p False mpp kind addr width = PMP_Allow"
proof -
  have "pmp_check_scope current_boot_entries p kind addr width = PMP_Allow"
    using scope_allow_entry_permits[of 0 addr width "(2::nat)^64"
                                      "[installed_entry PAYLOAD_START 18 PMP_RWX]" p kind]
          inside nonempty
    by (simp add: current_boot_entries_def)
  thus ?thesis by (simp add: pmp_check_scope_effective_def effective_privilege_no_mprv)
qed

theorem corrected_boot_scope_isolates_effective_low_priv:
  fixes fw_start :: xlenbits and k :: nat
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
      and eff_low: "low_priv (effective_privilege kind mprv mpp priv)"
      and ov: "ranges_overlap
                 (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4)
                 (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4 + 2 ^ k)
                 addr width"
  shows "pmp_check_scope_effective
           (bs_entries (corrected_boot_state old_mstatus fw_start k rest))
           priv mprv mpp kind addr width = PMP_Fault"
proof -
  define fw_base where "fw_base = unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4"
  have installed:
    "installed_entry fw_start k 0 = deny_l0_entry fw_base (fw_base + 2 ^ k)"
    using installed_deny[OF k_lo k_hi, of fw_start] fw_base_def by simp
  have ov': "ranges_overlap fw_base (fw_base + 2 ^ k) addr width"
    using ov by (simp add: fw_base_def)
  have fault:
    "pmp_check_scope
       (deny_l0_entry fw_base (fw_base + 2 ^ k) # rest)
       (effective_privilege kind mprv mpp priv) kind addr width = PMP_Fault"
    by (rule scope_deny_l0_faults_effective_low_priv_overlap[OF eff_low ov'])
  show ?thesis
    using fault
    by (simp add: pmp_check_scope_effective_def corrected_boot_state_def
                  corrected_boot_entries_def installed)
qed

corollary corrected_boot_scope_isolates_low_priv_no_mprv:
  fixes fw_start :: xlenbits and k :: nat
  defines "fw_base \<equiv> unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4"
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
      and low: "low_priv p"
      and ov: "ranges_overlap fw_base (fw_base + 2 ^ k) addr width"
  shows "pmp_check_scope_effective
           (bs_entries (corrected_boot_state old_mstatus fw_start k rest))
           p False mpp kind addr width = PMP_Fault"
proof -
  have eff: "low_priv (effective_privilege kind False mpp p)"
    using low by (simp add: effective_privilege_no_mprv)
  have ov':
    "ranges_overlap
       (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4)
       (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4 + 2 ^ k)
       addr width"
    using ov by (simp add: fw_base_def)
  show ?thesis
    by (rule corrected_boot_scope_isolates_effective_low_priv[OF k_lo k_hi eff ov'])
qed

corollary corrected_boot_scope_isolates_machine_data_with_mprv_to_low_mpp:
  fixes fw_start :: xlenbits and k :: nat
  defines "fw_base \<equiv> unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4"
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
      and data: "kind \<noteq> Execute"
      and low_mpp: "low_priv mpp"
      and ov: "ranges_overlap fw_base (fw_base + 2 ^ k) addr width"
  shows "pmp_check_scope_effective
           (bs_entries (corrected_boot_state old_mstatus fw_start k rest))
           Machine True mpp kind addr width = PMP_Fault"
proof -
  have eff: "low_priv (effective_privilege kind True mpp Machine)"
    using data low_mpp by (simp add: effective_privilege_data_mprv)
  have ov':
    "ranges_overlap
       (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4)
       (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4 + 2 ^ k)
       addr width"
    using ov by (simp add: fw_base_def)
  show ?thesis
    by (rule corrected_boot_scope_isolates_effective_low_priv[OF k_lo k_hi eff ov'])
qed

corollary corrected_boot_scope_execute_ignores_mprv:
  "pmp_check_scope_effective es priv mprv mpp Execute addr width =
   pmp_check_scope es priv Execute addr width"
  by (simp add: pmp_check_scope_effective_def effective_privilege_fetch)

end
