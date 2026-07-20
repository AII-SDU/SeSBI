theory SeSBI_PMP_Isolation
  imports SeSBI_PMP_NAPOT
begin

datatype PrivMode = Machine | Supervisor | User
datatype AccessKind = Read | Write | Execute
datatype PmpDecision = PMP_Continue | PMP_Allow | PMP_Fault

record PmpEntry =
  pmp_bgn :: nat
  pmp_en :: nat
  pmp_R :: bool
  pmp_W :: bool
  pmp_X :: bool
  pmp_L :: bool

definition low_priv :: "PrivMode \<Rightarrow> bool" where
  "low_priv p \<longleftrightarrow> p = Supervisor \<or> p = User"

text \<open>Right-open access range overlap: [addr, addr + width) intersects [bgn, en).\<close>
definition ranges_overlap :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "ranges_overlap bgn en addr width \<longleftrightarrow> addr < en \<and> bgn < addr + width"

text \<open>
  A high-priority L=0 deny entry: it constrains S/U accesses but trusted M-mode
  bypasses it.  RWX are all false, so a full match faults; a partial match also
  faults according to the Sail PMP range-matching rule.
\<close>
definition deny_l0_entry_check ::
  "PrivMode \<Rightarrow> AccessKind \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> PmpDecision" where
  "deny_l0_entry_check p _ bgn en addr width =
     (if low_priv p then
        (case pmpRangeMatch bgn en addr width of
           PMP_NoMatch \<Rightarrow> PMP_Continue
         | PMP_PartialMatch \<Rightarrow> PMP_Fault
         | PMP_Match \<Rightarrow> PMP_Fault)
      else PMP_Continue)"

definition entry_allows :: "PmpEntry \<Rightarrow> AccessKind \<Rightarrow> bool" where
  "entry_allows e kind =
     (case kind of
        Read \<Rightarrow> pmp_R e
      | Write \<Rightarrow> pmp_W e
      | Execute \<Rightarrow> pmp_X e)"

definition pmp_entry_check ::
  "PmpEntry \<Rightarrow> PrivMode \<Rightarrow> AccessKind \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> PmpDecision" where
  "pmp_entry_check e p kind addr width =
     (if p = Machine \<and> \<not> pmp_L e then PMP_Continue
      else
        (case pmpRangeMatch (pmp_bgn e) (pmp_en e) addr width of
           PMP_NoMatch \<Rightarrow> PMP_Continue
         | PMP_PartialMatch \<Rightarrow> PMP_Fault
         | PMP_Match \<Rightarrow> (if entry_allows e kind then PMP_Allow else PMP_Fault)))"

fun pmp_check_entries ::
  "PmpEntry list \<Rightarrow> PrivMode \<Rightarrow> AccessKind \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> PmpDecision" where
  "pmp_check_entries [] p _ _ _ = (if low_priv p then PMP_Fault else PMP_Allow)"
| "pmp_check_entries (e # es) p kind addr width =
     (case pmp_entry_check e p kind addr width of
        PMP_Continue \<Rightarrow> pmp_check_entries es p kind addr width
      | PMP_Allow \<Rightarrow> PMP_Allow
      | PMP_Fault \<Rightarrow> PMP_Fault)"

definition deny_l0_entry :: "nat \<Rightarrow> nat \<Rightarrow> PmpEntry" where
  "deny_l0_entry bgn en =
     \<lparr> pmp_bgn = bgn, pmp_en = en,
       pmp_R = False, pmp_W = False, pmp_X = False, pmp_L = False \<rparr>"

definition allow_l0_entry :: "nat \<Rightarrow> nat \<Rightarrow> PmpEntry" where
  "allow_l0_entry bgn en =
     \<lparr> pmp_bgn = bgn, pmp_en = en,
       pmp_R = True, pmp_W = True, pmp_X = True, pmp_L = False \<rparr>"

lemma pmpRangeMatch_NoMatch_iff:
  "pmpRangeMatch bgn en addr width = PMP_NoMatch
   \<longleftrightarrow> \<not> ranges_overlap bgn en addr width"
  by (auto simp: pmpRangeMatch_def ranges_overlap_def)

lemma pmpRangeMatch_overlaps_not_NoMatch:
  "ranges_overlap bgn en addr width
   \<Longrightarrow> pmpRangeMatch bgn en addr width \<noteq> PMP_NoMatch"
  by (simp add: pmpRangeMatch_NoMatch_iff)

theorem deny_l0_faults_any_low_priv_overlap:
  assumes low: "low_priv p"
      and ov: "ranges_overlap bgn en addr width"
  shows "deny_l0_entry_check p kind bgn en addr width = PMP_Fault"
  using low ov
  by (auto simp: deny_l0_entry_check_def pmpRangeMatch_NoMatch_iff
           split: PmpMatch.splits)

corollary deny_l0_faults_fully_inside:
  assumes low: "low_priv p"
      and inside: "bgn \<le> addr" "addr + width \<le> en"
      and nonempty: "0 < width"
  shows "deny_l0_entry_check p kind bgn en addr width = PMP_Fault"
proof -
  have "ranges_overlap bgn en addr width"
    using inside nonempty by (auto simp: ranges_overlap_def)
  with low show ?thesis by (rule deny_l0_faults_any_low_priv_overlap)
qed

lemma pmp_entry_check_deny_l0_eq:
  "pmp_entry_check (deny_l0_entry bgn en) p kind addr width =
   deny_l0_entry_check p kind bgn en addr width"
  by (cases p; cases kind; cases "pmpRangeMatch bgn en addr width")
     (auto simp: pmp_entry_check_def deny_l0_entry_def deny_l0_entry_check_def
                 entry_allows_def low_priv_def)

lemma pmp_check_entries_fault_head:
  assumes "pmp_entry_check e p kind addr width = PMP_Fault"
  shows "pmp_check_entries (e # es) p kind addr width = PMP_Fault"
  using assms by simp

theorem deny_l0_first_entry_faults_overlap:
  assumes low: "low_priv p"
      and ov: "ranges_overlap bgn en addr width"
  shows "pmp_check_entries (deny_l0_entry bgn en # es) p kind addr width = PMP_Fault"
proof -
  have "pmp_entry_check (deny_l0_entry bgn en) p kind addr width = PMP_Fault"
    using deny_l0_faults_any_low_priv_overlap[OF low ov]
    by (simp add: pmp_entry_check_deny_l0_eq)
  thus ?thesis by (rule pmp_check_entries_fault_head)
qed

corollary lower_priority_allow_cannot_override_deny_overlap:
  assumes low: "low_priv p"
      and ov: "ranges_overlap fw_bgn fw_en addr width"
  shows "pmp_check_entries
           [deny_l0_entry fw_bgn fw_en, allow_l0_entry allow_bgn allow_en]
           p kind addr width = PMP_Fault"
  by (rule deny_l0_first_entry_faults_overlap[OF low ov])

corollary deny_l0_faults_encoded_napot_overlap:
  fixes start :: xlenbits and k :: nat
  defines "base \<equiv> unat (drop_bit 2 start AND NOT (mask (k-2))) * 4"
  assumes k_lo: "3 \<le> k"
      and k_hi: "k \<le> 63"
      and low: "low_priv p"
      and ov: "ranges_overlap base (base + 2 ^ k) addr width"
  shows "deny_l0_entry_check p kind
           (fst (napot_region (pmp_encode_napot start k)))
           (snd (napot_region (pmp_encode_napot start k)))
           addr width = PMP_Fault"
proof -
  have reg: "napot_region (pmp_encode_napot start k) = (base, base + 2 ^ k)"
    using napot_interval_correct[OF k_lo k_hi, of start] base_def by simp
  have "deny_l0_entry_check p kind base (base + 2 ^ k) addr width = PMP_Fault"
    by (rule deny_l0_faults_any_low_priv_overlap[OF low ov])
  thus ?thesis by (simp add: reg)
qed

end
