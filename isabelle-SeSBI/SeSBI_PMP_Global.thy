theory SeSBI_PMP_Global
  imports Main
begin

(* ========================================================================= *)
(* SECTION 1: BASIC DEFINITIONS                                              *)
(* ========================================================================= *)

(* 1.1 Basic Types *)
type_synonym reg         = int
type_synonym state       = "reg \<Rightarrow> int"
type_synonym reg_index   = nat
type_synonym address     = nat
type_synonym size        = nat
type_synonym protection  = nat

(* 1.2 Constants *)
definition pmp_RWX :: nat where
  "pmp_RWX \<equiv> 7"  
  (* Read(1) + Write(2) + Execute(4) = 7 *)

(* PMP domain constants.
   The current SeSBI firmware and model support 16 PMP entries (indices 0..15).
   - PMP_ENTRY_COUNT: the total number of entries (= C macro MAX_CSR_PMP = 16).
   - MAX_PMP_INDEX:   the greatest valid index (= PMP_ENTRY_COUNT - 1 = 15).
   The C source uses MAX_CSR_PMP as the exclusive bound (idx < MAX_CSR_PMP).
   The Dafny model uses ValidPmpIndex(idx) { idx < 16 }.
   Both are equivalent to idx <= MAX_PMP_INDEX. *)
definition PMP_ENTRY_COUNT :: nat where
  "PMP_ENTRY_COUNT \<equiv> 16"

definition MAX_PMP_INDEX :: nat where
  "MAX_PMP_INDEX \<equiv> PMP_ENTRY_COUNT - 1"

(* Legacy alias kept for minimal downstream breakage; prefer PMP_ENTRY_COUNT. *)
abbreviation MAX_CSR_PMP :: nat where
  "MAX_CSR_PMP \<equiv> PMP_ENTRY_COUNT"

definition PMP_SHIFT :: nat where
  "PMP_SHIFT \<equiv> 2"

(* 1.3 PMP Entry Structure *)
type_synonym pmp_entry = "address \<times> size \<times> protection"

(* 1.4 Power-of-two check
   NOTE: 原本用 (n AND (n - 1) = 0) 的位运算需要额外位操作库。
   这里我们用 n = 2^k 的数学定义就够了。 *)
definition is_power_of_two :: "nat \<Rightarrow> bool" where
  "is_power_of_two n \<equiv> (n > 0 \<and> (\<exists>k. n = 2 ^ k))"

(* 1.5 PMP Entry Validity *)
definition valid_pmp_entry :: "pmp_entry \<Rightarrow> bool" where
  "valid_pmp_entry e \<equiv> 
    (case e of (addr, sz, prot) \<Rightarrow> 
       addr + sz \<le> 2 ^ (64 :: nat) \<and> 
       prot \<le> pmp_RWX \<and>
       (sz = 0 \<or> is_power_of_two sz))"

(* 1.6 PMP Configuration List Validity *)
definition valid_pmp_config :: "pmp_entry list \<Rightarrow> bool" where
  "valid_pmp_config pmps \<equiv>
     length pmps = PMP_ENTRY_COUNT \<and>
     (\<forall>e \<in> set pmps. valid_pmp_entry e)"

(* Relates the entry-count and maximum-index formulations. *)
lemma pmp_count_equivalence: "MAX_PMP_INDEX + 1 = PMP_ENTRY_COUNT"
  unfolding MAX_PMP_INDEX_def PMP_ENTRY_COUNT_def by simp

lemma pmp_index_bound_equiv: "(idx \<le> MAX_PMP_INDEX) = (idx < PMP_ENTRY_COUNT)"
  unfolding MAX_PMP_INDEX_def PMP_ENTRY_COUNT_def by auto

(* 1.7 SBI Set PMP
   如果 idx 合法且新 entry 合法，则更新第 idx 项；
   否则保持不变。
   list_update xs[i := v] 的语义是：
   - 若 i < length xs，则覆盖第 i 项；
   - 若 i \<ge> length xs，则返回 xs 本身。
 *)
definition sbi_set_pmp :: "reg_index \<Rightarrow> address \<Rightarrow> size \<Rightarrow> protection 
                           \<Rightarrow> pmp_entry list \<Rightarrow> pmp_entry list" where
  "sbi_set_pmp idx addr sz prot pmps \<equiv> 
    if idx < length pmps \<and> valid_pmp_entry (addr, sz, prot) 
    then pmps[idx := (addr, sz, prot)]
    else pmps"
(* ========================================================================= *)
(* SECTION 2: SYSTEM MODEL                                                   *)
(* ========================================================================= *)

(* 2.1 System State Record *)
record system_state =
  pmp_entries :: "pmp_entry list"
  timer       :: nat
  mstatus     :: nat
  mie         :: nat
  sp          :: int
  mscratch    :: int
  (* 还可以扩展更多寄存器/状态字段 *)

(* The C delegate_traps() routine writes mideleg and medeleg, which are outside
   this configuration-level state projection, and does not write mstatus.
   Therefore delegation is modeled as the identity on this projection. The
   allowed mask remains abstract, so preservation holds for any selected mask. *)
definition csr_mask_ok :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "csr_mask_ok value allowed_mask \<equiv>
     (\<forall>n. bit value n \<longrightarrow> bit allowed_mask n)"

consts mstatus_allowed_mask :: nat

definition delegate_traps :: "system_state \<Rightarrow> system_state" where
  "delegate_traps s \<equiv> s"

lemma delegate_traps_preserves_mstatus:
  assumes "csr_mask_ok (mstatus s) mstatus_allowed_mask"
  shows "csr_mask_ok (mstatus (delegate_traps s))
                     mstatus_allowed_mask"
  using assms by (simp add: delegate_traps_def)

(* 2.2 SBI Operation Datatype *)
datatype sbi_operation = 
    SetTimer nat
  | SetPMP reg_index address size protection
  | ConsolePutchar char
  | ConsoleGetchar
  | SendIPI nat
  | TrapInit
  | SystemReset
  | NoOp

(* 2.3 Initial State Constructor *)
definition init_system_state :: system_state where
  "init_system_state \<equiv>
     \<lparr> pmp_entries = replicate PMP_ENTRY_COUNT (0, 0, 0),
       timer       = 0,
       mstatus     = 0,
       mie         = 0,
       sp          = 0,
       mscratch    = 0 \<rparr>"

(* 2.4 System Invariant:
   - PMP 配置整体合法
   - 关键控制寄存器在 64-bit 范围内
   注意：这里我们只约束 timer/mstatus/mie，不去约束 sp/mscratch，
   因为 sp/mscratch 的安全性通常在 trap/init 的单独定理里证明。
 *)
definition system_invariant :: "system_state \<Rightarrow> bool" where
  "system_invariant s \<equiv> 
     valid_pmp_config (pmp_entries s) \<and>
     timer s   < 2 ^ (64 :: nat) \<and>
     mstatus s < 2 ^ (64 :: nat) \<and>
     mie s     < 2 ^ (64 :: nat)"

(* 2.5 SBI Operation Execution Semantics
   关键修正：SetTimer 不再直接写 t，而是写 (t mod 2^64)。
   这样才能保证 timer < 2^64 恒成立，从而不变式可证明保持。 *)
fun execute_sbi :: "sbi_operation \<Rightarrow> system_state \<Rightarrow> system_state" where
  "execute_sbi (SetTimer t) s =
     s\<lparr> timer := t mod 2 ^ (64 :: nat) \<rparr>" |

  "execute_sbi (SetPMP idx addr sz prot) s =
     s\<lparr> pmp_entries := sbi_set_pmp idx addr sz prot (pmp_entries s) \<rparr>" |

  "execute_sbi (ConsolePutchar c) s = s" |

  "execute_sbi ConsoleGetchar s = s" |

  "execute_sbi (SendIPI target) s = s" |

  "execute_sbi TrapInit s =
     s\<lparr> mie := 0 \<rparr>" |

  "execute_sbi SystemReset s = init_system_state" |

  "execute_sbi NoOp s = s"

(* 2.6 Execute Multiple Operations (left fold of execute_sbi) *)
definition execute_sbi_seq :: "sbi_operation list \<Rightarrow> system_state \<Rightarrow> system_state" where
  "execute_sbi_seq ops s \<equiv> fold execute_sbi ops s"

(* ========================================================================= *)
(* SECTION 3: AUXILIARY LEMMAS                                               *)
(* ========================================================================= *)

(* 3.1 Initial State Satisfies Invariant *)
lemma init_state_invariant:
  "system_invariant init_system_state"
proof -
  have "valid_pmp_config (pmp_entries init_system_state)"
  proof -
    have len: "length (pmp_entries init_system_state) = PMP_ENTRY_COUNT"
      unfolding init_system_state_def PMP_ENTRY_COUNT_def by simp
    have all_valid: "\<forall>e \<in> set (pmp_entries init_system_state). valid_pmp_entry e"
    proof
      fix e assume "e \<in> set (pmp_entries init_system_state)"
      then have "e = (0, 0, 0)" 
        unfolding init_system_state_def by auto
      thus "valid_pmp_entry e"
        unfolding valid_pmp_entry_def pmp_RWX_def by auto
    qed
    show ?thesis
      unfolding valid_pmp_config_def using len all_valid by simp
  qed
  moreover have "timer init_system_state < 2^64"
    unfolding init_system_state_def by simp
  moreover have "mstatus init_system_state < 2^64"
    unfolding init_system_state_def by simp
  moreover have "mie init_system_state < 2^64"
    unfolding init_system_state_def by simp
  ultimately show ?thesis
    unfolding system_invariant_def by simp
qed


(* 3.2 Updating one PMP entry (within bounds) preserves config validity *)
lemma valid_pmp_config_update:
  assumes valid_old: "valid_pmp_config pmps"
      and valid_new: "valid_pmp_entry new_entry"
      and in_bounds: "idx < length pmps"
  shows "valid_pmp_config (pmps[idx := new_entry])"
proof -
  have len: "length (pmps[idx := new_entry]) = length pmps"
    by simp
  have all_valid: "\<forall>e \<in> set (pmps[idx := new_entry]). valid_pmp_entry e"
  proof
    fix e assume "e \<in> set (pmps[idx := new_entry])"
    then obtain i where "i < length pmps" and "e = (pmps[idx := new_entry]) ! i"
      by (metis in_set_conv_nth len)
    show "valid_pmp_entry e"
    proof (cases "i = idx")
      case True
      then show ?thesis 
        using valid_new \<open>e = (pmps[idx := new_entry]) ! i\<close> in_bounds by simp
    next
      case False
      then have "e = pmps ! i"
        using \<open>e = (pmps[idx := new_entry]) ! i\<close> \<open>i < length pmps\<close> by simp
      thus ?thesis
        using valid_old \<open>i < length pmps\<close> 
        unfolding valid_pmp_config_def by (simp add: nth_mem)
    qed
  qed
  show ?thesis
    unfolding valid_pmp_config_def
    using len all_valid valid_old unfolding valid_pmp_config_def by simp
qed


(* 3.3 list_update at the list length is a no-op *)
lemma list_update_at_length [simp]:
  "xs[length xs := x] = xs"
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  (* length (a # xs) = Suc (length xs), and list_update recurses *)
  then show ?case by simp
qed

lemma valid_pmp_config_update_any:
  assumes cfg_ok:   "valid_pmp_config pmps"
      and idx_le:   "idx \<le> length pmps"
      and entry_ok: "valid_pmp_entry e"
  shows "valid_pmp_config (pmps[idx := e])"
proof (cases "idx < length pmps")
  case True
  then show ?thesis
    using valid_pmp_config_update[OF cfg_ok entry_ok True] by simp
next
  case False
  from idx_le False have idx_eq: "idx = length pmps"
    by simp

  have "pmps[idx := e] = pmps"
    using idx_eq by simp  (* uses your [simp] lemma list_update_at_length *)
  thus ?thesis
    using cfg_ok by simp
qed

(* 3.4 sbi_set_pmp preserves validity of the PMP configuration *)
lemma sbi_set_pmp_preserves_validity:
  assumes valid: "valid_pmp_config pmps"
  shows "valid_pmp_config (sbi_set_pmp idx addr sz prot pmps)"
proof (cases "idx < length pmps")
  case True
  note idx_in_bounds = this
  show ?thesis
  proof (cases "valid_pmp_entry (addr, sz, prot)")
    case True
    note entry_valid = this
    
    (* Both conditions satisfied: perform update *)
    have "sbi_set_pmp idx addr sz prot pmps = pmps[idx := (addr, sz, prot)]"
      unfolding sbi_set_pmp_def using idx_in_bounds entry_valid by simp
    
    moreover have "valid_pmp_config (pmps[idx := (addr, sz, prot)])"
      using valid_pmp_config_update[OF valid entry_valid idx_in_bounds] .
    
    ultimately show ?thesis by simp
  next
    case False
    (* Invalid entry: no update *)
    then have "sbi_set_pmp idx addr sz prot pmps = pmps"
      unfolding sbi_set_pmp_def by simp
    thus ?thesis using valid by simp
  qed
next
  case False
  (* Out of bounds index: no update *)
  then have "sbi_set_pmp idx addr sz prot pmps = pmps"
    unfolding sbi_set_pmp_def by simp
  thus ?thesis using valid by simp
qed

(* 引理1：非PMP非Reset操作不改变PMP *)
lemma non_pmp_non_reset_preserves_pmp:
  assumes "\<forall>idx addr sz prot. op \<noteq> SetPMP idx addr sz prot"  (* 全称量化 *)
      and "op \<noteq> SystemReset"
  shows "pmp_entries (execute_sbi op s) = pmp_entries s"
  using assms by (cases op; auto)

(* 引理2：Reset重置PMP到初始状态 *)
lemma reset_pmp_to_init:
  "execute_sbi SystemReset s = init_system_state"
  by simp

(* 推论：Reset后PMP有效（如果初始状态有效）*)
lemma reset_pmp_valid:
  "pmp_entries (execute_sbi SystemReset s) = pmp_entries init_system_state"
  by simp

(* ========================================================================= *)
(* SECTION 4: INVARIANT PRESERVATION                                         *)
(* ========================================================================= *)

(* 4.1 Single Operation Preserves Invariant *)
theorem sbi_operation_preserves_invariant:
  assumes inv: "system_invariant s"
  shows "system_invariant (execute_sbi op s)"
proof (cases op)
  case (SetTimer t)
  have entries_same:
    "pmp_entries (execute_sbi op s) = pmp_entries s"
    unfolding SetTimer by simp
  from inv have pmp_ok: "valid_pmp_config (pmp_entries s)"
    unfolding system_invariant_def by simp
  have timer_ok:
    "timer (execute_sbi op s) < 2 ^ (64 :: nat)"
    unfolding SetTimer by simp
  have mstatus_ok:
    "mstatus (execute_sbi op s) < 2 ^ (64 :: nat)"
    unfolding SetTimer using inv unfolding system_invariant_def by simp
  have mie_ok:
    "mie (execute_sbi op s) < 2 ^ (64 :: nat)"
    unfolding SetTimer using inv unfolding system_invariant_def by simp
  from pmp_ok entries_same timer_ok mstatus_ok mie_ok
  show ?thesis
    unfolding system_invariant_def by simp
next
  case (SetPMP idx addr sz prot)
  from inv have old_pmp:
    "valid_pmp_config (pmp_entries s)"
    unfolding system_invariant_def by simp
  have new_pmp:
    "valid_pmp_config (sbi_set_pmp idx addr sz prot (pmp_entries s))"
    using sbi_set_pmp_preserves_validity[OF old_pmp] .
  have entries_eq:
    "pmp_entries (execute_sbi op s)
     = sbi_set_pmp idx addr sz prot (pmp_entries s)"
    unfolding SetPMP by simp
  have timer_ok:
    "timer (execute_sbi op s) < 2 ^ (64 :: nat)"
    unfolding SetPMP using inv unfolding system_invariant_def by simp
  have mstatus_ok:
    "mstatus (execute_sbi op s) < 2 ^ (64 :: nat)"
    unfolding SetPMP using inv unfolding system_invariant_def by simp
  have mie_ok:
    "mie (execute_sbi op s) < 2 ^ (64 :: nat)"
    unfolding SetPMP using inv unfolding system_invariant_def by simp
  from new_pmp entries_eq timer_ok mstatus_ok mie_ok
  show ?thesis
    unfolding system_invariant_def by simp
next
  case (ConsolePutchar c)
  then show ?thesis
    using inv unfolding system_invariant_def by simp
next
  case ConsoleGetchar
  then show ?thesis
    using inv unfolding system_invariant_def by simp
next
  case (SendIPI target)
  then show ?thesis
    using inv unfolding system_invariant_def by simp
next
  case TrapInit
  have entries_same:
    "pmp_entries (execute_sbi op s) = pmp_entries s"
    unfolding TrapInit by simp
  from inv have pmp_ok:
    "valid_pmp_config (pmp_entries s)"
    unfolding system_invariant_def by simp
  have timer_ok:
    "timer (execute_sbi op s) < 2 ^ (64 :: nat)"
    unfolding TrapInit using inv unfolding system_invariant_def by simp
  have mstatus_ok:
    "mstatus (execute_sbi op s) < 2 ^ (64 :: nat)"
    unfolding TrapInit using inv unfolding system_invariant_def by simp
  have mie_ok:
    "mie (execute_sbi op s) < 2 ^ (64 :: nat)"
    unfolding TrapInit by simp
  from pmp_ok entries_same timer_ok mstatus_ok mie_ok
  show ?thesis
    unfolding system_invariant_def by simp
next
  case SystemReset
  then show ?thesis
    using init_state_invariant by simp
next
  case NoOp
  then show ?thesis
    using inv unfolding system_invariant_def by simp
qed

(* 4.2 Sequence of Operations Preserves Invariant *)
(* 4.2 Operation Sequence Preserves Invariant - CORRECTED *)
theorem sbi_sequence_preserves_invariant:
  assumes init: "system_invariant s0"
  shows "system_invariant (execute_sbi_seq ops s0)"
  unfolding execute_sbi_seq_def
  using init
proof (induction ops arbitrary: s0)
  case Nil
  (* Base case: empty list, state unchanged *)
  then show ?case by simp
next
  case (Cons op ops')
  (* Inductive case: op :: ops' *)
  (* Cons.prems is "system_invariant s0" *)
  (* Cons.IH is "\<And>s0. system_invariant s0 \<Longrightarrow> system_invariant (fold execute_sbi ops' s0)" *)
  
  have step: "system_invariant (execute_sbi op s0)"
    using Cons.prems sbi_operation_preserves_invariant by blast
  
  have "system_invariant (fold execute_sbi ops' (execute_sbi op s0))"
    using Cons.IH[OF step] by simp
  
  then show ?case by simp
qed
(* ========================================================================= *)
(* SECTION 5: GLOBAL PMP CORRECTNESS (Safety Theorems)                       *)
(* ========================================================================= *)

theorem pmp_global_correctness:
  assumes init: "system_invariant s0"
  shows "\<forall>ops. valid_pmp_config (pmp_entries (execute_sbi_seq ops s0))"
proof
  fix ops :: "sbi_operation list"
  have "system_invariant (execute_sbi_seq ops s0)"
    using sbi_sequence_preserves_invariant[OF init] by simp
  thus "valid_pmp_config (pmp_entries (execute_sbi_seq ops s0))"
    unfolding system_invariant_def by simp
qed
(* ========================================================================= *)
(* SECTION 6: COROLLARIES / DERIVED PROPERTIES                               *)
(* ========================================================================= *)

(* 6.1 No Invalid PMP Entry Can Be Reached *)
corollary no_invalid_pmp_reachable:
  assumes init: "system_invariant s0"
      and exec: "s' = execute_sbi_seq ops s0"
  shows "\<forall>e \<in> set (pmp_entries s'). valid_pmp_entry e"
proof -
  have "valid_pmp_config (pmp_entries s')"
    using pmp_global_correctness[OF init] exec by simp
  thus ?thesis
    unfolding valid_pmp_config_def by simp
qed

(* 6.2 PMP Protection Never Overflows Address Space *)
corollary pmp_no_overflow:
  assumes init: "system_invariant s0"
      and exec: "s' = execute_sbi_seq ops s0"
      and entry: "e \<in> set (pmp_entries s')"
  shows "case e of (addr, sz, prot) \<Rightarrow> addr + sz \<le> 2^64"
proof -
  have valid: "valid_pmp_entry e"
    using no_invalid_pmp_reachable[OF init exec] entry by simp
  thus ?thesis
    unfolding valid_pmp_entry_def by (cases e; auto)
qed

(* 6.3 Arbitrary Interleaving Preserves Safety *)
corollary arbitrary_interleaving_safe:
  assumes init: "system_invariant s0"
  shows "\<forall>ops1 ops2. 
    let s1 = execute_sbi_seq ops1 s0 in
    let s2 = execute_sbi_seq ops2 s1 in
    system_invariant s2"
proof (intro allI)
  fix ops1 ops2
  let ?s1 = "execute_sbi_seq ops1 s0"
  let ?s2 = "execute_sbi_seq ops2 ?s1"
  
  have inv1: "system_invariant ?s1"
    using sbi_sequence_preserves_invariant[OF init] by simp
  
  have inv2: "system_invariant ?s2"
    using sbi_sequence_preserves_invariant[OF inv1] by simp
  
  show "let s1 = execute_sbi_seq ops1 s0 in
        let s2 = execute_sbi_seq ops2 s1 in
        system_invariant s2"
    using inv2 by simp
qed


(* 6.4 Convenience lemmas for specific ops (nice to cite in text) *)
lemma set_timer_safe:
  assumes "system_invariant s"
  shows "system_invariant (execute_sbi (SetTimer t) s)"
  using sbi_operation_preserves_invariant[OF assms, of "SetTimer t"]
  by simp

lemma set_pmp_safe:
  assumes "system_invariant s"
  shows "system_invariant (execute_sbi (SetPMP idx addr sz prot) s)"
  using sbi_operation_preserves_invariant[OF assms, of "SetPMP idx addr sz prot"]
  by simp

lemma trap_init_safe:
  assumes "system_invariant s"
  shows "system_invariant (execute_sbi TrapInit s)"
  using sbi_operation_preserves_invariant[OF assms, of "TrapInit"]
  by simp

(* ========================================================================= *)
(* SECTION 7: THEORY SUMMARY                                                 *)
(* ========================================================================= *)

text \<open>
Key facts exported from this theory:

  • @{thm init_state_invariant}:
    The reset state @{term init_system_state} already satisfies @{term system_invariant}.

  • @{thm sbi_operation_preserves_invariant}:
    Every single SBI operation preserves @{term system_invariant}.

  • @{thm sbi_sequence_preserves_invariant}:
    Any finite sequence of SBI calls preserves @{term system_invariant}.

  • @{thm pmp_global_correctness} (main global safety theorem):
    For any call trace, the PMP configuration in the resulting state is always valid.

  • @{thm no_invalid_pmp_reachable}:
    No invalid PMP entry can ever appear in reachable states.

  • @{thm pmp_no_overflow}:
    No reachable PMP entry covers an address range beyond the 64-bit bound.

  • @{thm arbitrary_interleaving_safe}:
    Even when you take an arbitrary first sequence and then *another* arbitrary sequence,
    the resulting state is still safe.
\<close>

end
