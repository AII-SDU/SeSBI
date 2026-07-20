theory Scratch
  imports Main
begin

section \<open>Formal Verification of SBI Init Sequence\<close>

text \<open>
  This theory verifies selected register-state properties of the SBI firmware
  initialization sequence.  The model is an abstraction of the five selected
  state-modifying operations in @{text "base.S"}; it is not a RISC-V instruction
  semantics, a binary semantics, or an end-to-end refinement of the assembly.
\<close>

subsection \<open>Register and State Definitions\<close>

datatype reg =
    mie | sp | t0 | mscratch | zero
  | other string  (* catch-all for extension registers *)

type_synonym state = "reg \<Rightarrow> int"

subsection \<open>Constants\<close>

consts stacks_start :: int

subsection \<open>Primitive Register Operations\<close>

definition csrw :: "reg \<Rightarrow> reg \<Rightarrow> state \<Rightarrow> state" where
  "csrw rd rs s \<equiv> s(rd := s rs)"

definition li :: "reg \<Rightarrow> int \<Rightarrow> state \<Rightarrow> state" where
  "li rd imm s \<equiv> s(rd := imm)"

definition add :: "reg \<Rightarrow> reg \<Rightarrow> reg \<Rightarrow> state \<Rightarrow> state" where
  "add rd rs rt s \<equiv> s(rd := s rs + s rt)"

subsection \<open>Initialization Sequence\<close>

text \<open>
  Five-step model matching the program order of @{text "base.S"}:
    1. csrw mie, zero
    2. la sp, stacks_start   (modeled as li sp stacks_start)
    3. li t0, 4096
    4. add sp, sp, t0
    5. csrw mscratch, sp
  The explicit @{text "li t0, 4096"} instruction is represented by an independent
  state update, so every source-level state-modifying operation has a corresponding
  abstract update.
\<close>

definition init_sequence :: "state \<Rightarrow> state" where
  "init_sequence s \<equiv>
    let s1 = csrw mie zero s;         \<comment> \<open>step 1: disable interrupts\<close>
        s2 = li sp stacks_start s1;    \<comment> \<open>step 2: load stack base\<close>
        s3 = li t0 4096 s2;            \<comment> \<open>step 3: load per-hart stack size\<close>
        s4 = add sp sp t0 s3;          \<comment> \<open>step 4: compute stack top\<close>
        s5 = csrw mscratch sp s4       \<comment> \<open>step 5: save sp for trap recovery\<close>
    in s5"

subsection \<open>Abstract Small-Step Execution\<close>

text \<open>
  The following instruction datatype and transition relation make the execution
  order of the five selected register updates explicit.  The constructors denote
  only the abstract operations used above.  In particular, they do not model
  instruction decoding, exceptions, memory, privilege checks, or other RISC-V
  architectural behavior.
\<close>

datatype startup_instr =
    CsrwI reg reg
  | LoadI reg int
  | AddI reg reg reg

fun exec_startup_instr :: "startup_instr \<Rightarrow> state \<Rightarrow> state" where
  "exec_startup_instr (CsrwI rd rs) s = csrw rd rs s"
| "exec_startup_instr (LoadI rd value) s = li rd value s"
| "exec_startup_instr (AddI rd rs rt) s = add rd rs rt s"

type_synonym startup_config = "startup_instr list \<times> state"

inductive startup_step :: "startup_config \<Rightarrow> startup_config \<Rightarrow> bool" where
  startup_step_head:
    "startup_step (instr # rest, s)
                  (rest, exec_startup_instr instr s)"

inductive startup_steps :: "startup_config \<Rightarrow> startup_config \<Rightarrow> bool" where
  startup_steps_refl:
    "startup_steps config config"
| startup_steps_cons:
    "startup_step config config' \<Longrightarrow>
     startup_steps config' config'' \<Longrightarrow>
     startup_steps config config''"

fun exec_startup_program :: "startup_instr list \<Rightarrow> state \<Rightarrow> state" where
  "exec_startup_program [] s = s"
| "exec_startup_program (instr # rest) s =
     exec_startup_program rest (exec_startup_instr instr s)"

definition startup_program :: "startup_instr list" where
  "startup_program =
    [CsrwI mie zero,
     LoadI sp stacks_start,
     LoadI t0 4096,
     AddI sp sp t0,
     CsrwI mscratch sp]"

lemma startup_step_deterministic:
  assumes "startup_step config next1"
      and "startup_step config next2"
  shows "next1 = next2"
  using assms by (auto elim!: startup_step.cases)

lemma exec_startup_program_small_steps:
  "startup_steps (program, s) ([], exec_startup_program program s)"
proof (induction program arbitrary: s)
  case Nil
  then show ?case
    by (simp add: startup_steps.startup_steps_refl)
next
  case (Cons instr rest)
  have one:
    "startup_step (instr # rest, s)
                  (rest, exec_startup_instr instr s)"
    by (rule startup_step.startup_step_head)
  have remaining:
    "startup_steps (rest, exec_startup_instr instr s)
                   ([], exec_startup_program rest (exec_startup_instr instr s))"
    by (rule Cons.IH)
  show ?case
    using startup_steps.startup_steps_cons[OF one remaining]
    by simp
qed

lemma startup_program_functional_execution:
  "exec_startup_program startup_program s = init_sequence s"
  by (simp add: startup_program_def init_sequence_def Let_def)

theorem startup_program_executes_to_init_sequence:
  "startup_steps (startup_program, s) ([], init_sequence s)"
  using exec_startup_program_small_steps[of startup_program s]
  by (simp add: startup_program_functional_execution)

subsection \<open>Validity of Initial State\<close>

text \<open>
  With the explicit @{text "li t0, 4096"} modeled, the only required preconditions
  are that the zero register holds 0 and that the linker-provided @{text "stacks_start"}
  is non-negative.
\<close>

definition valid_init_state :: "state \<Rightarrow> bool" where
  "valid_init_state s \<equiv>
    s zero = 0 \<and>
    0 \<le> stacks_start"

subsection \<open>Helper Lemmas\<close>

lemma fun_upd_other [simp]:
  assumes "r \<noteq> r'"
  shows "(s(r' := v)) r = s r"
  using assms by simp

lemma fun_upd_same [simp]:
  "(s(r := v)) r = v"
  by simp

subsection \<open>Main Theorem: Init Sequence Correctness\<close>

text \<open>
  After the five-step initialization, the machine state satisfies:
    - interrupts are masked (mie = 0);
    - the stack pointer is at @{text "stacks_start + 4096"};
    - mscratch holds the same value (for trap-time stack recovery);
    - mscratch is non-zero (so the first trap can safely dereference it).
\<close>

theorem init_sequence_correctness:
  assumes init: "valid_init_state s"
  shows
    "let s' = init_sequence s in
       s' mie = 0 \<and>
       s' sp = stacks_start + 4096 \<and>
       s' mscratch = stacks_start + 4096 \<and>
       s' mscratch \<noteq> 0"
proof -
  obtain s1 s2 s3 s4 s5 where
    step1: "s1 = csrw mie zero s" and
    step2: "s2 = li sp stacks_start s1" and
    step3: "s3 = li t0 4096 s2" and
    step4: "s4 = add sp sp t0 s3" and
    step5: "s5 = csrw mscratch sp s4" and
    final: "init_sequence s = s5"
    unfolding init_sequence_def Let_def by auto

  from init have base_zero: "s zero = 0"
               and base_ss:  "0 \<le> stacks_start"
    unfolding valid_init_state_def by auto

  (* Step 1: csrw mie, zero -- disables all interrupts *)
  have s1_mie: "s1 mie = 0"
    unfolding step1 csrw_def using base_zero by simp

  (* Step 2: li sp, stacks_start -- load stack base address *)
  have s2_sp: "s2 sp = stacks_start"
    unfolding step2 li_def by simp

  (* Step 3: li t0, 4096 -- load per-hart stack size *)
  have s3_t0: "s3 t0 = 4096"
    unfolding step3 li_def by simp

  have s3_sp: "s3 sp = s2 sp"
    unfolding step3 li_def by simp

  (* Step 4: add sp, sp, t0 -- compute stack top *)
  have s4_sp_eq: "s4 sp = s3 sp + s3 t0"
    unfolding step4 add_def by simp

  have s4_sp_val: "s4 sp = stacks_start + 4096"
    using s4_sp_eq s3_sp s2_sp s3_t0 by simp

  (* Step 5: csrw mscratch, sp -- save stack pointer for trap recovery *)
  have s5_mscratch_eq: "s5 mscratch = s4 sp"
    unfolding step5 csrw_def by simp

  have s5_mscratch_val: "s5 mscratch = stacks_start + 4096"
    using s5_mscratch_eq s4_sp_val by simp

  have s5_sp_eq: "s5 sp = s4 sp"
    unfolding step5 csrw_def by simp

  have s5_sp_val: "s5 sp = stacks_start + 4096"
    using s5_sp_eq s4_sp_val by simp

  (* mie remains 0 through steps 2-5: none of them write to mie *)
  have s5_mie_eq: "s5 mie = s1 mie"
    unfolding step2 step3 step4 step5 li_def add_def csrw_def by auto

  have s5_mie_zero: "s5 mie = 0"
    using s5_mie_eq s1_mie by simp

  (* mscratch is non-zero because stacks_start >= 0 and we add 4096 *)
  have mscratch_nonzero: "s5 mscratch \<noteq> 0"
    using s5_mscratch_val base_ss by linarith

  show ?thesis
    unfolding final Let_def
    using s5_mie_zero s5_sp_val s5_mscratch_val mscratch_nonzero
    by auto
qed

end
