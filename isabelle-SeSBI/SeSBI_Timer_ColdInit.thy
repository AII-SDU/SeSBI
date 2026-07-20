theory SeSBI_Timer_ColdInit
  imports Main
begin

section \<open>Cold-start timer initialization model\<close>

text \<open>
  Abstract model of the M-mode cold-start timer initialization implemented in
  @{text "SeSBI-code/sbi/sbi_timer.c"} as @{text "sbi_timer_init()"}, called
  once from @{text "sbi_main()"} after @{text "sbi_trap_init()"} and before the
  PMP configuration / supervisor handoff.

  This model corresponds to the ABSTRACT POST-CONDITIONS of that routine plus a
  hand-written source mapping.  It is NOT a mechanized C-to-model refinement
  proof: no claim is made that the compiled C is formally refined by this model.

  The cold-init routine establishes a deterministic, silent "no deadline"
  timer-service readiness state.  It is deliberately DISTINCT from the
  post-handoff deadline-programming operation (modelled by @{text timer_program}
  in @{text SeSBI_Timer_Frame} and @{text SetTimer} in the Dafny timer model),
  which arms the first periodic deadline and enables the machine timer
  interrupt.  Cold init does the opposite: it leaves no armed deadline and masks
  the machine timer interrupt.

  Post-conditions proved here (matching the C routine's contract):
    - the free-running @{text mtime} is left unmodified;
    - @{text mtimecmp} is set to @{text UINT64_MAX} (no comparator match);
    - the @{text MTIE} bit of @{text mie} is cleared;
    - the @{text STIP} bit of @{text mip} is cleared;
    - every OTHER bit of @{text mie} and @{text mip} is preserved;
    - the operation is idempotent (running cold init twice equals once).
\<close>

subsection \<open>Constants and abstract machine state\<close>

text \<open>The 64-bit all-ones comparator value written by the C routine.\<close>
definition UINT64_MAX :: nat where
  "UINT64_MAX = 2 ^ 64 - 1"

text \<open>
  Bit positions.  On RISC-V the machine timer interrupt occupies
  @{text "IRQ_M_TIMER = 7"} in both @{text mie} (MTIE) and @{text mip} (MTIP);
  the supervisor timer pending bit @{text STIP} is @{text "IRQ_S_TIMER = 5"}.
\<close>
definition MTIE_BIT :: nat where "MTIE_BIT = 7"
definition STIP_BIT :: nat where "STIP_BIT = 5"

text \<open>
  Abstract machine state relevant to cold-start timer init.  @{text mie} and
  @{text mip} are modelled as bit-indexed predicates so that "every other bit is
  preserved" is expressible and provable.
\<close>
record MState =
  mtime    :: nat
  mtimecmp :: nat
  mie      :: "nat \<Rightarrow> bool"
  mip      :: "nat \<Rightarrow> bool"

subsection \<open>The cold-init operation\<close>

definition cold_timer_init :: "MState \<Rightarrow> MState" where
  "cold_timer_init s =
     s\<lparr> mtimecmp := UINT64_MAX,
        mie := (mie s)(MTIE_BIT := False),
        mip := (mip s)(STIP_BIT := False) \<rparr>"

subsection \<open>Post-conditions\<close>

text \<open>The comparator is set to the all-ones no-match value.\<close>
theorem cold_init_sets_cmp_uint64_max:
  "mtimecmp (cold_timer_init s) = UINT64_MAX"
  by (simp add: cold_timer_init_def)

text \<open>The machine timer interrupt enable (MTIE) is cleared.\<close>
theorem cold_init_clears_mtie:
  "mie (cold_timer_init s) MTIE_BIT = False"
  by (simp add: cold_timer_init_def)

text \<open>Any stale supervisor timer pending bit (STIP) is cleared.\<close>
theorem cold_init_clears_stip:
  "mip (cold_timer_init s) STIP_BIT = False"
  by (simp add: cold_timer_init_def)

text \<open>The free-running counter @{text mtime} is untouched.\<close>
theorem cold_init_preserves_mtime:
  "mtime (cold_timer_init s) = mtime s"
  by (simp add: cold_timer_init_def)

text \<open>Every @{text mie} bit other than MTIE is preserved.\<close>
theorem cold_init_preserves_other_mie:
  assumes "n \<noteq> MTIE_BIT"
  shows "mie (cold_timer_init s) n = mie s n"
  using assms by (simp add: cold_timer_init_def)

text \<open>Every @{text mip} bit other than STIP is preserved.\<close>
theorem cold_init_preserves_other_mip:
  assumes "n \<noteq> STIP_BIT"
  shows "mip (cold_timer_init s) n = mip s n"
  using assms by (simp add: cold_timer_init_def)

subsection \<open>No spurious machine-timer condition after cold init\<close>

text \<open>
  With the comparator at @{text UINT64_MAX} and MTIE cleared, there is no armed
  and enabled machine-timer deadline: the enable bit is low regardless of the
  counter.  This is the abstract counterpart of "no spurious timer interrupt
  before handoff".
\<close>
theorem cold_init_no_armed_enabled_mtimer:
  "\<not> mie (cold_timer_init s) MTIE_BIT"
  by (simp add: cold_timer_init_def)

subsection \<open>Idempotency\<close>

text \<open>
  Running cold init twice yields exactly the same abstract state as running it
  once: the second application rewrites the same fields to the same values.
\<close>
theorem cold_init_idempotent:
  "cold_timer_init (cold_timer_init s) = cold_timer_init s"
  by (simp add: cold_timer_init_def fun_upd_idem_iff)

subsection \<open>Distinctness from post-handoff deadline programming\<close>

text \<open>
  A sanity theorem making the cold-init/service-path distinction explicit: cold
  init leaves MTIE low, whereas arming a real deadline (the post-handoff path)
  must raise it.  Hence the two operations cannot be conflated: any state
  produced by cold init fails the "machine timer enabled" predicate that a
  freshly-armed deadline state satisfies.
\<close>
definition mtimer_enabled :: "MState \<Rightarrow> bool" where
  "mtimer_enabled s \<longleftrightarrow> mie s MTIE_BIT"

theorem cold_init_not_deadline_armed:
  "\<not> mtimer_enabled (cold_timer_init s)"
  by (simp add: mtimer_enabled_def cold_timer_init_def)

end
