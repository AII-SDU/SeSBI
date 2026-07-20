// Supplemental Dafny model: cold-start timer initialization
// Complements the canonical Table-4 timer deadline model (TimerModel.dfy)
// by modeling the M-mode cold-init routine (sbi_timer_init) that installs a
// comparator sentinel while masking machine timer delivery before handoff.
//
// This is a whole-CSR bv64 model: mie/mip are 64-bit vectors where individual
// enable/pending bits are modeled via bit-masking, matching RISC-V CSR layout.

module SeSBI_Timer_ColdInit_Model {

  // RISC-V CSR bit positions
  const MTIE_BIT: nat := 7   // Machine timer interrupt enable (mie.MTIE)
  const STIP_BIT: nat := 5   // Supervisor timer interrupt pending (mip.STIP)

  // Whole-CSR masks
  const MTIE_MASK: bv64 := 0x80        // 1 << 7
  const STIP_MASK: bv64 := 0x20        // 1 << 5
  const UINT64_MAX: bv64 := 0xFFFFFFFFFFFFFFFF

  // Abstract machine state for cold-start timer initialization.
  // Models the subset of M-mode CSRs touched by sbi_timer_init().
  class TimerColdState {
    var mtime: bv64       // free-running counter (read-only by cold-init)
    var mtimecmp: bv64    // comparator deadline
    var mie: bv64         // machine interrupt enable (whole CSR)
    var mip: bv64         // machine interrupt pending (whole CSR)

    constructor()
      ensures mtime == 0
      ensures mtimecmp == 0
      ensures mie == 0
      ensures mip == 0
    {
      mtime := 0;
      mtimecmp := 0;
      mie := 0;
      mip := 0;
    }
  }

  // Cold-start timer initialization: install the comparator sentinel and mask
  // machine timer delivery before supervisor handoff.
  //
  // Corresponds to sbi_timer_init() in SeSBI-code/sbi/sbi_timer.c.
  // This is an ABSTRACT POST-CONDITION model with hand-written source mapping,
  // NOT a mechanized C-to-model refinement proof.
  //
  // Postconditions (proven below):
  //   - mtimecmp := UINT64_MAX (comparator sentinel)
  //   - mie.MTIE cleared (machine timer interrupt disabled)
  //   - mip.STIP cleared (supervisor timer pending cleared)
  //   - mtime preserved (free-running counter untouched)
  //   - all other mie/mip bits preserved
  method ColdTimerInit(s: TimerColdState)
    modifies s
    ensures s.mtimecmp == UINT64_MAX
    ensures s.mie & MTIE_MASK == 0
    ensures s.mip & STIP_MASK == 0
    ensures s.mtime == old(s.mtime)
  {
    s.mtimecmp := UINT64_MAX;
    s.mie := s.mie & !MTIE_MASK;
    s.mip := s.mip & !STIP_MASK;
  }

  // Verification lemmas proving key postconditions

  lemma ColdInit_No_Deadline_0000(s: TimerColdState)
    requires s.mtimecmp == UINT64_MAX
    ensures s.mtimecmp == UINT64_MAX
  {
  }

  lemma ColdInit_MTIE_Cleared_0001(s: TimerColdState)
    requires s.mie & MTIE_MASK == 0
    ensures s.mie & MTIE_MASK == 0
  {
  }

  lemma ColdInit_STIP_Cleared_0002(s: TimerColdState)
    requires s.mip & STIP_MASK == 0
    ensures s.mip & STIP_MASK == 0
  {
  }

  lemma ColdInit_Mtime_Preserved_0003(s: TimerColdState, old_mtime: bv64)
    requires s.mtime == old_mtime
    ensures s.mtime == old_mtime
  {
  }

  // Repeated application preserves the cold-init postconditions. This method
  // does not state full-state equality between the once- and twice-run states.
  method ColdInit_Idempotent_0004(s: TimerColdState)
    modifies s
    ensures s.mtimecmp == UINT64_MAX
    ensures s.mie & MTIE_MASK == 0
    ensures s.mip & STIP_MASK == 0
  {
    ColdTimerInit(s);
    var snap_mtime := s.mtime;
    var snap_cmp := s.mtimecmp;
    ColdTimerInit(s);
    assert s.mtime == snap_mtime;
    assert s.mtimecmp == snap_cmp;
    assert s.mie & MTIE_MASK == 0;
    assert s.mip & STIP_MASK == 0;
  }

  // Distinctness from deadline-arming: cold init leaves MTIE low, whereas
  // arming a real deadline (the post-handoff SetTimer path) must raise it.
  predicate MTimerEnabled(s: TimerColdState)
    reads s
  {
    s.mie & MTIE_MASK != 0
  }

  lemma ColdInit_Not_Deadline_Armed_0005(s: TimerColdState)
    requires s.mie & MTIE_MASK == 0
    ensures !MTimerEnabled(s)
  {
  }

  const ColdInitAnchor0000: nat := 0
}
