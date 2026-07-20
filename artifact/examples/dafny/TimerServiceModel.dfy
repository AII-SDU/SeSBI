// Executable fixed-width model of the SeSBI timer-service transitions.
//
// The transition structure follows SeSBI-code/sbi/sbi_timer.c and
// SeSBI-code/sbi/sbi_time.c on the scoped RV64 boot-hart path:
//   * ColdInit models sbi_timer_init().
//   * TimerHasExpired models the normalized 0/1 result of
//     sbi_timer_has_expired().
//   * TimerProcess models sbi_timer_process().
//   * EventStart models both branches of clint_timer_event_start().
//   * EcallTime models the supported and unsupported sbi_ecall_time() paths.
//
// The deadline is a timer-state effect.  The SBI call returns status zero and
// value zero on success, matching C aggregate initialization, under which the
// omitted value member is zero-initialized; the call does not return the
// requested deadline as its result value.
// The methods are atomic software transitions.  An mtime frame condition says
// that the corresponding C routine issues no write to the free-running
// counter; it does not assert that physical time stops while code executes.

module SeSBI_Timer_Service_Model {

  const MTIE_MASK: bv64 := 0x80
  const STIP_MASK: bv64 := 0x20
  const UINT64_MAX: bv64 := 0xFFFFFFFFFFFFFFFF

  const SBI_TIME_SET_TIMER: bv64 := 0
  const SBI_SUCCESS: int := 0
  const SBI_ERR_NOT_SUPPORTED: int := -2

  datatype SBIReturn = SBIReturn(error: int, value: bv64)

  class TimerState {
    var mtime: bv64
    var mtimecmp: bv64
    var mie: bv64
    var mip: bv64

    constructor(initialMtime: bv64, initialMtimecmp: bv64,
                initialMie: bv64, initialMip: bv64)
      ensures mtime == initialMtime
      ensures mtimecmp == initialMtimecmp
      ensures mie == initialMie
      ensures mip == initialMip
    {
      mtime := initialMtime;
      mtimecmp := initialMtimecmp;
      mie := initialMie;
      mip := initialMip;
    }
  }

  // C cold initialization sets the no-deadline sentinel and clears only the
  // two named interrupt bits.  The whole-CSR frame clauses state that every
  // other mie/mip bit, as well as the free-running counter, is preserved.
  method {:isolate_assertions} ColdInit(s: TimerState)
    modifies s
    ensures s.mtimecmp == UINT64_MAX
    ensures s.mtime == old(s.mtime)
    ensures s.mie == old(s.mie) & !MTIE_MASK
    ensures s.mip == old(s.mip) & !STIP_MASK
    ensures s.mie & MTIE_MASK == 0
    ensures s.mip & STIP_MASK == 0
  {
    s.mtimecmp := UINT64_MAX;
    s.mie := s.mie & !MTIE_MASK;
    s.mip := s.mip & !STIP_MASK;
  }

  // On RV64, comparison of two bv64 values is unsigned.  The C int return is
  // normalized here to exactly zero or one while preserving its truth value.
  method {:isolate_assertions} TimerHasExpired(mtimecmp: bv64, currentTime: bv64)
      returns (expired: int)
    ensures expired == 0 || expired == 1
    ensures (expired != 0) <==> (mtimecmp < currentTime)
  {
    if mtimecmp < currentTime {
      expired := 1;
    } else {
      expired := 0;
    }
  }

  // Timer interrupt processing disables MTIE and raises STIP.  It does not
  // alter the counter or comparator and changes no other CSR bits.
  method {:isolate_assertions} TimerProcess(s: TimerState)
    modifies s
    ensures s.mtime == old(s.mtime)
    ensures s.mtimecmp == old(s.mtimecmp)
    ensures s.mie == old(s.mie) & !MTIE_MASK
    ensures s.mip == old(s.mip) | STIP_MASK
    ensures s.mie & MTIE_MASK == 0
    ensures s.mip & STIP_MASK == STIP_MASK
  {
    s.mie := s.mie & !MTIE_MASK;
    s.mip := s.mip | STIP_MASK;
  }

  // Deadline programming snapshots mtime once, as the C routine does.  An
  // already-expired deadline raises STIP and returns without touching
  // mtimecmp or mie.  Otherwise it programs the comparator, clears STIP, and
  // enables MTIE.  The contracts give exact target and frame properties for
  // both branches.
  method {:isolate_assertions} EventStart(s: TimerState, nextEvent: bv64)
    modifies s
    ensures s.mtime == old(s.mtime)
    ensures nextEvent < old(s.mtime) ==>
      s.mtimecmp == old(s.mtimecmp) &&
      s.mie == old(s.mie) &&
      s.mip == old(s.mip) | STIP_MASK &&
      s.mip & STIP_MASK == STIP_MASK
    ensures !(nextEvent < old(s.mtime)) ==>
      s.mtimecmp == nextEvent &&
      s.mie == old(s.mie) | MTIE_MASK &&
      s.mip == old(s.mip) & !STIP_MASK &&
      s.mie & MTIE_MASK == MTIE_MASK &&
      s.mip & STIP_MASK == 0
  {
    var currentTime := s.mtime;
    var expired := TimerHasExpired(nextEvent, currentTime);
    if expired != 0 {
      s.mip := s.mip | STIP_MASK;
      return;
    }

    s.mtimecmp := nextEvent;
    s.mip := s.mip & !STIP_MASK;
    s.mie := s.mie | MTIE_MASK;
  }

  // The supported TIME fid performs the deadline state transition and returns
  // { SBI_SUCCESS, 0 }.  Any other fid returns { SBI_ERR_NOT_SUPPORTED, 0 }
  // without changing timer state.
  method {:isolate_assertions} EcallTime(s: TimerState, fid: bv64, deadline: bv64)
      returns (r: SBIReturn)
    modifies s
    ensures fid != SBI_TIME_SET_TIMER ==>
      r == SBIReturn(SBI_ERR_NOT_SUPPORTED, 0) &&
      s.mtime == old(s.mtime) &&
      s.mtimecmp == old(s.mtimecmp) &&
      s.mie == old(s.mie) &&
      s.mip == old(s.mip)
    ensures fid == SBI_TIME_SET_TIMER ==>
      r == SBIReturn(SBI_SUCCESS, 0) &&
      s.mtime == old(s.mtime)
    ensures fid == SBI_TIME_SET_TIMER && deadline < old(s.mtime) ==>
      s.mtimecmp == old(s.mtimecmp) &&
      s.mie == old(s.mie) &&
      s.mip == old(s.mip) | STIP_MASK
    ensures fid == SBI_TIME_SET_TIMER && !(deadline < old(s.mtime)) ==>
      s.mtimecmp == deadline &&
      s.mie == old(s.mie) | MTIE_MASK &&
      s.mip == old(s.mip) & !STIP_MASK
  {
    if fid != SBI_TIME_SET_TIMER {
      r := SBIReturn(SBI_ERR_NOT_SUPPORTED, 0);
      return;
    }

    EventStart(s, deadline);
    r := SBIReturn(SBI_SUCCESS, 0);
  }
}
