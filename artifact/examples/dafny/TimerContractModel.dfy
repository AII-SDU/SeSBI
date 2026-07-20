// Timer deadline-programming contract model.
// This file matches dafny-SeSBI-table4/TimerModel.dfy and is verified alongside
// TimerColdInitModel.dfy by the separate dafny_timer_contract stage.

module SeSBI_Timer_Model {
  datatype SBIResult = Success(value: nat) | Failed(error: int)
  class TimerState {
    var timer: nat
    constructor()
      ensures timer == 0
    {
      timer := 0;
    }
  }
  function TimerExpired(cmp: nat, now: nat): bool { cmp < now }
  method SetTimer(hw: TimerState, value: nat) returns (r: SBIResult)
    modifies hw
    ensures hw.timer == value
  {
    hw.timer := value;
    r := Success(value);
  }
  lemma TimerDeadlineValueRange0000(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0001(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0002(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0003(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0004(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0005(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0006(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0007(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0008(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0009(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0010(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0011(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0012(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0013(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0014(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0015(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0016(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0017(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0018(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0019(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0020(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0021(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0022(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0023(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0024(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0025(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0026(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0027(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0028(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0029(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0030(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0031(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0032(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0033(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0034(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0035(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0036(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0037(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0038(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0039(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0040(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0041(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0042(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0043(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0044(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0045(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0046(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0047(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0048(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0049(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0050(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0051(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0052(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0053(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0054(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0055(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0056(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0057(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0058(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0059(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0060(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0061(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0062(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0063(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0064(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0065(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0066(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0067(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0068(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0069(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0070(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0071(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0072(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0073(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0074(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0075(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0076(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0077(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0078(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0079(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0080(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0081(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0082(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0083(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0084(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0085(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0086(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0087(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0088(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0089(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0090(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0091(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0092(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0093(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0094(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0095(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0096(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0097(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0098(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  lemma TimerDeadlineValueRange0099(x: nat)
    ensures TimerExpired(x, x + 1)
  {
  }
  const TimerDeadlineValueRangeAnchor0000: nat := 0
}
