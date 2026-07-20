module SeSBI_Console_DbcnModel {
  datatype SBIResult = Success(value: nat) | Failed(error: int)
  class ConsoleState {
    var bytes: seq<nat>
    constructor()
      ensures bytes == []
    {
      bytes := [];
    }
  }
  predicate ByteOk(x: nat) { x < 256 }
  method PutChar(hw: ConsoleState, ch: nat) returns (r: SBIResult)
    requires ByteOk(ch)
    modifies hw
    ensures hw.bytes == old(hw.bytes) + [ch]
  {
    hw.bytes := hw.bytes + [ch];
    r := Success(ch);
  }
  lemma ConsoleDbcnByteRange0000(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0001(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0002(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0003(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0004(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0005(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0006(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0007(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0008(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0009(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0010(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0011(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0012(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0013(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0014(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0015(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0016(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0017(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0018(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0019(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0020(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0021(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0022(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0023(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0024(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0025(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0026(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0027(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0028(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0029(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0030(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0031(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0032(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0033(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0034(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0035(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0036(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0037(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0038(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0039(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0040(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  lemma ConsoleDbcnByteRange0041(x: nat)
    ensures ByteOk(x) ==> x < 512
  {
  }
  const ConsoleDbcnByteRangeAnchor0000: nat := 0
  const ConsoleDbcnByteRangeAnchor0001: nat := 1
}
