// Fixed-width executable model of SeSBI's validated RV64 PMP update.
//
// The model covers the total signed-index input domain, the two implemented
// RV64 pmpcfg banks, all sixteen pmpaddr slots, the allow-all sentinel, and
// target/frame behavior.  It is deliberately compact: each guarantee below is
// a semantic contract, not repeated inventory.
module SeSBI_PmpRoutineModel {
  const PMP_ENTRY_COUNT: int := 16

  const UINT64_MAX: bv64 := 0xFFFFFFFFFFFFFFFF
  const PMP_R: bv64 := 0x01
  const PMP_W: bv64 := 0x02
  const PMP_X: bv64 := 0x04
  const PMP_RWX: bv64 := 0x07
  const PMP_A_NA4: bv64 := 0x10
  const PMP_A_NAPOT: bv64 := 0x18

  datatype PmpReturn = PmpSuccess | PmpError

  class PmpState {
    var pmpcfg0: bv64
    var pmpcfg2: bv64
    var pmpaddr: seq<bv64>

    constructor(cfg0: bv64, cfg2: bv64, addresses: seq<bv64>)
      requires |addresses| == PMP_ENTRY_COUNT
      ensures pmpcfg0 == cfg0
      ensures pmpcfg2 == cfg2
      ensures pmpaddr == addresses
    {
      pmpcfg0 := cfg0;
      pmpcfg2 := cfg2;
      pmpaddr := addresses;
    }
  }

  function ValidSignedIndex(idx: int): bool
  {
    0 <= idx < PMP_ENTRY_COUNT
  }

  function SupportedProt(prot: bv64): bool
  {
    (prot & !PMP_RWX) == 0 &&
    ((prot & PMP_W) == 0 || (prot & PMP_R) != 0)
  }

  function AllowAll(start: bv64, size: bv64): bool
  {
    start == 0 && size == UINT64_MAX
  }

  function PowerOfTwo(size: bv64): bool
  {
    size != 0 && (size & (size - 1)) == 0
  }

  function OrdinaryRegion(start: bv64, size: bv64): bool
  {
    4 <= size &&
    PowerOfTwo(size) &&
    (start & (size - 1)) == 0 &&
    start <= UINT64_MAX - (size - 1)
  }

  function ValidRegion(start: bv64, size: bv64): bool
  {
    AllowAll(start, size) || OrdinaryRegion(start, size)
  }

  function ValidRequest(idx: int, start: bv64, size: bv64,
                        prot: bv64): bool
  {
    ValidSignedIndex(idx) && ValidRegion(start, size) && SupportedProt(prot)
  }

  function CfgBank(idx: int): int
    requires ValidSignedIndex(idx)
  {
    if idx < 8 then 0 else 2
  }

  function CfgByteOffset(idx: int): int
    requires ValidSignedIndex(idx)
  {
    idx % 8
  }

  function CfgByte(cfg: bv64, offset: int): bv8
    requires 0 <= offset < 8
  {
    if offset == 0 then (cfg & 0xFF) as bv8
    else if offset == 1 then ((cfg >> 8) & 0xFF) as bv8
    else if offset == 2 then ((cfg >> 16) & 0xFF) as bv8
    else if offset == 3 then ((cfg >> 24) & 0xFF) as bv8
    else if offset == 4 then ((cfg >> 32) & 0xFF) as bv8
    else if offset == 5 then ((cfg >> 40) & 0xFF) as bv8
    else if offset == 6 then ((cfg >> 48) & 0xFF) as bv8
    else ((cfg >> 56) & 0xFF) as bv8
  }

  function ReplaceCfgByte(cfg: bv64, offset: int, value: bv8): bv64
    requires 0 <= offset < 8
  {
    if offset == 0 then
      (cfg & 0xFFFFFFFFFFFFFF00) | (value as bv64)
    else if offset == 1 then
      (cfg & 0xFFFFFFFFFFFF00FF) | ((value as bv64) << 8)
    else if offset == 2 then
      (cfg & 0xFFFFFFFFFF00FFFF) | ((value as bv64) << 16)
    else if offset == 3 then
      (cfg & 0xFFFFFFFF00FFFFFF) | ((value as bv64) << 24)
    else if offset == 4 then
      (cfg & 0xFFFFFF00FFFFFFFF) | ((value as bv64) << 32)
    else if offset == 5 then
      (cfg & 0xFFFF00FFFFFFFFFF) | ((value as bv64) << 40)
    else if offset == 6 then
      (cfg & 0xFF00FFFFFFFFFFFF) | ((value as bv64) << 48)
    else
      (cfg & 0x00FFFFFFFFFFFFFF) | ((value as bv64) << 56)
  }

  function CfgFrameMask(offset: int): bv64
    requires 0 <= offset < 8
  {
    if offset == 0 then 0xFFFFFFFFFFFFFF00
    else if offset == 1 then 0xFFFFFFFFFFFF00FF
    else if offset == 2 then 0xFFFFFFFFFF00FFFF
    else if offset == 3 then 0xFFFFFFFF00FFFFFF
    else if offset == 4 then 0xFFFFFF00FFFFFFFF
    else if offset == 5 then 0xFFFF00FFFFFFFFFF
    else if offset == 6 then 0xFF00FFFFFFFFFFFF
    else 0x00FFFFFFFFFFFFFF
  }

  lemma ReplaceCfgByteTarget(cfg: bv64, offset: int, value: bv8)
    requires 0 <= offset < 8
    ensures CfgByte(ReplaceCfgByte(cfg, offset, value), offset) == value
  {
  }

  lemma ReplaceCfgByteFrame0(cfg: bv64, value: bv8)
    ensures ReplaceCfgByte(cfg, 0, value) & CfgFrameMask(0) ==
            cfg & CfgFrameMask(0)
  {
  }

  lemma ReplaceCfgByteFrame1(cfg: bv64, value: bv8)
    ensures ReplaceCfgByte(cfg, 1, value) & CfgFrameMask(1) ==
            cfg & CfgFrameMask(1)
  {
  }

  lemma ReplaceCfgByteFrame2(cfg: bv64, value: bv8)
    ensures ReplaceCfgByte(cfg, 2, value) & CfgFrameMask(2) ==
            cfg & CfgFrameMask(2)
  {
  }

  lemma ReplaceCfgByteFrame3(cfg: bv64, value: bv8)
    ensures ReplaceCfgByte(cfg, 3, value) & CfgFrameMask(3) ==
            cfg & CfgFrameMask(3)
  {
  }

  lemma ReplaceCfgByteFrame4(cfg: bv64, value: bv8)
    ensures ReplaceCfgByte(cfg, 4, value) & CfgFrameMask(4) ==
            cfg & CfgFrameMask(4)
  {
  }

  lemma ReplaceCfgByteFrame5(cfg: bv64, value: bv8)
    ensures ReplaceCfgByte(cfg, 5, value) & CfgFrameMask(5) ==
            cfg & CfgFrameMask(5)
  {
  }

  lemma ReplaceCfgByteFrame6(cfg: bv64, value: bv8)
    ensures ReplaceCfgByte(cfg, 6, value) & CfgFrameMask(6) ==
            cfg & CfgFrameMask(6)
  {
  }

  lemma ReplaceCfgByteFrame7(cfg: bv64, value: bv8)
    ensures ReplaceCfgByte(cfg, 7, value) & CfgFrameMask(7) ==
            cfg & CfgFrameMask(7)
  {
  }

  function ConfigByte(size: bv64, prot: bv64): bv8
  {
    ((prot | (if size == 4 then PMP_A_NA4 else PMP_A_NAPOT)) & 0xFF) as bv8
  }

  function EncodeAddress(start: bv64, size: bv64): bv64
    requires ValidRegion(start, size)
  {
    if AllowAll(start, size) then UINT64_MAX
    else if size == 4 then start >> 2
    else (start >> 2) | ((size >> 3) - 1)
  }

  method SetPmp(s: PmpState, idx: int, start: bv64, size: bv64,
                prot: bv64) returns (r: PmpReturn)
    requires |s.pmpaddr| == PMP_ENTRY_COUNT
    modifies s
    ensures |s.pmpaddr| == PMP_ENTRY_COUNT
    ensures !ValidRequest(idx, start, size, prot) ==>
      r == PmpError &&
      s.pmpcfg0 == old(s.pmpcfg0) &&
      s.pmpcfg2 == old(s.pmpcfg2) &&
      s.pmpaddr == old(s.pmpaddr)
    ensures ValidRequest(idx, start, size, prot) ==> r == PmpSuccess
    ensures ValidRequest(idx, start, size, prot) ==>
      s.pmpaddr[idx] == EncodeAddress(start, size)
    ensures ValidRequest(idx, start, size, prot) ==>
      forall j: int | 0 <= j < PMP_ENTRY_COUNT && j != idx ::
        s.pmpaddr[j] == old(s.pmpaddr[j])
    ensures ValidRequest(idx, start, size, prot) && idx < 8 ==>
      s.pmpcfg0 ==
        ReplaceCfgByte(old(s.pmpcfg0), CfgByteOffset(idx),
                       ConfigByte(size, prot)) &&
      s.pmpcfg2 == old(s.pmpcfg2)
    ensures ValidRequest(idx, start, size, prot) && 8 <= idx ==>
      s.pmpcfg0 == old(s.pmpcfg0) &&
      s.pmpcfg2 ==
        ReplaceCfgByte(old(s.pmpcfg2), CfgByteOffset(idx),
                       ConfigByte(size, prot))
    ensures ValidRequest(idx, start, size, prot) && idx < 8 ==>
      CfgByte(s.pmpcfg0, CfgByteOffset(idx)) == ConfigByte(size, prot)
    ensures ValidRequest(idx, start, size, prot) && 8 <= idx ==>
      CfgByte(s.pmpcfg2, CfgByteOffset(idx)) == ConfigByte(size, prot)
  {
    if !ValidRequest(idx, start, size, prot) {
      r := PmpError;
      return;
    }

    var offset := CfgByteOffset(idx);
    var cfg := ConfigByte(size, prot);
    ghost var oldCfg0 := s.pmpcfg0;
    ghost var oldCfg2 := s.pmpcfg2;

    ReplaceCfgByteTarget(if idx < 8 then oldCfg0 else oldCfg2, offset, cfg);

    s.pmpaddr := s.pmpaddr[idx := EncodeAddress(start, size)];
    if idx < 8 {
      s.pmpcfg0 := ReplaceCfgByte(s.pmpcfg0, offset, cfg);
    } else {
      s.pmpcfg2 := ReplaceCfgByte(s.pmpcfg2, offset, cfg);
    }
    r := PmpSuccess;
  }

  lemma LowIndicesSelectCfg0(idx: int)
    requires 0 <= idx < 8
    ensures CfgBank(idx) == 0
    ensures CfgByteOffset(idx) == idx
  {
  }

  lemma HighIndicesSelectCfg2(idx: int)
    requires 8 <= idx < PMP_ENTRY_COUNT
    ensures CfgBank(idx) == 2
    ensures CfgByteOffset(idx) == idx - 8
  {
  }

  lemma NegativeIndicesAreRejected(idx: int, start: bv64, size: bv64,
                                   prot: bv64)
    requires idx < 0
    ensures !ValidRequest(idx, start, size, prot)
  {
  }

  lemma UpperOutOfRangeIndicesAreRejected(idx: int, start: bv64, size: bv64,
                                          prot: bv64)
    requires PMP_ENTRY_COUNT <= idx
    ensures !ValidRequest(idx, start, size, prot)
  {
  }

  lemma BootRequestsAreAccepted()
    ensures ValidRequest(0, 0, UINT64_MAX, PMP_RWX)
    ensures ValidRequest(1, 0x80000000, 0x40000, PMP_RWX)
  {
  }
}
