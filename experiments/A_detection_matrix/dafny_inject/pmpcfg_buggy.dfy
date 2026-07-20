module SeSBI_PMP_EncodingModel {
  datatype SBIResult = Success(value: nat) | Failed(error: int)
  datatype PmpPerm = NoPerm | Read | Write | Execute | Rwx
  datatype PmpEntry = PmpEntry(addr: nat, size: nat, perm: PmpPerm)
  predicate ValidSize(size: nat) { size >= 4 }
  predicate ValidEntry(e: PmpEntry) { ValidSize(e.size) }
  function EncodeAddr(addr: nat): nat { addr / 4 }
  method SetPmp(addr: nat, size: nat, perm: PmpPerm) returns (e: PmpEntry)
    requires ValidSize(size)
    ensures ValidEntry(e)
    ensures e.addr == EncodeAddr(addr)
  {
    e := PmpEntry(EncodeAddr(addr), size, perm);
  }
  predicate ValidPmpIndex(idx: nat) { idx < 16 }
  predicate ValidPmpRegion(base: nat, size: nat) { ValidSize(size) && base % 4 == 0 }
  function PmpCfgCsrIndex(idx: nat): nat
    requires ValidPmpIndex(idx)
  { if idx < 8 then 0 else 2 }
  function PmpCfgByteOffset(idx: nat): nat
    requires ValidPmpIndex(idx)
  { idx % 4 }  // INJECTED pmpcfg offset bug
  function PmpCfgShift(idx: nat): nat
    requires ValidPmpIndex(idx)
  { 8 * PmpCfgByteOffset(idx) }
  function NapotMask(size: nat): nat
    requires size >= 8
  { size / 8 - 1 }
  function EncodeNapot(base: nat, size: nat): nat
    requires ValidPmpRegion(base, size)
    requires size >= 8
  { EncodeAddr(base) + NapotMask(size) }
  lemma PmpIndexLowSelectsCfg0(idx: nat)
    requires idx < 8
    ensures PmpCfgCsrIndex(idx) == 0
  {
  }
  lemma PmpIndexHighSelectsCfg2(idx: nat)
    requires 8 <= idx < 16
    ensures PmpCfgCsrIndex(idx) == 2
  {
  }
  lemma PmpByteOffsetBounded(idx: nat)
    requires ValidPmpIndex(idx)
    ensures PmpCfgByteOffset(idx) < 8
  {
  }
  lemma PmpCfgShiftBounded(idx: nat)
    requires ValidPmpIndex(idx)
    ensures PmpCfgShift(idx) < 64
  {
  }
  lemma PmpNapoteMaskNonnegative(size: nat)
    requires size >= 8
    ensures NapotMask(size) + 1 == size / 8
  {
  }
  lemma SetPmpReturnsEncodedEntry(addr: nat, size: nat, perm: PmpPerm)
    requires ValidSize(size)
    ensures ValidEntry(PmpEntry(EncodeAddr(addr), size, perm))
  {
  }
  datatype PmpMode = Off | TOR | NA4 | NAPOT
  function ModeBits(mode: PmpMode): nat
  {
    match mode
    case Off => 0
    case TOR => 1
    case NA4 => 2
    case NAPOT => 3
  }
  function PermBits(perm: PmpPerm): nat
  {
    match perm
    case NoPerm => 0
    case Read => 1
    case Write => 2
    case Execute => 4
    case Rwx => 7
  }
  function LockBit(locked: bool): nat { if locked then 128 else 0 }
  const PmpCfgLockMask: nat := 128
  const PmpCfgModeScale: nat := 8
  function PmpCfgByte(perm: PmpPerm, mode: PmpMode, locked: bool): nat
  {
    PermBits(perm) + PmpCfgModeScale * ModeBits(mode) + LockBit(locked)
  }
  predicate ValidCfgByte(cfg: nat) { cfg < 256 }
  function RegionEnd(base: nat, size: nat): nat
    requires ValidPmpRegion(base, size)
  { base + size }
  predicate RegionContains(base: nat, size: nat, addr: nat)
    requires ValidPmpRegion(base, size)
  { base <= addr && addr < RegionEnd(base, size) }
  predicate ReadPermitted(perm: PmpPerm) { perm == Read || perm == Rwx }
  predicate WritePermitted(perm: PmpPerm) { perm == Write || perm == Rwx }
  predicate ExecPermitted(perm: PmpPerm) { perm == Execute || perm == Rwx }
  lemma PmpModeOffBits()
    ensures ModeBits(Off) == 0
  {
  }
  lemma PmpModeTorBits()
    ensures ModeBits(TOR) == 1
  {
  }
  lemma PmpModeNa4Bits()
    ensures ModeBits(NA4) == 2
  {
  }
  lemma PmpModeNapotBits()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpModeBitsBounded(mode: PmpMode)
    ensures ModeBits(mode) < 4
  {
  }
  lemma PmpNoPermBits()
    ensures PermBits(NoPerm) == 0
  {
  }
  lemma PmpReadPermBits()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpWritePermBits()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpExecPermBits()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpRwxPermBits()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpPermBitsBounded(perm: PmpPerm)
    ensures PermBits(perm) < 8
  {
  }
  lemma PmpLockBitClear()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpLockBitSet()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpLockBitBounded(locked: bool)
    ensures LockBit(locked) <= PmpCfgLockMask
  {
  }
  lemma PmpCfgByteUnlockedNapotRwx()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgByteLockedNapotRwx()
    ensures PmpCfgByte(Rwx, NAPOT, true) == 159
  {
  }
  lemma PmpCfgByteBounded(perm: PmpPerm, mode: PmpMode, locked: bool)
    ensures ValidCfgByte(PmpCfgByte(perm, mode, locked))
  {
  }
  lemma PmpReadPermissionRecognizesRead()
    ensures ReadPermitted(Read)
  {
  }
  lemma PmpReadPermissionRecognizesRwx()
    ensures ReadPermitted(Rwx)
  {
  }
  lemma PmpWritePermissionRecognizesWrite()
    ensures WritePermitted(Write)
  {
  }
  lemma PmpWritePermissionRecognizesRwx()
    ensures WritePermitted(Rwx)
  {
  }
  lemma PmpExecPermissionRecognizesExecute()
    ensures ExecPermitted(Execute)
  {
  }
  lemma PmpExecPermissionRecognizesRwx()
    ensures ExecPermitted(Rwx)
  {
  }
  lemma PmpNoPermDisablesRead()
    ensures !ReadPermitted(NoPerm)
  {
  }
  lemma PmpNoPermDisablesWrite()
    ensures !WritePermitted(NoPerm)
  {
  }
  lemma PmpNoPermDisablesExec()
    ensures !ExecPermitted(NoPerm)
  {
  }
  lemma PmpRegionEndAdvances(base: nat, size: nat)
    requires ValidPmpRegion(base, size)
    ensures RegionEnd(base, size) == base + size
  {
  }
  lemma PmpRegionContainsBase(base: nat, size: nat)
    requires ValidPmpRegion(base, size)
    ensures RegionContains(base, size, base)
  {
  }
  lemma PmpRegionRejectsEnd(base: nat, size: nat)
    requires ValidPmpRegion(base, size)
    ensures !RegionContains(base, size, RegionEnd(base, size))
  {
  }
  lemma PmpEncodedBaseAligned(base: nat, size: nat)
    requires ValidPmpRegion(base, size)
    ensures EncodeAddr(base) * 4 == base
  {
  }
  lemma PmpNapotEncodingExtendsBase(base: nat, size: nat)
    requires ValidPmpRegion(base, size)
    requires size >= 8
    ensures EncodeNapot(base, size) >= EncodeAddr(base)
  {
  }
  lemma PmpCfgIndexByteOffsetLow(idx: nat)
    requires idx < 8
    ensures PmpCfgCsrIndex(idx) == 0 && PmpCfgByteOffset(idx) == idx
  {
  }
  lemma PmpCfgIndexByteOffsetHigh(idx: nat)
    requires 8 <= idx < 16
    ensures PmpCfgCsrIndex(idx) == 2 && PmpCfgByteOffset(idx) == idx - 8
  {
  }
  lemma PmpCfgShiftMatchesOffset(idx: nat)
    requires ValidPmpIndex(idx)
    ensures PmpCfgShift(idx) == PmpCfgModeScale * PmpCfgByteOffset(idx)
  {
  }
  lemma PmpCfgWritePermBit0057()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0058()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0059()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0060()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0061()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0062()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0063()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0064()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0065()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0066()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0067()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0068()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0069()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0070()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0071()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0072()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0073()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0074()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0075()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0076()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0077()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0078()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0079()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0080()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0081()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0082()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0083()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0084()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0085()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0086()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0087()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0088()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0089()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0090()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0091()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0092()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0093()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0094()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0095()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0096()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0097()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0098()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0099()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0100()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0101()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0102()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0103()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0104()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0105()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0106()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0107()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0108()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0109()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0110()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0111()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0112()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0113()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0114()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0115()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0116()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0117()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0118()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0119()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0120()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0121()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0122()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0123()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0124()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0125()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0126()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0127()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0128()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0129()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0130()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0131()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0132()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0133()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0134()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0135()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0136()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0137()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0138()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0139()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0140()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0141()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0142()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0143()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0144()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0145()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0146()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0147()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0148()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0149()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0150()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0151()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0152()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0153()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0154()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0155()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0156()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0157()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0158()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0159()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0160()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0161()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0162()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0163()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0164()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0165()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0166()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0167()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0168()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0169()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0170()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0171()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0172()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0173()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0174()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0175()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0176()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0177()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0178()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0179()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0180()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0181()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0182()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0183()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0184()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0185()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0186()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0187()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0188()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0189()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0190()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0191()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0192()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0193()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0194()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0195()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0196()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0197()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0198()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0199()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0200()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0201()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0202()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0203()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0204()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0205()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0206()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0207()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0208()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0209()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0210()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0211()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0212()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0213()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0214()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0215()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0216()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0217()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0218()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0219()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0220()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0221()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0222()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0223()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0224()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0225()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0226()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0227()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0228()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0229()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0230()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0231()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0232()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0233()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0234()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0235()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0236()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0237()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0238()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0239()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0240()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0241()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0242()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0243()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0244()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0245()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0246()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0247()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0248()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0249()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0250()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0251()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0252()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0253()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0254()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0255()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0256()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0257()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0258()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0259()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0260()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0261()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0262()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0263()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0264()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0265()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0266()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0267()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0268()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0269()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0270()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0271()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0272()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0273()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0274()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0275()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0276()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0277()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0278()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0279()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0280()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0281()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0282()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0283()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0284()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0285()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0286()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0287()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  lemma PmpCfgReadPermBit0288()
    ensures PermBits(Read) == 1
  {
  }
  lemma PmpCfgWritePermBit0289()
    ensures PermBits(Write) == 2
  {
  }
  lemma PmpCfgExecPermBit0290()
    ensures PermBits(Execute) == 4
  {
  }
  lemma PmpCfgRwxPermBits0291()
    ensures PermBits(Rwx) == 7
  {
  }
  lemma PmpCfgNapotModeBits0292()
    ensures ModeBits(NAPOT) == 3
  {
  }
  lemma PmpCfgUnlockedBit0293()
    ensures LockBit(false) == 0
  {
  }
  lemma PmpCfgLockedBit0294()
    ensures LockBit(true) == PmpCfgLockMask
  {
  }
  lemma PmpCfgRwxNapotByte0295()
    ensures PmpCfgByte(Rwx, NAPOT, false) == 31
  {
  }
  const PmpEncodingInventoryAnchor0000: nat := 0
}
