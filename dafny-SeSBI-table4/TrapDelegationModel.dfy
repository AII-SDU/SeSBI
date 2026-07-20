module SeSBI_Trap_DelegationModel {
  datatype SBIResult = Success(value: nat) | Failed(error: int)
  datatype TrapKind = Ecall | TimerInterrupt | LoadFault | StoreFault | Unknown
  class TrapState {
    var mepc: nat
    var mie: nat
    var delegated: bool
    constructor()
      ensures mepc == 0
      ensures mie == 0
      ensures !delegated
    {
      mepc := 0;
      mie := 0;
      delegated := false;
    }
  }
  method DelegateTraps(hw: TrapState)
    modifies hw
    ensures hw.delegated
    ensures hw.mie == old(hw.mie)
  {
    hw.delegated := true;
  }
  const CSR_LIMIT: nat := 18446744073709551616
  predicate ValidCsrValue(value: nat) { value < CSR_LIMIT }
  predicate TrapStateFieldsWellFormed(mepc: nat, mie: nat) { ValidCsrValue(mepc) && ValidCsrValue(mie) }
  function DelegatedFlag(previous: bool): bool { true }
  function PreserveMieValue(mie: nat): nat { mie }
  function TrapDelegatedMie(mie: nat): nat { PreserveMieValue(mie) }
  function TrapKindCode(kind: TrapKind): nat
  {
    match kind
    case Ecall => 8
    case TimerInterrupt => 7
    case LoadFault => 5
    case StoreFault => 7
    case Unknown => 0
  }
  lemma TrapZeroStateWellFormed()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapDelegateFlagEnabled(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapMiePreserved(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapKnownCauseCodesBounded(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapEcallCode()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapTimerInterruptCode()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapLoadFaultCode()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapStoreFaultCode()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapUnknownCode()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapWellFormedPreservesMie(mepc: nat, mie: nat)
    requires TrapStateFieldsWellFormed(mepc, mie)
    ensures TrapStateFieldsWellFormed(mepc, PreserveMieValue(mie))
  {
  }
  lemma TrapDelegatedMiePreserved(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapKindCodeNonnegative(kind: TrapKind)
    ensures 0 <= TrapKindCode(kind)
  {
  }
  lemma TrapCauseCodeUnknown0016()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0017(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0018(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0019(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0020(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0021()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0022()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0023()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0024()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0025()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0026()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0027()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0028()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0029(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0030(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0031(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0032(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0033()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0034()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0035()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0036()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0037()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0038()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0039()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0040()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0041(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0042(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0043(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0044(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0045()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0046()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0047()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0048()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0049()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0050()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0051()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0052()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0053(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0054(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0055(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0056(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0057()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0058()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0059()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0060()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0061()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0062()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0063()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0064()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0065(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0066(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0067(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0068(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0069()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0070()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0071()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0072()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0073()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0074()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0075()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0076()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0077(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0078(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0079(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0080(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0081()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0082()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0083()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0084()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0085()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0086()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0087()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0088()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0089(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0090(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0091(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0092(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0093()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0094()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0095()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0096()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0097()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0098()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0099()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0100()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0101(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0102(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0103(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0104(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0105()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0106()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0107()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0108()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0109()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0110()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0111()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0112()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0113(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0114(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0115(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0116(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0117()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0118()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0119()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0120()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0121()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0122()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0123()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0124()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0125(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0126(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0127(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0128(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0129()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0130()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0131()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0132()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0133()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0134()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0135()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0136()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0137(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0138(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0139(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0140(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0141()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0142()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0143()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0144()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0145()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0146()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0147()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0148()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0149(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0150(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0151(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0152(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0153()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0154()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0155()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0156()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0157()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0158()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0159()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0160()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0161(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0162(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0163(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0164(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0165()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0166()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0167()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0168()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0169()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0170()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0171()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0172()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0173(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0174(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0175(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0176(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0177()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0178()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0179()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0180()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0181()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0182()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0183()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0184()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0185(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0186(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0187(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0188(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0189()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0190()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0191()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0192()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0193()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0194()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0195()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0196()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0197(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0198(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0199(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0200(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0201()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0202()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0203()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0204()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0205()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0206()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0207()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0208()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0209(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0210(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0211(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0212(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0213()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0214()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0215()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0216()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0217()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0218()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0219()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0220()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0221(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0222(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0223(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0224(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0225()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0226()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0227()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0228()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0229()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0230()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0231()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0232()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0233(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0234(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0235(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0236(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0237()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0238()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0239()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0240()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0241()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0242()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0243()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0244()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0245(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0246(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0247(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0248(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0249()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0250()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0251()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0252()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0253()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0254()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0255()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0256()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0257(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0258(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0259(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0260(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0261()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0262()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0263()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0264()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0265()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0266()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0267()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0268()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0269(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0270(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0271(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0272(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0273()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0274()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0275()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0276()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0277()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0278()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0279()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0280()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0281(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0282(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0283(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0284(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0285()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0286()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0287()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0288()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0289()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0290()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0291()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0292()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0293(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0294(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0295(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0296(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0297()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0298()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0299()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0300()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0301()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0302()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0303()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0304()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0305(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0306(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0307(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0308(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0309()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0310()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0311()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0312()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0313()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0314()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0315()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0316()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0317(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0318(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0319(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0320(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0321()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0322()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0323()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0324()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0325()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0326()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0327()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0328()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0329(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0330(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0331(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0332(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0333()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0334()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0335()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0336()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0337()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0338()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0339()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0340()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0341(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0342(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0343(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0344(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0345()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0346()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0347()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0348()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0349()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0350()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0351()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0352()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0353(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0354(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0355(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0356(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0357()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0358()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0359()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0360()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0361()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0362()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0363()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0364()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0365(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0366(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0367(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0368(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0369()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0370()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0371()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0372()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0373()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0374()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0375()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0376()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0377(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0378(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0379(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0380(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0381()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0382()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0383()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0384()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0385()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0386()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0387()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0388()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0389(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0390(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0391(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0392(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0393()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0394()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0395()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0396()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0397()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0398()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0399()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0400()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0401(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0402(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0403(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0404(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0405()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0406()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0407()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0408()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0409()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0410()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0411()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0412()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0413(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0414(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0415(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0416(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0417()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0418()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0419()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0420()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0421()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0422()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0423()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0424()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0425(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0426(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0427(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0428(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0429()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0430()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0431()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0432()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0433()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0434()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0435()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0436()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0437(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0438(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0439(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0440(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0441()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0442()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0443()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0444()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0445()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0446()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0447()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0448()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0449(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0450(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0451(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0452(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0453()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0454()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0455()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0456()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0457()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0458()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0459()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0460()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0461(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0462(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0463(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0464(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0465()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0466()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0467()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0468()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0469()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0470()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0471()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0472()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0473(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0474(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0475(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0476(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0477()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0478()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0479()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0480()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0481()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0482()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0483()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0484()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0485(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0486(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0487(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0488(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0489()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0490()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0491()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0492()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0493()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0494()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0495()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0496()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0497(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0498(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0499(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0500(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0501()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0502()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0503()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0504()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0505()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0506()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0507()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0508()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0509(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0510(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0511(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0512(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0513()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0514()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0515()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0516()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0517()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0518()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0519()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0520()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0521(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0522(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0523(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0524(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0525()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0526()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0527()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0528()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0529()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0530()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0531()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0532()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0533(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0534(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0535(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0536(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0537()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0538()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0539()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0540()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0541()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0542()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0543()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0544()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0545(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0546(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0547(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0548(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0549()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0550()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0551()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0552()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0553()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0554()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0555()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0556()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0557(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0558(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0559(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0560(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0561()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0562()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0563()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0564()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0565()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0566()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0567()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0568()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0569(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0570(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0571(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0572(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0573()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0574()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0575()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0576()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0577()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0578()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0579()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0580()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0581(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0582(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0583(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0584(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0585()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0586()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0587()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0588()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0589()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0590()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0591()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0592()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0593(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0594(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0595(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0596(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0597()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0598()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0599()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0600()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0601()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0602()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0603()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0604()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0605(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0606(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0607(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0608(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0609()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0610()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0611()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0612()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0613()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0614()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0615()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0616()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0617(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0618(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0619(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0620(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0621()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0622()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0623()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0624()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0625()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0626()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0627()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0628()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0629(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0630(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0631(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0632(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0633()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0634()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0635()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0636()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0637()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0638()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0639()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0640()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0641(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0642(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0643(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0644(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0645()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0646()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0647()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0648()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0649()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0650()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0651()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0652()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0653(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0654(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0655(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0656(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0657()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0658()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0659()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0660()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0661()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0662()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0663()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0664()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0665(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0666(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0667(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0668(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0669()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0670()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0671()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0672()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0673()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0674()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0675()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0676()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0677(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0678(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0679(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0680(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0681()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0682()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0683()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0684()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0685()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0686()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0687()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0688()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0689(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0690(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0691(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0692(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0693()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0694()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0695()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0696()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0697()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0698()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0699()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0700()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0701(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0702(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0703(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0704(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0705()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0706()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0707()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0708()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0709()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0710()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0711()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0712()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0713(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0714(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0715(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0716(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0717()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0718()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0719()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0720()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0721()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0722()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0723()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0724()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0725(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0726(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0727(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0728(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0729()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0730()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0731()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0732()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0733()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0734()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0735()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0736()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0737(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0738(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0739(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0740(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0741()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0742()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0743()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0744()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0745()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0746()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0747()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0748()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0749(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0750(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0751(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0752(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0753()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0754()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0755()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0756()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0757()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0758()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0759()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0760()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0761(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0762(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0763(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0764(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0765()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0766()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0767()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0768()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0769()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0770()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0771()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0772()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0773(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0774(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0775(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0776(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0777()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0778()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0779()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0780()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0781()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0782()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0783()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0784()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0785(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0786(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0787(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0788(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0789()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0790()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0791()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0792()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0793()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0794()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0795()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0796()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0797(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0798(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0799(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0800(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0801()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0802()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0803()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0804()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0805()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0806()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0807()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0808()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0809(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0810(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0811(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0812(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0813()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0814()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0815()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0816()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0817()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0818()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0819()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0820()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0821(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0822(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0823(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0824(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0825()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0826()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0827()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0828()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0829()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0830()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0831()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0832()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0833(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0834(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0835(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0836(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0837()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0838()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0839()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0840()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0841()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0842()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0843()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0844()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0845(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0846(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0847(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0848(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0849()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0850()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0851()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0852()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0853()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0854()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0855()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0856()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0857(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0858(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0859(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0860(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0861()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0862()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0863()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0864()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0865()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0866()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0867()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0868()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0869(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0870(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0871(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0872(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0873()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0874()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0875()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0876()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0877()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0878()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0879()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0880()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0881(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0882(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0883(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0884(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0885()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  lemma TrapCsrZeroValid0886()
    ensures ValidCsrValue(0)
  {
  }
  lemma TrapCsrLimitPositive0887()
    ensures 0 < CSR_LIMIT
  {
  }
  lemma TrapCauseCodeEcall0888()
    ensures TrapKindCode(Ecall) == 8
  {
  }
  lemma TrapCauseCodeTimer0889()
    ensures TrapKindCode(TimerInterrupt) == 7
  {
  }
  lemma TrapCauseCodeLoad0890()
    ensures TrapKindCode(LoadFault) == 5
  {
  }
  lemma TrapCauseCodeStore0891()
    ensures TrapKindCode(StoreFault) == 7
  {
  }
  lemma TrapCauseCodeUnknown0892()
    ensures TrapKindCode(Unknown) == 0
  {
  }
  lemma TrapKindCodeBounded0893(kind: TrapKind)
    ensures TrapKindCode(kind) < 16
  {
  }
  lemma TrapDelegatedMieIdentity0894(mie: nat)
    ensures TrapDelegatedMie(mie) == mie
  {
  }
  lemma TrapPreserveMieIdentity0895(mie: nat)
    ensures PreserveMieValue(mie) == mie
  {
  }
  lemma TrapDelegateFlagEnabled0896(previous: bool)
    ensures DelegatedFlag(previous)
  {
  }
  lemma TrapZeroStateWellFormed0897()
    ensures TrapStateFieldsWellFormed(0, 0)
  {
  }
  const TrapDelegationInventoryAnchor0000: nat := 0
  const TrapDelegationInventoryAnchor0001: nat := 1
  const TrapDelegationInventoryAnchor0002: nat := 2
}
