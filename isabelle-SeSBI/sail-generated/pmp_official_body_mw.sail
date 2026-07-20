default Order dec
$include <prelude.sail>

overload operator & = {and_vec}
overload operator ^ = {xor_vec}
overload ~ = {not_vec}
overload operator + = {add_bits, add_bits_int}

/*
 * Official-function-body PMP subset.
 *
 * This file keeps the branch structure of sail-riscv pmpCheck,
 * pmpMatchAddr, pmpCheckRWX, and accessFaultFromAccessType, but makes the PMP
 * table an explicit function argument.  It is not the full sail-riscv global
 * register-state model.
 */

enum pmpAddrMatch = {PMP_NoMatch, PMP_PartialMatch, PMP_Match}

enum PmpAddrMatchType = {OFF, TOR, NA4, NAPOT}

enum Privilege = {User, VirtualUser, Supervisor, VirtualSupervisor, Machine}

enum PmpAccess = {
  Access_Load_Data,
  Access_Load_Vector,
  Access_Load_PageTableEntry,
  Access_Load_ShadowStack,
  Access_LoadReserved_Data,
  Access_Store_Data,
  Access_Store_Vector,
  Access_Store_PageTableEntry,
  Access_Store_ShadowStack,
  Access_StoreConditional_Data,
  Access_Atomic_Data_Data,
  Access_Atomic_ShadowStack_ShadowStack,
  Access_InstructionFetch,
  Access_Cache_CB_manage,
  Access_Cache_CB_zero,
  Access_Cache_Prefetch_I,
  Access_Cache_Prefetch_R,
  Access_Cache_Prefetch_W,
}

enum PmpException = {
  E_Fetch_Access_Fault,
  E_Load_Access_Fault,
  E_SAMO_Access_Fault,
}

struct Pmpcfg_ent = {
  cfg_R : bool,
  cfg_W : bool,
  cfg_X : bool,
  cfg_A : PmpAddrMatchType,
  cfg_L : bool,
}

struct PmpRawEntry = {
  raw_addr : bits(64),
  raw_cfg  : Pmpcfg_ent,
}

function accessFaultFromAccessType(access : PmpAccess) -> PmpException =
  match access {
    Access_InstructionFetch                  => E_Fetch_Access_Fault,
    Access_Load_Data                         => E_Load_Access_Fault,
    Access_Load_Vector                       => E_Load_Access_Fault,
    Access_Load_PageTableEntry               => E_Load_Access_Fault,
    Access_LoadReserved_Data                 => E_Load_Access_Fault,
    Access_Store_Data                        => E_SAMO_Access_Fault,
    Access_Store_Vector                      => E_SAMO_Access_Fault,
    Access_Store_PageTableEntry              => E_SAMO_Access_Fault,
    Access_StoreConditional_Data             => E_SAMO_Access_Fault,
    Access_Atomic_Data_Data                  => E_SAMO_Access_Fault,
    Access_Load_ShadowStack                  => E_SAMO_Access_Fault,
    Access_Store_ShadowStack                 => E_SAMO_Access_Fault,
    Access_Atomic_ShadowStack_ShadowStack    => E_SAMO_Access_Fault,
    Access_Cache_CB_manage                   => E_SAMO_Access_Fault,
    Access_Cache_CB_zero                     => E_SAMO_Access_Fault,
    Access_Cache_Prefetch_R                  => E_Load_Access_Fault,
    Access_Cache_Prefetch_W                  => E_SAMO_Access_Fault,
    Access_Cache_Prefetch_I                  => E_Fetch_Access_Fault,
  }

function pmpCheckRWX(ent : Pmpcfg_ent, access : PmpAccess) -> bool =
  match access {
    Access_Load_Data                         => ent.cfg_R,
    Access_Load_Vector                       => ent.cfg_R,
    Access_Load_PageTableEntry               => ent.cfg_R,
    Access_LoadReserved_Data                 => ent.cfg_R,
    Access_Store_Data                        => ent.cfg_W,
    Access_Store_Vector                      => ent.cfg_W,
    Access_Store_PageTableEntry              => ent.cfg_W,
    Access_StoreConditional_Data             => ent.cfg_W,
    Access_Atomic_Data_Data                  => ent.cfg_R & ent.cfg_W,
    Access_InstructionFetch                  => ent.cfg_X,
    Access_Load_ShadowStack                  => ent.cfg_R & ent.cfg_W,
    Access_Store_ShadowStack                 => ent.cfg_R & ent.cfg_W,
    Access_Atomic_ShadowStack_ShadowStack    => ent.cfg_R & ent.cfg_W,
    Access_Cache_CB_manage                   => ent.cfg_R | ent.cfg_W,
    Access_Cache_CB_zero                     => ent.cfg_W,
    Access_Cache_Prefetch_I                  => ent.cfg_X,
    Access_Cache_Prefetch_R                  => ent.cfg_R,
    Access_Cache_Prefetch_W                  => ent.cfg_W,
  }

function pmpLocked(cfg : Pmpcfg_ent) -> bool =
  cfg.cfg_L

function pmpRangeMatch(begin_ : nat, end_ : nat, addr : nat, width : nat) -> pmpAddrMatch =
  if      (addr + width <= begin_) | (end_ <= addr)
  then    PMP_NoMatch
  else if (begin_ <= addr) & (addr + width <= end_)
  then    PMP_Match
  else    PMP_PartialMatch

function pmpaddrAddr(pmpaddr : bits(64)) -> nat =
  unsigned(pmpaddr) * 4

function napotRegion(pmpaddr : bits(64)) -> (nat, nat) = {
  let mask = pmpaddr ^ (pmpaddr + 1);
  let begin_words = unsigned(pmpaddr & (~(mask)));
  let end_words = begin_words + unsigned(mask) + 1;
  (begin_words * 4, end_words * 4)
}

function pmpMatchAddr(
  addr         : nat,
  width        : nat,
  ent          : Pmpcfg_ent,
  pmpaddr      : bits(64),
  prev_pmpaddr : bits(64),
) -> pmpAddrMatch =
  match ent.cfg_A {
    OFF => PMP_NoMatch,
    TOR => {
      if unsigned(prev_pmpaddr) >= unsigned(pmpaddr)
      then PMP_NoMatch
      else pmpRangeMatch(pmpaddrAddr(prev_pmpaddr), pmpaddrAddr(pmpaddr), addr, width)
    },
    NA4 => {
      let begin_ = pmpaddrAddr(pmpaddr);
      pmpRangeMatch(begin_, begin_ + 4, addr, width)
    },
    NAPOT => {
      let (begin_, end_) = napotRegion(pmpaddr);
      pmpRangeMatch(begin_, end_, addr, width)
    },
  }

function pmpCheckFromPrev(
  prev    : bits(64),
  entries : list(PmpRawEntry),
  addr    : nat,
  width   : nat,
  access  : PmpAccess,
  priv    : Privilege,
) -> option(PmpException) =
  match entries {
    [||] => match priv {
      Machine => None(),
      _       => Some(accessFaultFromAccessType(access)),
    },
    ent :: rest => {
      match pmpMatchAddr(addr, width, ent.raw_cfg, ent.raw_addr, prev) {
        PMP_NoMatch => pmpCheckFromPrev(ent.raw_addr, rest, addr, width, access, priv),
        PMP_PartialMatch => Some(accessFaultFromAccessType(access)),
        PMP_Match => {
          if pmpCheckRWX(ent.raw_cfg, access) |
             (match priv {
                Machine => if pmpLocked(ent.raw_cfg) then false else true,
                _       => false,
              })
          then None()
          else Some(accessFaultFromAccessType(access))
        },
      }
    },
  }

function pmpCheckOfficialBody(
  entries : list(PmpRawEntry),
  addr    : nat,
  width   : nat,
  access  : PmpAccess,
  priv    : Privilege,
) -> option(PmpException) =
  pmpCheckFromPrev(0x0000000000000000, entries, addr, width, access, priv)
