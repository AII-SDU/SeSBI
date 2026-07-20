default Order dec
$include <prelude.sail>

overload operator & = {and_vec}
overload operator ^ = {xor_vec}
overload ~ = {not_vec}
overload operator + = {add_bits, add_bits_int}

/* Minimal raw-table subset for the SeSBI PMP proof chain. */

enum pmpAddrMatch = {PMP_NoMatch, PMP_PartialMatch, PMP_Match}

enum PmpRawMode = {Raw_OFF, Raw_TOR, Raw_NA4, Raw_NAPOT}

enum PmpScopePriv = {Scope_User, Scope_Supervisor, Scope_Machine}

enum PmpScopeAccess = {Scope_Read, Scope_Write, Scope_Execute}

enum PmpScopeDecision = {Scope_Continue, Scope_Allow, Scope_Fault}

struct PmpRawCfg = {
  raw_mode : PmpRawMode,
  raw_R    : bool,
  raw_W    : bool,
  raw_X    : bool,
  raw_L    : bool,
}

struct PmpRawEntry = {
  raw_addr     : bits(64),
  raw_cfg      : PmpRawCfg,
  raw_all_ones : bool,
}

struct PmpScopeEntry = {
  scope_bgn : nat,
  scope_en  : nat,
  scope_R   : bool,
  scope_W   : bool,
  scope_X   : bool,
  scope_L   : bool,
}

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

function rawEntryOfRegion(cfg : PmpRawCfg, begin_ : nat, end_ : nat) -> PmpScopeEntry =
  struct {
    scope_bgn = begin_,
    scope_en  = end_,
    scope_R   = cfg.raw_R,
    scope_W   = cfg.raw_W,
    scope_X   = cfg.raw_X,
    scope_L   = cfg.raw_L,
  }

function decodeRawPmpEntry(
  prev : bits(64),
  ent  : PmpRawEntry,
) -> option(PmpScopeEntry) =
  match ent.raw_cfg.raw_mode {
    Raw_OFF => None(),
    Raw_TOR => Some(rawEntryOfRegion(ent.raw_cfg, pmpaddrAddr(prev), pmpaddrAddr(ent.raw_addr))),
    Raw_NA4 => Some(rawEntryOfRegion(ent.raw_cfg, pmpaddrAddr(ent.raw_addr), pmpaddrAddr(ent.raw_addr) + 4)),
    Raw_NAPOT => {
      if ent.raw_all_ones
      then Some(rawEntryOfRegion(ent.raw_cfg, 0, 18446744073709551616))
      else {
        let (begin_, end_) = napotRegion(ent.raw_addr);
        Some(rawEntryOfRegion(ent.raw_cfg, begin_, end_))
      }
    },
  }

function decodeRawPmpTableFromPrev(
  prev    : bits(64),
  entries : list(PmpRawEntry),
) -> list(PmpScopeEntry) =
  match entries {
    [||] => [||],
    ent :: rest => {
      let tail = decodeRawPmpTableFromPrev(ent.raw_addr, rest);
      match decodeRawPmpEntry(prev, ent) {
        None()  => tail,
        Some(e) => e :: tail,
      }
    },
  }

function pmpCheckRWX_scope(ent : PmpScopeEntry, access : PmpScopeAccess) -> bool =
  match access {
    Scope_Read    => ent.scope_R,
    Scope_Write   => ent.scope_W,
    Scope_Execute => ent.scope_X,
  }

function pmpLocked_scope(ent : PmpScopeEntry) -> bool =
  ent.scope_L

function pmpEntryCheckScope(
  ent    : PmpScopeEntry,
  priv   : PmpScopePriv,
  access : PmpScopeAccess,
  addr   : nat,
  width  : nat,
) -> PmpScopeDecision =
  match pmpRangeMatch(ent.scope_bgn, ent.scope_en, addr, width) {
    PMP_NoMatch      => Scope_Continue,
    PMP_PartialMatch => Scope_Fault,
    PMP_Match        =>
      if pmpCheckRWX_scope(ent, access)
      then Scope_Allow
      else match priv {
        Scope_Machine => if pmpLocked_scope(ent) then Scope_Fault else Scope_Allow,
        _             => Scope_Fault,
      },
  }

function pmpCheckScope(
  entries : list(PmpScopeEntry),
  priv    : PmpScopePriv,
  access  : PmpScopeAccess,
  addr    : nat,
  width   : nat,
) -> PmpScopeDecision =
  match entries {
    [||] => match priv {
      Scope_Machine => Scope_Allow,
      _             => Scope_Fault,
    },
    ent :: rest => {
      match pmpEntryCheckScope(ent, priv, access, addr, width) {
        Scope_Continue => pmpCheckScope(rest, priv, access, addr, width),
        Scope_Allow    => Scope_Allow,
        Scope_Fault    => Scope_Fault,
      }
    }
  }

function effectivePrivilegeScope(
  access : PmpScopeAccess,
  mprv   : bool,
  mpp    : PmpScopePriv,
  priv   : PmpScopePriv,
) -> PmpScopePriv =
  match access {
    Scope_Execute => priv,
    _             => if mprv then mpp else priv,
  }

function pmpCheckRawTableEffective(
  raw_entries : list(PmpRawEntry),
  priv        : PmpScopePriv,
  mprv        : bool,
  mpp         : PmpScopePriv,
  access      : PmpScopeAccess,
  addr        : nat,
  width       : nat,
) -> PmpScopeDecision =
  pmpCheckScope(
    decodeRawPmpTableFromPrev(0x0000000000000000, raw_entries),
    effectivePrivilegeScope(access, mprv, mpp, priv),
    access,
    addr,
    width
  )
