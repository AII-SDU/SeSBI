default Order dec
$include <prelude.sail>

/* operator overloads as in sail-riscv model/prelude/prelude.sail */
overload operator & = {and_vec}

/* Minimal, pure interval-entry subset of sail-riscv PMP pmpCheck. */
enum pmpAddrMatch = {PMP_NoMatch, PMP_PartialMatch, PMP_Match}

enum PmpScopePriv = {Scope_User, Scope_Supervisor, Scope_Machine}

enum PmpScopeAccess = {Scope_Read, Scope_Write, Scope_Execute}

enum PmpScopeDecision = {Scope_Continue, Scope_Allow, Scope_Fault}

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

function isFetchScope(access : PmpScopeAccess) -> bool =
  match access {
    Scope_Execute => true,
    _             => false,
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

function pmpCheckScopeEffective(
  entries : list(PmpScopeEntry),
  priv    : PmpScopePriv,
  mprv    : bool,
  mpp     : PmpScopePriv,
  access  : PmpScopeAccess,
  addr    : nat,
  width   : nat,
) -> PmpScopeDecision =
  pmpCheckScope(entries, effectivePrivilegeScope(access, mprv, mpp, priv), access, addr, width)
