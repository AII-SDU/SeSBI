default Order dec
$include <prelude.sail>

/* operator overloads as in sail-riscv model/prelude/prelude.sail */
overload operator & = {and_vec}
overload operator ^ = {xor_vec}
overload ~ = {not_vec}
overload operator + = {add_bits, add_bits_int}

/* Verbatim from sail-riscv model/pmp/pmp_control.sail */
enum pmpAddrMatch = {PMP_NoMatch, PMP_PartialMatch, PMP_Match}

function pmpRangeMatch(begin_ : nat, end_ : nat, addr : nat, width : nat) -> pmpAddrMatch =
  if      (addr + width <= begin_) | (end_ <= addr)
  then    PMP_NoMatch
  else if (begin_ <= addr) & (addr + width <= end_)
  then    PMP_Match
  else    PMP_PartialMatch

function napot_region(pmpaddr : bits(64)) -> (nat, nat) = {
  let mask = pmpaddr ^ (pmpaddr + 1);
  let begin_words = unsigned(pmpaddr & (~(mask)));
  let end_words = begin_words + unsigned(mask) + 1;
  (begin_words * 4, end_words * 4)
}
