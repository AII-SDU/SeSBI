theory SeSBI_PMP_Conformance
  imports SeSBI_PMP_NAPOT
begin

text \<open>
  TRANSCRIPTION-FAITHFULNESS CROSS-CHECK.

  The definitions in SeSBI_PMP_NAPOT (pmpRangeMatch, napot_region) are hand
  transcriptions of the official sail-riscv PMP semantics.  To remove
  "trust the human reading of the Sail source" as an assumption, we ran the
  official Sail compiler (Sail 0.20.1, Lem 2025-03-13) on the VERBATIM
  function bodies from model/pmp/pmp_control.sail and machine-translated them
  to Isabelle.  The generated reference is in sail-generated/Pmp_extract.thy
  (reproduce with sail-generated/REPRODUCE.sh).

  This theory pins our hand transcription to that machine-generated output.
\<close>

subsection \<open>pmpRangeMatch: machine-generated reference (verbatim) + formal equality\<close>

text \<open>
  Copied verbatim from the Sail-compiler output sail-generated/Pmp_extract.thy
  (definition pmpRangeMatch, lines 211-215), retyped only to return our PmpMatch
  enum (whose constructors carry the same names the generator emitted).  The
  generator works over @{typ int}; our model works over @{typ nat}.
\<close>
definition pmpRangeMatch_sail :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> PmpMatch" where
  "pmpRangeMatch_sail begin1 end1 addr width =
     (if (((((((addr + width)) \<le> begin1)) \<or> ((end1 \<le> addr))))) then PMP_NoMatch
      else if (((((begin1 \<le> addr)) \<and> ((((addr + width)) \<le> end1))))) then PMP_Match
      else PMP_PartialMatch)"

text \<open>Our hand-written @{const pmpRangeMatch} (over nat) coincides with the
      machine-generated Sail definition (over int) under the canonical
      nat-to-int embedding.  Hence the matching logic is a faithful transcription.\<close>
theorem pmpRangeMatch_matches_sail:
  "pmpRangeMatch bgn en addr width
     = pmpRangeMatch_sail (int bgn) (int en) (int addr) (int width)"
  by (simp add: pmpRangeMatch_def pmpRangeMatch_sail_def
                of_nat_le_iff flip: of_nat_add)

subsection \<open>napot_region: operator-level correspondence to the generated def\<close>

text \<open>
  The Sail compiler emitted (sail-generated/Pmp_extract.thy, lines 224-229),
  in Lem's bit-list representation:

    napot_region pmpaddr =
      let mask1      = xor_vec pmpaddr (add_vec_int pmpaddr 1)   in
      let begin_words = uint0 (and_vec pmpaddr (not_vec mask1))  in
      let end_words   = (begin_words + uint0 mask1) + 1          in
      (begin_words * 4, end_words * 4)

  Our SeSBI_PMP_NAPOT.napot_region (machine-word representation):

    napot_region pa =
      let m  = pa XOR (pa + 1)        in
      let bw = unat (pa AND NOT m)    in
      let ew = bw + unat m + 1        in
      (bw * 4, ew * 4)

  Operator-by-operator correspondence (Sail bit-list  <->  HOL machine word):
    xor_vec a b      <->  a XOR b              (bitvector xor)
    add_vec_int a 1  <->  a + 1                (bitvector successor)
    and_vec a b      <->  a AND b              (bitvector and)
    not_vec a        <->  NOT a                (bitvector complement)
    uint0 a          <->  unat a               (unsigned interpretation)
    a + b, a * 4     <->  a + b, a * 4         (nat arithmetic)

  i.e. the two are the SAME sequence of operations.  A fully formal
  @{prop "napot_region = generated_napot_region"} additionally requires the
  Sail bit-list/machine-word bridge lemmas (Sail2_operators_*), whose Isabelle
  session is built on the AFP Word_Lib entry; that build is the only remaining
  step and is independent of the proof content above.
\<close>

end
