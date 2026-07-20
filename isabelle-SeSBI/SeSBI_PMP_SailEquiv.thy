theory SeSBI_PMP_SailEquiv
  imports
    SeSBI_PMP_NAPOT
    "sail-generated/Pmp_extract_mw"   \<comment> \<open>Sail-compiler-generated, machine-word mode (the REAL generated def)\<close>
begin

unbundle bit_operations_syntax

text \<open>
  FULL MACHINE-CHECKED transcription faithfulness for the NAPOT region.

  Pmp_extract_mw.napot_region is the definition the official Sail compiler emits
  (machine-word mode) from the VERBATIM official body in
  sail-riscv/model/pmp/pmp_control.sail.  We prove inside the Isabelle kernel
  that our hand-written SeSBI_PMP_NAPOT.napot_region computes the same thing, so
  the correspondence is part of the checked development -- not a human diff.

  We unfold the *base* Sail mword operator definitions (Sail2_operators_mwords,
  which build on Isabelle2025-2); the Sail `*_lemmas` files do not build on this
  Isabelle (coercion bitU/word clashes), so we derive what we need directly.
\<close>

text \<open>Sail's @{const add_vec_int} on a word, with literal 1, is word successor.
      Derived from the Machine-word Bitvector dictionary.\<close>
lemma add_vec_int_one: "add_vec_int (a :: 64 word) 1 = a + 1"
proof -
  have "add_vec_int a (1::int) = word_of_int (uint a + uint (word_of_int 1 :: 64 word))"
    unfolding add_vec_int_def arith_op_bv_int_def
              instance_Sail2_values_Bitvector_Machine_word_mword_dict_def int_of_mword_def
    by simp
  thus ?thesis by (simp add: word_of_int_uint)
qed

text \<open>Normalize the generated Sail body without invoking the broken/expensive
      Sail simp-lemma bundle.\<close>
lemma generated_napot_region_unfolded:
  fixes pa :: "64 word"
  shows "Pmp_extract_mw.napot_region pa =
         (int (unat (pa AND NOT (pa XOR (pa + 1))) * 4),
          int ((unat (pa AND NOT (pa XOR (pa + 1))) + unat (pa XOR (pa + 1)) + 1) * 4))"
proof -
  have add1: "add_vec_int pa ((1 :: int)::ii) = pa + 1"
    by (simp add: add_vec_int_one)
  show ?thesis
    unfolding Pmp_extract_mw.napot_region_def Let_def
    by (simp only: add1 xor_vec_def and_vec_def not_vec_def uint_nat
                   of_nat_add of_nat_mult of_nat_numeral of_nat_1)
qed

lemma sesbi_napot_region_unfolded:
  fixes pa :: "64 word"
  shows "(int (fst (SeSBI_PMP_NAPOT.napot_region pa)),
          int (snd (SeSBI_PMP_NAPOT.napot_region pa))) =
         (int (unat (pa AND NOT (pa XOR (pa + 1))) * 4),
          int ((unat (pa AND NOT (pa XOR (pa + 1))) + unat (pa XOR (pa + 1)) + 1) * 4))"
  unfolding SeSBI_PMP_NAPOT.napot_region_def Let_def
  by simp

text \<open>MAIN: our napot_region equals the Sail-generated one (under nat\<rightarrow>int).\<close>
theorem napot_region_matches_sail:
  fixes pa :: "64 word"
  shows "Pmp_extract_mw.napot_region pa
           = (int (fst (SeSBI_PMP_NAPOT.napot_region pa)),
              int (snd (SeSBI_PMP_NAPOT.napot_region pa)))"
  using generated_napot_region_unfolded[of pa]
        sesbi_napot_region_unfolded[of pa]
  by simp

text \<open>Hence the official-semantics interval-correctness theorem holds verbatim
      for the Sail-generated region too.\<close>
corollary napot_interval_correct_sail:
  assumes "3 \<le> k" and "k \<le> 63"
  shows "Pmp_extract_mw.napot_region (pmp_encode_napot start k)
           = (int (unat (drop_bit 2 start AND NOT (mask (k-2))) * 4),
              int (unat (drop_bit 2 start AND NOT (mask (k-2))) * 4 + 2 ^ k))"
  using napot_region_matches_sail[of "pmp_encode_napot start k"]
        napot_interval_correct[OF assms]
  by simp

end
