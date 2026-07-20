theory SeSBI_PMP_NAPOT
  imports "HOL-Library.Word"
begin

unbundle bit_operations_syntax   \<comment> \<open>activate infix AND/OR/XOR/NOT for words\<close>

text \<open>
  Thin vertical slice for the SeSBI PMP verification.

  We (1) transcribe the official sail-riscv PMP address-matching semantics
  (model/pmp/pmp_control.sail: pmpRangeMatch and the NAPOT branch of
  pmpMatchAddr), (2) model the SeSBI firmware's NAPOT encoding
  (SeSBI-code/sbi/sbi_main.c, the `order > PMP_SHIFT` path), and (3) prove
  INTERVAL CORRECTNESS: the official NAPOT decode of the firmware's encoded
  pmpaddr is exactly the intended, naturally-aligned power-of-two region
  [base, base + 2^k).  This is strictly stronger than encode/decode round-trip
  and is what the isolation argument rests on.

  Faithfulness to the official Sail is by line-for-line transcription here;
  it is to be cross-checked against the generated Sail->Isabelle theory once
  the full RISC-V session is built.
\<close>

type_synonym xlenbits = "64 word"   \<comment> \<open>RV64 pmpaddr register width\<close>

subsection \<open>Official sail-riscv matching semantics (verbatim transcription)\<close>

datatype PmpMatch = PMP_NoMatch | PMP_PartialMatch | PMP_Match

text \<open>pmp_control.sail:59-69 -- right-open interval containment over naturals.\<close>
definition pmpRangeMatch :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> PmpMatch" where
  "pmpRangeMatch bgn en addr width =
     (if addr + width \<le> bgn \<or> en \<le> addr then PMP_NoMatch
      else if bgn \<le> addr \<and> addr + width \<le> en then PMP_Match
      else PMP_PartialMatch)"

text \<open>pmp_control.sail:97-108 -- NAPOT branch of pmpMatchAddr.
      mask = pmpaddr XOR (pmpaddr+1); region = [begin_words*4, end_words*4).\<close>
definition napot_region :: "xlenbits \<Rightarrow> nat \<times> nat" where
  "napot_region pa =
     (let m  = pa XOR (pa + 1);
          bw = unat (pa AND NOT m);
          ew = bw + unat m + 1
      in (bw * 4, ew * 4))"

definition pmpMatchNAPOT :: "xlenbits \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> PmpMatch" where
  "pmpMatchNAPOT pa addr width =
     (let (b,e) = napot_region pa in pmpRangeMatch b e addr width)"

subsection \<open>SeSBI firmware NAPOT encoding (sbi_main.c)\<close>

text \<open>
  sbi_main.c (order = k, with 3 <= k <= 63, i.e. the NAPOT, non-XLEN case):
    pmpaddr  = start >> 2;
    addrmask = (1 << (order - PMP_SHIFT)) - 1;   // PMP_SHIFT = 2
    pmpaddr &= ~addrmask;
    pmpaddr |= (addrmask >> 1);
\<close>
definition pmp_encode_napot :: "xlenbits \<Rightarrow> nat \<Rightarrow> xlenbits" where
  "pmp_encode_napot start k =
     (let a0 = drop_bit 2 start;
          addrmask = mask (k - 2)          \<comment> \<open>\<open>(1 << (k-2)) - 1\<close>\<close>
      in (a0 AND NOT addrmask) OR drop_bit 1 addrmask)"

subsection \<open>Easy facts\<close>

text \<open>For a non-empty access, a full Match is exactly interval containment.\<close>
lemma pmpRangeMatch_Match_iff:
  assumes "0 < width"
  shows "pmpRangeMatch bgn en addr width = PMP_Match
           \<longleftrightarrow> bgn \<le> addr \<and> addr + width \<le> en"
  using assms by (auto simp: pmpRangeMatch_def)

text \<open>\<open>2^(k-2) * 4 = 2^k\<close> for \<open>k \<ge> 2\<close>.\<close>
lemma pow_k: assumes "2 \<le> k" shows "(2::nat) ^ (k-2) * 4 = 2 ^ k"
proof -
  have "(2::nat) ^ (k-2) * 4 = 2 ^ (k-2) * 2 ^ 2" by simp
  also have "\<dots> = 2 ^ (k - 2 + 2)" by (simp add: power_add)
  also have "\<dots> = 2 ^ k" using le_add_diff_inverse2[OF assms] by simp
  finally show ?thesis .
qed

text \<open>Bound-aware @{term drop_bit}-of-@{term mask} (the unconditional form is
      false for words once \<open>m\<close> exceeds the word length).\<close>
lemma drop_bit1_mask_lt:
  fixes m :: nat
  assumes "m \<le> 64"
  shows "drop_bit 1 (mask m :: xlenbits) = mask (m - 1)"
proof (rule bit_word_eqI)
  fix n assume "n < LENGTH(64)"
  with assms show "bit (drop_bit 1 (mask m :: xlenbits)) n = bit (mask (m-1) :: xlenbits) n"
    by (auto simp: bit_simps)
qed

subsection \<open>Core word lemmas\<close>

text \<open>The encoding keeps the high (\<open>\<ge> k-2\<close>) bits of \<open>start>>2\<close> and clears the low
      \<open>k-2\<close> bits -- i.e. masking the encoded value recovers the same base as
      masking \<open>start>>2\<close>.\<close>
lemma encode_and_not_mask:
  "pmp_encode_napot start k AND NOT (mask (k-2))
     = drop_bit 2 start AND NOT (mask (k-2))"
  unfolding pmp_encode_napot_def Let_def
  by (rule bit_word_eqI) (auto simp: bit_simps)

text \<open>Generic helper: for a value @{term b} whose low \<open>m+1\<close> bits are clear,
      OR-ing in the low \<open>m\<close>-bit mask yields a NAPOT pmpaddr whose recovered Sail
      mask \<open>x XOR (x+1)\<close> equals exactly \<open>mask (m+1)\<close>.\<close>
lemma xor_succ_low:
  fixes b :: xlenbits
  assumes z: "b AND mask (Suc m) = 0" and m: "Suc m \<le> 64"
  shows "(b OR mask m) XOR ((b OR mask m) + 1) = mask (Suc m)"
proof -
  have bz: "\<not> bit b j" if "j \<le> m" for j
  proof -
    have "bit (b AND mask (Suc m)) j = bit b j" using that m by (auto simp: bit_simps)
    thus ?thesis using z by simp
  qed
  have dis1: "b AND mask m = 0"
    by (rule bit_word_eqI) (use bz in \<open>auto simp: bit_simps\<close>)
  have e1: "b OR mask m = b + mask m" using dis1 by (simp add: disjunctive_add_eq_or)
  have pbeq: "mask m + 1 = (push_bit m 1 :: xlenbits)" by (simp add: mask_eq_decr_exp)
  have e2: "(b OR mask m) + 1 = b + push_bit m 1" using e1 pbeq by (simp add: add.assoc)
  have dis2: "b AND push_bit m 1 = 0"
    by (rule bit_word_eqI) (use bz in \<open>auto simp: bit_simps\<close>)
  have e3: "(b OR mask m) + 1 = b OR push_bit m 1"
    using e2 dis2 by (simp add: disjunctive_add_eq_or)
  show ?thesis unfolding e3
  proof (rule bit_word_eqI)
    fix n assume "n < LENGTH(64)"
    hence n64: "n < 64" by simp
    have mlt: "m < 64" using m by simp
    show "bit ((b OR mask m) XOR (b OR push_bit m 1)) n = bit (mask (Suc m) :: xlenbits) n"
    proof (cases "n \<le> m")
      case True
      with bz have "\<not> bit b n" by simp
      with True n64 mlt show ?thesis by (auto simp: bit_simps)
    next
      case False
      with n64 mlt show ?thesis by (auto simp: bit_simps)
    qed
  qed
qed

text \<open>The crux: the Sail NAPOT mask recovered from the firmware's encoding is
      exactly the low \<open>k-2\<close> bits, \<open>pmpaddr XOR (pmpaddr+1) = mask (k-2)\<close>.\<close>
lemma encode_xor_succ:
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
  shows "pmp_encode_napot start k XOR (pmp_encode_napot start k + 1) = mask (k-2)"
proof -
  define b where "b = (drop_bit 2 start AND NOT (mask (k-2)) :: xlenbits)"
  have kk: "k - 2 \<le> 64" using k_hi by simp
  have dm: "drop_bit 1 (mask (k-2) :: xlenbits) = mask (k-3)"
    using drop_bit1_mask_lt[OF kk] by simp
  have enc: "pmp_encode_napot start k = b OR mask (k-3)"
    by (simp add: pmp_encode_napot_def Let_def b_def dm del: One_nat_def)
  have sm: "Suc (k-3) = k - 2" using k_lo by simp
  have z: "b AND mask (Suc (k-3)) = 0"
    unfolding sm b_def by (rule bit_word_eqI) (auto simp: bit_simps)
  have le: "Suc (k-3) \<le> 64" using kk sm by simp
  have main: "(b OR mask (k-3)) XOR ((b OR mask (k-3)) + 1) = mask (Suc (k-3))"
    by (rule xor_succ_low[OF z le])
  show ?thesis using main enc sm by simp
qed

subsection \<open>Interval correctness\<close>

text \<open>\<open>unat\<close> of a low-bit mask (within word length).\<close>
lemma unat_mask_k:
  assumes k_hi: "k \<le> 63"
  shows "unat (mask (k-2) :: xlenbits) = 2 ^ (k-2) - 1"
proof -
  have lt: "(2::nat) ^ (k-2) - 1 < 2 ^ 64"
  proof -
    have "(2::nat) ^ (k-2) < 2 ^ 64" using k_hi by (intro power_strict_increasing) auto
    thus ?thesis by linarith
  qed
  have eq: "mask (k-2) = (word_of_nat (2 ^ (k-2) - 1) :: xlenbits)"
    by (simp add: mask_eq_decr_exp of_nat_diff)
  show ?thesis by (subst eq, subst unat_of_nat) (use lt in simp)
qed

text \<open>
  MAIN: the official NAPOT decode of the firmware's encoding is the aligned
  region [base, base + 2^k), where base = (start with its low k bits cleared).
\<close>
theorem napot_interval_correct:
  fixes start :: xlenbits and k :: nat
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
  defines "base \<equiv> unat (drop_bit 2 start AND NOT (mask (k-2))) * 4"
  shows "napot_region (pmp_encode_napot start k) = (base, base + 2^k)"
proof -
  let ?pa = "pmp_encode_napot start k"
  let ?b = "drop_bit 2 start AND NOT (mask (k-2)) :: xlenbits"
  have m: "?pa XOR (?pa + 1) = mask (k-2)" by (rule encode_xor_succ[OF k_lo k_hi])
  have reg: "napot_region ?pa
               = (unat ?b * 4, (unat ?b + unat (mask (k-2) :: xlenbits) + 1) * 4)"
    unfolding napot_region_def Let_def by (simp only: m encode_and_not_mask)
  have key: "unat (mask (k-2) :: xlenbits) + 1 = 2 ^ (k-2)"
    using unat_mask_k[OF k_hi] by simp
  have pow: "(2::nat) ^ (k-2) * 4 = 2 ^ k" using k_lo by (simp add: pow_k)
  have snd: "(unat ?b + unat (mask (k-2) :: xlenbits) + 1) * 4 = unat ?b * 4 + 2 ^ k"
  proof -
    have "unat ?b + unat (mask (k-2) :: xlenbits) + 1 = unat ?b + 2 ^ (k-2)"
      using key by linarith
    hence "(unat ?b + unat (mask (k-2) :: xlenbits) + 1) * 4 = (unat ?b + 2 ^ (k-2)) * 4"
      by simp
    also have "\<dots> = unat ?b * 4 + 2 ^ (k-2) * 4" by (simp add: add_mult_distrib)
    also have "\<dots> = unat ?b * 4 + 2 ^ k" by (simp add: pow)
    finally show ?thesis .
  qed
  show ?thesis using reg snd by (simp add: base_def)
qed

text \<open>The decoded region is naturally aligned to its size.\<close>
corollary napot_region_aligned:
  fixes start :: xlenbits and k :: nat
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
  shows "\<exists>base. base mod 2 ^ k = 0
            \<and> napot_region (pmp_encode_napot start k) = (base, base + 2^k)"
proof (intro exI conjI)
  let ?b = "drop_bit 2 start AND NOT (mask (k-2)) :: xlenbits"
  let ?base = "unat ?b * 4"
  show "napot_region (pmp_encode_napot start k) = (?base, ?base + 2^k)"
    by (rule napot_interval_correct[OF k_lo k_hi])
  have z: "?b AND mask (k-2) = 0"
    by (rule bit_word_eqI) (auto simp: bit_simps)
  hence dvd_b: "(2::nat) ^ (k-2) dvd unat ?b"
    by (simp add: and_mask_dvd_nat)
  have pow: "(2::nat) ^ (k-2) * 4 = 2 ^ k" using k_lo by (simp add: pow_k)
  from dvd_b have "(2::nat) ^ (k-2) * 4 dvd unat ?b * 4" by (rule mult_dvd_mono) simp
  hence "(2::nat) ^ k dvd ?base" by (simp add: pow)
  thus "?base mod 2 ^ k = 0" by simp
qed

text \<open>
  Security-relevant reading: an address block is accepted by the official NAPOT
  matcher for the firmware's encoding iff it lies within the intended region.
\<close>
corollary napot_match_iff_in_region:
  fixes start :: xlenbits and addr :: nat and width :: nat and k :: nat
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63" and w: "0 < width"
  defines "base \<equiv> unat (drop_bit 2 start AND NOT (mask (k-2))) * 4"
  shows "pmpMatchNAPOT (pmp_encode_napot start k) addr width = PMP_Match
           \<longleftrightarrow> base \<le> addr \<and> addr + width \<le> base + 2^k"
proof -
  have "pmpMatchNAPOT (pmp_encode_napot start k) addr width
          = pmpRangeMatch base (base + 2^k) addr width"
    by (simp add: pmpMatchNAPOT_def napot_interval_correct[OF k_lo k_hi] base_def)
  thus ?thesis by (simp add: pmpRangeMatch_Match_iff[OF w])
qed

end
