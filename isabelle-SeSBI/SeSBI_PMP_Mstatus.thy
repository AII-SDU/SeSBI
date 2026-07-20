theory SeSBI_PMP_Mstatus
  imports "HOL-Library.Word"
begin

unbundle bit_operations_syntax

lemma len64 [simp]: "LENGTH(64) = 64"
  by simp

section \<open>Correct mstatus field insertion (mirrors the firmware INSERT_FIELD macro)\<close>

text \<open>
  S5-lite, block 1.  The earlier draft modelled \<open>update_mstatus\<close> with a byte
  index (\<open>2^(reg*8)\<close>), which is wrong: mstatus fields sit at bit positions
  (MPP at 11..12, MPIE at 7), not byte boundaries.  Here we model the ACTUAL
  firmware macro (SeSBI-code/include/asm/csr.h):

    INSERT_FIELD(val, which, fieldval)
      = (val & ~which) | (fieldval * (which & ~(which-1)))

  where \<open>which\<close> is the field MASK and \<open>which & ~(which-1)\<close> is its lowest set bit
  (the field position).  We prove that the target field gets the value and that
  every other bit is unchanged (frame).
\<close>

definition insert_field :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "insert_field val which fieldval =
     (val AND NOT which) OR (fieldval * (which AND NOT (which - 1)))"

definition get_field :: "64 word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 64 word" where
  "get_field reg pos width = drop_bit pos reg AND mask width"

text \<open>csr.h constants, in \<open>push_bit\<close>/\<open>mask\<close> form so bit reasoning stays transparent.\<close>
definition MSTATUS_MPP  :: "64 word" where "MSTATUS_MPP  = push_bit 11 (mask 2)"  \<comment> \<open>\<open>3<<11\<close>, bits 11..12\<close>
definition MSTATUS_MPIE :: "64 word" where "MSTATUS_MPIE = push_bit 7 (mask 1)"   \<comment> \<open>\<open>0x80\<close>, bit 7\<close>
definition PRV_S :: "64 word" where "PRV_S = 1"

text \<open>The field-position lowbit = the lowest set bit of the mask (ground).\<close>
lemma MPP_lowbit:  "MSTATUS_MPP  AND NOT (MSTATUS_MPP  - 1) = push_bit 11 1"
  unfolding MSTATUS_MPP_def by eval
lemma MPIE_lowbit: "MSTATUS_MPIE AND NOT (MSTATUS_MPIE - 1) = push_bit 7 1"
  unfolding MSTATUS_MPIE_def by eval

text \<open>The MPP write: clear bits 11..12, then set bit 11 (PRV_S).\<close>
lemma insert_MPP_PRV_S:
  "insert_field val MSTATUS_MPP PRV_S = (val AND NOT MSTATUS_MPP) OR push_bit 11 1"
  by (simp add: insert_field_def PRV_S_def MPP_lowbit)
text \<open>The MPIE clear: clear bit 7.\<close>
lemma insert_MPIE_0:
  "insert_field val MSTATUS_MPIE 0 = val AND NOT MSTATUS_MPIE"
  by (simp add: insert_field_def)

text \<open>The MPIE set path used by the current firmware's \<open>val |= MSTATUS_MPIE\<close>.\<close>
lemma insert_MPIE_1:
  "insert_field val MSTATUS_MPIE 1 = (val AND NOT MSTATUS_MPIE) OR MSTATUS_MPIE"
  by (simp add: insert_field_def MPIE_lowbit MSTATUS_MPIE_def)

subsection \<open>Field set + frame\<close>

text \<open>MPP (bits 11..12) becomes PRV_S = 0b01 (Supervisor).\<close>
theorem mstatus_mpp_set:
  "get_field (insert_field val MSTATUS_MPP PRV_S) 11 2 = PRV_S"
  apply (unfold insert_MPP_PRV_S)
  apply (unfold get_field_def PRV_S_def MSTATUS_MPP_def)
  apply (rule bit_word_eqI)
  apply (simp only: bit_simps possible_bit_word len_of_numeral_defs comp_def)
  apply (case_tac "bit (val::64 word) (11 + n)"; presburger)
  done

text \<open>Every bit outside the MPP field [11,13) is unchanged.\<close>
theorem mstatus_mpp_frame:
  assumes "n < 11 \<or> 13 \<le> n"
  shows "bit (insert_field val MSTATUS_MPP PRV_S) n = bit val n"
proof -
  have cap: "n < 64 \<or> \<not> bit (val::64 word) n"
    using bit_imp_le_length[where w=val and n=n] by auto
  show ?thesis using assms cap
    unfolding insert_MPP_PRV_S
    by (cases "n < 64"; cases "bit (val::64 word) n";
        simp only: bit_simps possible_bit_word len64 MSTATUS_MPP_def;
        presburger)
qed

text \<open>MPIE (bit 7) becomes 0.\<close>
theorem mstatus_mpie_clear:
  "get_field (insert_field val MSTATUS_MPIE 0) 7 1 = 0"
  unfolding insert_MPIE_0
  apply (unfold get_field_def MSTATUS_MPIE_def)
  apply (rule bit_word_eqI)
  apply (simp only: bit_simps possible_bit_word len64 comp_def bit_0_eq bot_fun_def)
  apply (simp; presburger)
  done

text \<open>MPIE (bit 7) becomes 1.\<close>
theorem mstatus_mpie_set:
  "get_field (insert_field val MSTATUS_MPIE 1) 7 1 = 1"
  unfolding insert_MPIE_1
  apply (unfold get_field_def MSTATUS_MPIE_def)
  apply (rule bit_word_eqI)
  apply (simp only: bit_simps possible_bit_word len64 comp_def)
  apply (case_tac n; simp)
  done

text \<open>MPIE clear leaves every other bit unchanged.\<close>
theorem mstatus_mpie_frame:
  assumes "n \<noteq> 7"
  shows "bit (insert_field val MSTATUS_MPIE 0) n = bit val n"
proof -
  have cap: "n < 64 \<or> \<not> bit (val::64 word) n"
    using bit_imp_le_length[where w=val and n=n] by auto
  show ?thesis using assms cap
    unfolding insert_MPIE_0
    by (cases "n < 64"; cases "bit (val::64 word) n";
        simp only: bit_simps possible_bit_word len64 MSTATUS_MPIE_def;
        presburger)
qed

end
