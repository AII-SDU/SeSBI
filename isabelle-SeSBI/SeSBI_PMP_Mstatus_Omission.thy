theory SeSBI_PMP_Mstatus_Omission
  imports SeSBI_PMP_Mstatus
begin

unbundle bit_operations_syntax

section \<open>Exact-omission model for the MPIE write\<close>

text \<open>
  This theory defines an MPP-only omission variant and an MPP-plus-MPIE
  corrected variant, then proves that the S-mode-entry postcondition
  distinguishes them.

  The corrected firmware expression is:
    val = INSERT_FIELD(val, MSTATUS_MPP, PRV_S);
    val |= MSTATUS_MPIE;

  The omission variant is:
    val = INSERT_FIELD(val, MSTATUS_MPP, PRV_S);
    // MPIE not set
\<close>

subsection \<open>Buggy and corrected mode-setup paths\<close>

text \<open>The buggy path: only inserts MPP = PRV_S, does not touch MPIE.\<close>
definition buggy_mode_setup :: "64 word \<Rightarrow> 64 word" where
  "buggy_mode_setup old = insert_field old MSTATUS_MPP PRV_S"

text \<open>The corrected path: inserts MPP = PRV_S, then sets MPIE = 1.\<close>
definition corrected_mode_setup :: "64 word \<Rightarrow> 64 word" where
  "corrected_mode_setup old =
     insert_field (insert_field old MSTATUS_MPP PRV_S) MSTATUS_MPIE 1"

subsection \<open>S-mode entry postcondition on mstatus\<close>

text \<open>
  For a correct privilege transition via mret, mstatus must have:
    MPP = 01 (Supervisor)
    MPIE = 1 (interrupts enabled after mret)
\<close>
definition smode_entry_mstatus :: "64 word \<Rightarrow> bool" where
  "smode_entry_mstatus val \<longleftrightarrow>
     get_field val 11 2 = PRV_S \<and>
     get_field val 7 1 = 1"

subsection \<open>Key helper: MPIE field (bit 7) not affected by MPP write (bits 11-12)\<close>

lemma mpie_preserved_by_mpp_write:
  "get_field (insert_field old MSTATUS_MPP PRV_S) 7 1 = get_field old 7 1"
proof -
  have f7: "bit (insert_field old MSTATUS_MPP PRV_S) 7 = bit old 7"
    using mstatus_mpp_frame[of 7 old] by simp
  show ?thesis
    unfolding get_field_def
  proof (rule bit_word_eqI)
    fix n :: nat
    show "bit (drop_bit 7 (insert_field old MSTATUS_MPP PRV_S) AND mask 1) n
        = bit (drop_bit 7 old AND mask 1) n"
      using f7 by (cases "n = 0"; simp add: bit_simps)
  qed
qed

lemma mpp_preserved_by_mpie_write:
  "get_field (insert_field val MSTATUS_MPIE 1) 11 2 = get_field val 11 2"
  apply (unfold insert_MPIE_1)
  apply (unfold get_field_def MSTATUS_MPIE_def)
  apply (rule bit_word_eqI)
  apply (simp only: bit_simps possible_bit_word len64 comp_def)
  apply (case_tac "bit (val::64 word) (11 + n)"; presburger)
  done

subsection \<open>Corrected path satisfies the postcondition\<close>

theorem corrected_satisfies_postcondition:
  "smode_entry_mstatus (corrected_mode_setup old)"
proof -
  have mpp: "get_field (corrected_mode_setup old) 11 2 = PRV_S"
    unfolding corrected_mode_setup_def
    using mstatus_mpp_set mpp_preserved_by_mpie_write by simp
  have mpie: "get_field (corrected_mode_setup old) 7 1 = 1"
    unfolding corrected_mode_setup_def
    using mstatus_mpie_set by simp
  show ?thesis
    unfolding smode_entry_mstatus_def using mpp mpie by simp
qed

subsection \<open>Buggy path does NOT satisfy the postcondition when initial MPIE = 0\<close>

text \<open>
  The key insight: if the original mstatus has MPIE = 0 (which is the typical
  state after hardware reset or after entering an exception handler), the buggy
  path leaves MPIE unchanged at 0, violating the postcondition.
\<close>

theorem buggy_fails_postcondition_when_mpie_initially_zero:
  assumes initial_mpie_zero: "get_field old 7 1 = 0"
  shows "\<not> smode_entry_mstatus (buggy_mode_setup old)"
proof -
  have "get_field (buggy_mode_setup old) 7 1 = get_field old 7 1"
    unfolding buggy_mode_setup_def
    using mpie_preserved_by_mpp_write by simp
  hence "get_field (buggy_mode_setup old) 7 1 = 0"
    using initial_mpie_zero by simp
  thus ?thesis
    unfolding smode_entry_mstatus_def by simp
qed

subsection \<open>The formal property distinguishes the two variants\<close>

text \<open>
  This is the core result: under the same initial condition (MPIE = 0),
  the corrected path satisfies the postcondition while the buggy path does not.
  This demonstrates that the formal property has discriminating power over
  the specific MPIE-omission defect.
\<close>

theorem omission_distinguished:
  assumes "get_field old 7 1 = 0"
  shows "smode_entry_mstatus (corrected_mode_setup old)"
    and "\<not> smode_entry_mstatus (buggy_mode_setup old)"
  using corrected_satisfies_postcondition
        buggy_fails_postcondition_when_mpie_initially_zero[OF assms]
  by auto

subsection \<open>MPP is correctly set in both paths\<close>

text \<open>
  Both the buggy and corrected paths set MPP correctly.
  The defect is solely in the MPIE handling.
\<close>

theorem buggy_mpp_correct:
  "get_field (buggy_mode_setup old) 11 2 = PRV_S"
  unfolding buggy_mode_setup_def
  using mstatus_mpp_set by simp

theorem corrected_mpp_correct:
  "get_field (corrected_mode_setup old) 11 2 = PRV_S"
  unfolding corrected_mode_setup_def
  using mstatus_mpp_set mpp_preserved_by_mpie_write by simp

end
