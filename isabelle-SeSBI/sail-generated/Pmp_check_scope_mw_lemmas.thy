theory Pmp_check_scope_mw_lemmas
  imports
    Pmp_check_scope_mw
    Sail.Sail2_values_lemmas
    Sail.Sail2_state_lemmas
    Sail.Add_Cancel_Distinct
begin

lemma registers_distinct:
  "distinct (map fst registers)"
  unfolding registers_def list.simps fst_conv
  by (distinct_string; simp)

lemma registers_eqs_setup:
  "!x : set registers. map_of registers (fst x) = Some (snd x)"
  using registers_distinct
  by simp

lemmas map_of_registers_eqs[simp] =
    registers_eqs_setup[simplified arg_cong[where f=set, OF registers_def]
        list.simps ball_simps fst_conv snd_conv]

lemmas get_regval_unfold = get_regval_def[THEN fun_cong,
    unfolded register_accessors_def mk_accessors_def fst_conv snd_conv]
lemmas set_regval_unfold = set_regval_def[THEN fun_cong,
    unfolded register_accessors_def mk_accessors_def fst_conv snd_conv]



lemmas register_defs = get_regval_unfold set_regval_unfold

lemma bool_of_register_value_eq_Some_iff[simp]:
  "bool_of_register_value rv = Some v \<longleftrightarrow> rv = Regval_bool v"
  by (cases rv; auto)

declare register_value_of_bool_def[simp]

lemma regval_bool[simp]:
  "bool_of_register_value (register_value_of_bool v) = Some v"
  by auto

lemma int_of_register_value_eq_Some_iff[simp]:
  "int_of_register_value rv = Some v \<longleftrightarrow> rv = Regval_int v"
  by (cases rv; auto)

declare register_value_of_int_def[simp]

lemma regval_int[simp]:
  "int_of_register_value (register_value_of_int v) = Some v"
  by auto

lemma real_of_register_value_eq_Some_iff[simp]:
  "real_of_register_value rv = Some v \<longleftrightarrow> rv = Regval_real v"
  by (cases rv; auto)

declare register_value_of_real_def[simp]

lemma regval_real[simp]:
  "real_of_register_value (register_value_of_real v) = Some v"
  by auto

lemma string_of_register_value_eq_Some_iff[simp]:
  "string_of_register_value rv = Some v \<longleftrightarrow> rv = Regval_string v"
  by (cases rv; auto)

declare register_value_of_string_def[simp]

lemma regval_string[simp]:
  "string_of_register_value (register_value_of_string v) = Some v"
  by auto

lemma bitvector_1_of_regval_eq_Some_iff[simp]:
  "bitvector_1_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_1 v"
  by (cases rv; auto)

declare regval_of_bitvector_1_def[simp]

lemma regval_bitvector_1[simp]:
  "bitvector_1_of_regval (regval_of_bitvector_1 v) = Some v"
  by auto



lemma vector_of_rv_rv_of_vector[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "vector_of_regval of_rv (regval_of_vector rv_of v) = Some v"
proof -
  from assms have "of_rv \<circ> rv_of = Some" by auto
  then show ?thesis by (auto simp: regval_of_vector_def)
qed

lemma option_of_rv_rv_of_option[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "option_of_regval of_rv (regval_of_option rv_of v) = Some v"
  using assms by (cases v) (auto simp: regval_of_option_def)

lemma list_of_rv_rv_of_list[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "list_of_regval of_rv (regval_of_list rv_of v) = Some v"
proof -
  from assms have "of_rv \<circ> rv_of = Some" by auto
  with assms show ?thesis by (induction v) (auto simp: regval_of_list_def)
qed







end
