theory Rv64d_lemmas
  imports
    Rv64d
    Sail.Sail2_values_lemmas
    Sail.Sail2_concurrency_interface_lemmas
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



lemmas register_defs = get_regval_unfold set_regval_unfold pmpaddr_n_ref_def pmpcfg_n_ref_def
  sig_seip_ref_def sig_meip_ref_def mideleg_ref_def medeleg_ref_def mip_ref_def mie_ref_def
  tselect_ref_def stval_ref_def scause_ref_def sepc_ref_def sscratch_ref_def stvec_ref_def
  mconfigptr_ref_def mhartid_ref_def marchid_ref_def mimpid_ref_def mvendorid_ref_def
  minstret_increment_ref_def minstret_ref_def mtime_ref_def mcycle_ref_def mcountinhibit_ref_def
  mcounteren_ref_def scounteren_ref_def mscratch_ref_def mtval_ref_def mepc_ref_def mcause_ref_def
  mtvec_ref_def senvcfg_ref_def menvcfg_ref_def mseccfg_ref_def mstatus_ref_def cur_inst_ref_def
  cur_privilege_ref_def x31_ref_def x30_ref_def x29_ref_def x28_ref_def x27_ref_def x26_ref_def
  x25_ref_def x24_ref_def x23_ref_def x22_ref_def x21_ref_def x20_ref_def x19_ref_def x18_ref_def
  x17_ref_def x16_ref_def x15_ref_def x14_ref_def x13_ref_def x12_ref_def x11_ref_def x10_ref_def
  x9_ref_def x8_ref_def x7_ref_def x6_ref_def x5_ref_def x4_ref_def x3_ref_def x2_ref_def x1_ref_def
  nextPC_ref_def PC_ref_def misa_ref_def rvfi_mem_data_present_ref_def rvfi_mem_data_ref_def
  rvfi_int_data_present_ref_def rvfi_int_data_ref_def rvfi_pc_data_ref_def rvfi_inst_data_ref_def
  rvfi_instruction_ref_def fp_rounding_global_ref_def

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

lemma Privilege_of_regval_eq_Some_iff[simp]:
  "Privilege_of_regval rv = Some v \<longleftrightarrow> rv = Regval_Privilege v"
  by (cases rv; auto)

declare regval_of_Privilege_def[simp]

lemma regval_Privilege[simp]:
  "Privilege_of_regval (regval_of_Privilege v) = Some v"
  by auto

lemma bitvector_1_of_regval_eq_Some_iff[simp]:
  "bitvector_1_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_1 v"
  by (cases rv; auto)

declare regval_of_bitvector_1_def[simp]

lemma regval_bitvector_1[simp]:
  "bitvector_1_of_regval (regval_of_bitvector_1 v) = Some v"
  by auto

lemma bitvector_128_of_regval_eq_Some_iff[simp]:
  "bitvector_128_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_128 v"
  by (cases rv; auto)

declare regval_of_bitvector_128_def[simp]

lemma regval_bitvector_128[simp]:
  "bitvector_128_of_regval (regval_of_bitvector_128 v) = Some v"
  by auto

lemma bitvector_192_of_regval_eq_Some_iff[simp]:
  "bitvector_192_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_192 v"
  by (cases rv; auto)

declare regval_of_bitvector_192_def[simp]

lemma regval_bitvector_192[simp]:
  "bitvector_192_of_regval (regval_of_bitvector_192 v) = Some v"
  by auto

lemma bitvector_32_of_regval_eq_Some_iff[simp]:
  "bitvector_32_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_32 v"
  by (cases rv; auto)

declare regval_of_bitvector_32_def[simp]

lemma regval_bitvector_32[simp]:
  "bitvector_32_of_regval (regval_of_bitvector_32 v) = Some v"
  by auto

lemma bitvector_320_of_regval_eq_Some_iff[simp]:
  "bitvector_320_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_320 v"
  by (cases rv; auto)

declare regval_of_bitvector_320_def[simp]

lemma regval_bitvector_320[simp]:
  "bitvector_320_of_regval (regval_of_bitvector_320 v) = Some v"
  by auto

lemma bitvector_5_of_regval_eq_Some_iff[simp]:
  "bitvector_5_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_5 v"
  by (cases rv; auto)

declare regval_of_bitvector_5_def[simp]

lemma regval_bitvector_5[simp]:
  "bitvector_5_of_regval (regval_of_bitvector_5 v) = Some v"
  by auto

lemma bitvector_64_of_regval_eq_Some_iff[simp]:
  "bitvector_64_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_64 v"
  by (cases rv; auto)

declare regval_of_bitvector_64_def[simp]

lemma regval_bitvector_64[simp]:
  "bitvector_64_of_regval (regval_of_bitvector_64 v) = Some v"
  by auto

lemma bitvector_704_of_regval_eq_Some_iff[simp]:
  "bitvector_704_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_704 v"
  by (cases rv; auto)

declare regval_of_bitvector_704_def[simp]

lemma regval_bitvector_704[simp]:
  "bitvector_704_of_regval (regval_of_bitvector_704 v) = Some v"
  by auto

lemma bitvector_8_of_regval_eq_Some_iff[simp]:
  "bitvector_8_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_8 v"
  by (cases rv; auto)

declare regval_of_bitvector_8_def[simp]

lemma regval_bitvector_8[simp]:
  "bitvector_8_of_regval (regval_of_bitvector_8 v) = Some v"
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
