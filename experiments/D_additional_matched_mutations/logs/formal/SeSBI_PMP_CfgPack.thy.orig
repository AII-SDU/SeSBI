theory SeSBI_PMP_CfgPack
  imports SeSBI_PMP_NAPOT
begin

unbundle bit_operations_syntax

section \<open>sbi_set_pmp's pmpcfg byte packing into the 64-bit CSR, with frame\<close>

text \<open>
  Experiment 06.  On RV64 one @{text pmpcfg} CSR holds eight entries' cfg bytes.
  sbi_set_pmp (SeSBI-code/sbi/sbi_main.c) writes one byte with a read-modify-write:

    pmpcfg_shift = (reg_idx & 7) << 3;
    cfgmask      = ~(0xffUL << pmpcfg_shift);
    pmpcfg       = (read_csr_num(pmpcfg_csr) & cfgmask)
                 | ((prot << pmpcfg_shift) & ~cfgmask);

  We model this exactly and prove the two properties that matter:
   * TARGET: the written byte @{text i} reads back as the new cfg byte.
   * FRAME : every other byte @{text "j \<noteq> i"} is unchanged.

  The frame property is precisely the "does not clobber neighbouring PMP
  entries" guarantee that the prior abstract model could not see.
\<close>

text \<open>\<open>byte_idx = reg_idx & 7\<close>; the shift is \<open>byte_idx * 8\<close>.\<close>

definition cfgmask :: "nat \<Rightarrow> 64 word" where
  "cfgmask i = NOT (push_bit (i * 8) (mask 8))"   \<comment> \<open>\<open>~(0xff << shift)\<close>\<close>

definition pmpcfg_write :: "64 word \<Rightarrow> nat \<Rightarrow> 8 word \<Rightarrow> 64 word" where
  "pmpcfg_write old i new =
     (old AND cfgmask i) OR (push_bit (i * 8) (ucast new) AND NOT (cfgmask i))"

text \<open>The cfg byte of entry \<open>j\<close>: low 8 bits of \<open>pmpcfg >> (j*8)\<close>.\<close>
definition cfg_byte :: "64 word \<Rightarrow> nat \<Rightarrow> 8 word" where
  "cfg_byte reg j = ucast (drop_bit (j * 8) reg)"

text \<open>Bit \<open>m\<close> of byte \<open>j\<close> is bit \<open>j*8+m\<close> of the register (for \<open>m < 8\<close>).\<close>
lemma bit_cfg_byte:
  fixes reg :: "64 word"
  assumes "m < 8"
  shows "bit (cfg_byte reg j) m = bit reg (j * 8 + m)"
  using assms by (simp add: cfg_byte_def bit_simps ac_simps)

text \<open>The zero-extended cfg byte has nonzero bits only below position 8.\<close>
lemma bit_ucast8:
  "bit (ucast (b :: 8 word) :: 64 word) k = (k < 8 \<and> bit b k)"
  by (auto simp: bit_ucast_iff dest: bit_imp_le_length)

text \<open>TARGET: the written byte reads back as @{term new}.\<close>
theorem cfg_byte_write_target:
  assumes i: "i < 8"
  shows "cfg_byte (pmpcfg_write old i new) i = new"
proof (rule bit_word_eqI)
  fix m :: nat assume "m < LENGTH(8)"
  hence m8: "m < 8" by simp
  have "bit (cfg_byte (pmpcfg_write old i new) i) m
          = bit (pmpcfg_write old i new) (i * 8 + m)"
    using m8 by (rule bit_cfg_byte)
  also have "\<dots> = bit new m"
    using i m8
    by (simp add: pmpcfg_write_def cfgmask_def bit_simps bit_ucast8; presburger)
  finally show "bit (cfg_byte (pmpcfg_write old i new) i) m = bit new m" .
qed

text \<open>FRAME: any other byte @{term j} is untouched.\<close>
theorem cfg_byte_write_frame:
  assumes i: "i < 8" and j: "j < 8" and ne: "i \<noteq> j"
  shows "cfg_byte (pmpcfg_write old i new) j = cfg_byte old j"
proof (rule bit_word_eqI)
  fix m :: nat assume "m < LENGTH(8)"
  hence m8: "m < 8" by simp
  have "bit (cfg_byte (pmpcfg_write old i new) j) m
          = bit (pmpcfg_write old i new) (j * 8 + m)"
    using m8 by (rule bit_cfg_byte)
  also have "\<dots> = bit old (j * 8 + m)"
  proof -
    have notbytei: "\<not> (i * 8 \<le> j * 8 + m \<and> j * 8 + m - i * 8 < 8)"
      using i j ne m8 by presburger
    have nlt: "j * 8 + m < 64" using j m8 by simp
    have keep: "bit (cfgmask i) (j * 8 + m)"
      using notbytei nlt by (simp add: cfgmask_def bit_simps)
    have nopush: "\<not> bit (push_bit (i*8) (ucast new) AND NOT (cfgmask i)) (j * 8 + m)"
      using notbytei nlt by (simp add: cfgmask_def bit_simps bit_ucast8)
    show ?thesis
      using keep nopush by (simp add: pmpcfg_write_def bit_simps)
  qed
  also have "\<dots> = bit (cfg_byte old j) m"
    using m8 by (simp add: bit_cfg_byte)
  finally show "bit (cfg_byte (pmpcfg_write old i new) j) m = bit (cfg_byte old j) m" .
qed

text \<open>
  Consequence for installation: writing entry @{term i} then reading the eight
  bytes yields @{term new} at @{term i} and the old bytes elsewhere -- so a
  sequence of sbi_set_pmp writes to distinct indices installs each entry's cfg
  byte independently, with no cross-entry interference.
\<close>
corollary pmpcfg_write_installs_independently:
  assumes "i < 8" "j < 8"
  shows "cfg_byte (pmpcfg_write old i new) j =
         (if j = i then new else cfg_byte old j)"
  using assms cfg_byte_write_target cfg_byte_write_frame by (cases "j = i") auto

end
