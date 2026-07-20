theory SeSBI_PMP_RawDecode
  imports SeSBI_PMP_CheckScope SeSBI_PMP_CfgPack
begin

unbundle bit_operations_syntax

section \<open>Raw PMP CSR decode bridge\<close>

text \<open>
  This theory connects raw PMP-shaped CSR bytes and @{text pmpaddr} values back
  to the decoded @{typ PmpEntry} records used by the local PMP-check proofs.

  Scope:
   * RV64-sized @{typ xlenbits} @{text pmpaddr} values are modelled.
   * The address modes OFF, TOR, NA4, and NAPOT are decoded from the A field.
   * The SeSBI XLEN all-ones path, @{text "pmpaddr = -1UL"}, is represented by
     its S5/S7 architectural effect: an allow-all interval over @{term "2^64"}.
   * This is still a local decode bridge, not the complete official sail-riscv
     PMP state machine.
\<close>

datatype RawPmpAddrMode = Raw_OFF | Raw_TOR | Raw_NA4 | Raw_NAPOT

definition PMP_A_OFF :: "8 word" where "PMP_A_OFF = 0x00"
definition PMP_A_TOR :: "8 word" where "PMP_A_TOR = 0x08"
definition PMP_A_NA4 :: "8 word" where "PMP_A_NA4 = 0x10"

definition cfg_A_field :: "8 word \<Rightarrow> 8 word" where
  "cfg_A_field c = c AND PMP_A"

definition cfg_addr_mode :: "8 word \<Rightarrow> RawPmpAddrMode" where
  "cfg_addr_mode c =
     (if cfg_A_field c = PMP_A_OFF then Raw_OFF
      else if cfg_A_field c = PMP_A_TOR then Raw_TOR
      else if cfg_A_field c = PMP_A_NA4 then Raw_NA4
      else Raw_NAPOT)"

definition pmpaddr_addr :: "xlenbits \<Rightarrow> nat" where
  "pmpaddr_addr pa = unat pa * 4"

definition pmpaddr_all_ones :: xlenbits where
  "pmpaddr_all_ones = -1"

definition raw_region_of ::
  "xlenbits \<Rightarrow> xlenbits \<Rightarrow> 8 word \<Rightarrow> (nat \<times> nat) option" where
  "raw_region_of prev pa cfg =
     (case cfg_addr_mode cfg of
        Raw_OFF \<Rightarrow> None
      | Raw_TOR \<Rightarrow> Some (pmpaddr_addr prev, pmpaddr_addr pa)
      | Raw_NA4 \<Rightarrow> Some (pmpaddr_addr pa, pmpaddr_addr pa + 4)
      | Raw_NAPOT \<Rightarrow>
          Some (if pa = pmpaddr_all_ones then (0, (2::nat)^64)
                else napot_region pa))"

definition raw_entry_of_region :: "8 word \<Rightarrow> nat \<times> nat \<Rightarrow> PmpEntry" where
  "raw_entry_of_region cfg r =
     \<lparr> pmp_bgn = fst r, pmp_en = snd r,
       pmp_R = cfg_R cfg, pmp_W = cfg_W cfg,
       pmp_X = cfg_X cfg, pmp_L = cfg_L cfg \<rparr>"

definition decode_raw_pmp_entry ::
  "xlenbits \<Rightarrow> xlenbits \<Rightarrow> 8 word \<Rightarrow> PmpEntry option" where
  "decode_raw_pmp_entry prev pa cfg =
     map_option (raw_entry_of_region cfg) (raw_region_of prev pa cfg)"

definition prepend_decoded_raw_entry ::
  "xlenbits \<Rightarrow> xlenbits \<Rightarrow> 8 word \<Rightarrow> PmpEntry list \<Rightarrow> PmpEntry list" where
  "prepend_decoded_raw_entry prev pa cfg rest =
     (case decode_raw_pmp_entry prev pa cfg of
        None \<Rightarrow> rest
      | Some e \<Rightarrow> e # rest)"

definition decode_raw_entry_from_cfg_reg ::
  "64 word \<Rightarrow> nat \<Rightarrow> xlenbits \<Rightarrow> xlenbits \<Rightarrow> PmpEntry option" where
  "decode_raw_entry_from_cfg_reg cfgreg i prev pa =
     decode_raw_pmp_entry prev pa (cfg_byte cfgreg i)"

subsection \<open>Address-mode decode facts\<close>

lemma cfg_A_field_sbi_pmpcfg_byte:
  "cfg_A_field (sbi_pmpcfg_byte prot) = PMP_A_NAPOT"
  by (rule bit_word_eqI)
     (simp add: cfg_A_field_def sbi_pmpcfg_byte_def
                PMP_A_def PMP_A_NAPOT_def bit_simps)

lemma cfg_addr_mode_sbi_pmpcfg_byte:
  "cfg_addr_mode (sbi_pmpcfg_byte prot) = Raw_NAPOT"
  by (simp add: cfg_addr_mode_def cfg_A_field_sbi_pmpcfg_byte
                PMP_A_OFF_def PMP_A_TOR_def PMP_A_NA4_def PMP_A_NAPOT_def)

theorem decode_raw_OFF_none:
  assumes "cfg_A_field cfg = PMP_A_OFF"
  shows "decode_raw_pmp_entry prev pa cfg = None"
  using assms
  by (simp add: decode_raw_pmp_entry_def raw_region_of_def cfg_addr_mode_def)

theorem decode_raw_TOR_entry:
  assumes "cfg_A_field cfg = PMP_A_TOR"
  shows "decode_raw_pmp_entry prev pa cfg =
         Some \<lparr> pmp_bgn = pmpaddr_addr prev, pmp_en = pmpaddr_addr pa,
                pmp_R = cfg_R cfg, pmp_W = cfg_W cfg,
                pmp_X = cfg_X cfg, pmp_L = cfg_L cfg \<rparr>"
  using assms
  by (simp add: decode_raw_pmp_entry_def raw_region_of_def raw_entry_of_region_def
                cfg_addr_mode_def PMP_A_OFF_def PMP_A_TOR_def)

theorem decode_raw_NA4_entry:
  assumes "cfg_A_field cfg = PMP_A_NA4"
  shows "decode_raw_pmp_entry prev pa cfg =
         Some \<lparr> pmp_bgn = pmpaddr_addr pa, pmp_en = pmpaddr_addr pa + 4,
                pmp_R = cfg_R cfg, pmp_W = cfg_W cfg,
                pmp_X = cfg_X cfg, pmp_L = cfg_L cfg \<rparr>"
  using assms
  by (simp add: decode_raw_pmp_entry_def raw_region_of_def raw_entry_of_region_def
                cfg_addr_mode_def PMP_A_OFF_def PMP_A_TOR_def PMP_A_NA4_def)

theorem decode_raw_NAPOT_entry:
  assumes "cfg_A_field cfg = PMP_A_NAPOT"
      and "pa \<noteq> pmpaddr_all_ones"
  shows "decode_raw_pmp_entry prev pa cfg =
         Some \<lparr> pmp_bgn = fst (napot_region pa), pmp_en = snd (napot_region pa),
                pmp_R = cfg_R cfg, pmp_W = cfg_W cfg,
                pmp_X = cfg_X cfg, pmp_L = cfg_L cfg \<rparr>"
  using assms
  by (simp add: decode_raw_pmp_entry_def raw_region_of_def raw_entry_of_region_def
                cfg_addr_mode_def PMP_A_OFF_def PMP_A_TOR_def PMP_A_NA4_def
                PMP_A_NAPOT_def)

theorem decode_raw_NAPOT_all_ones_entry:
  assumes "cfg_A_field cfg = PMP_A_NAPOT"
      and "pa = pmpaddr_all_ones"
  shows "decode_raw_pmp_entry prev pa cfg =
         Some \<lparr> pmp_bgn = 0, pmp_en = (2::nat)^64,
                pmp_R = cfg_R cfg, pmp_W = cfg_W cfg,
                pmp_X = cfg_X cfg, pmp_L = cfg_L cfg \<rparr>"
  using assms
  by (simp add: decode_raw_pmp_entry_def raw_region_of_def raw_entry_of_region_def
                cfg_addr_mode_def PMP_A_OFF_def PMP_A_TOR_def PMP_A_NA4_def
                PMP_A_NAPOT_def)

subsection \<open>Connection to pmpcfg byte packing\<close>

theorem decode_from_pmpcfg_write_target:
  assumes "i < 8"
  shows "decode_raw_entry_from_cfg_reg (pmpcfg_write old i new) i prev pa =
         decode_raw_pmp_entry prev pa new"
  using cfg_byte_write_target[OF assms, of old new]
  by (simp add: decode_raw_entry_from_cfg_reg_def)

theorem decode_from_pmpcfg_write_frame:
  assumes "i < 8" "j < 8" "i \<noteq> j"
  shows "decode_raw_entry_from_cfg_reg (pmpcfg_write old i new) j prev pa =
         decode_raw_entry_from_cfg_reg old j prev pa"
  using cfg_byte_write_frame[OF assms, of old new]
  by (simp add: decode_raw_entry_from_cfg_reg_def)

subsection \<open>Connection to SeSBI sbi_set_pmp NAPOT writes\<close>

lemma pmp_encode_napot_not_all_ones:
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
  shows "pmp_encode_napot start k \<noteq> pmpaddr_all_ones"
proof
  assume eq: "pmp_encode_napot start k = pmpaddr_all_ones"
  let ?n = "k - 3"
  have n64: "?n < LENGTH(64)"
    using k_hi by simp
  have clear: "\<not> bit (pmp_encode_napot start k) ?n"
  proof -
    have n_lt: "?n < k - 2"
      using k_lo by simp
    have suc_n: "Suc ?n = k - 2"
      using k_lo by simp
    have high_clear:
      "\<not> bit (drop_bit 2 start AND NOT (mask (k-2) :: xlenbits)) ?n"
      using n64 n_lt by (simp add: bit_simps)
    have low_clear:
      "\<not> bit (drop_bit 1 (mask (k-2) :: xlenbits)) ?n"
      using suc_n by (simp add: bit_simps)
    show ?thesis
      using high_clear low_clear
      by (simp add: pmp_encode_napot_def Let_def bit_simps)
  qed
  have set: "bit pmpaddr_all_ones ?n"
    using n64 by (simp add: pmpaddr_all_ones_def)
  show False using eq clear set by simp
qed

theorem decode_raw_sbi_napot_eq_installed_entry:
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
  shows "decode_raw_pmp_entry prev (pmp_encode_napot start k) (sbi_pmpcfg_byte prot) =
         Some (installed_entry start k prot)"
  using pmp_encode_napot_not_all_ones[OF k_lo k_hi, of start]
  by (simp add: decode_raw_pmp_entry_def raw_region_of_def raw_entry_of_region_def
                installed_entry_def Let_def cfg_addr_mode_sbi_pmpcfg_byte)

theorem decode_raw_sbi_deny_napot_eq_deny_l0_entry:
  fixes start :: xlenbits and k :: nat
  defines "base \<equiv> unat (drop_bit 2 start AND NOT (mask (k-2))) * 4"
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
  shows "decode_raw_pmp_entry prev (pmp_encode_napot start k) (sbi_pmpcfg_byte 0) =
         Some (deny_l0_entry base (base + 2 ^ k))"
  using decode_raw_sbi_napot_eq_installed_entry[
          where prev=prev and start=start and prot=0, OF k_lo k_hi]
        installed_deny[OF k_lo k_hi, of start]
  by (simp add: base_def)

theorem decode_raw_sbi_allow_napot_eq_allow_l0_entry:
  fixes start :: xlenbits and k :: nat
  defines "base \<equiv> unat (drop_bit 2 start AND NOT (mask (k-2))) * 4"
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
  shows "decode_raw_pmp_entry prev (pmp_encode_napot start k) (sbi_pmpcfg_byte PMP_RWX) =
         Some (allow_l0_entry base (base + 2 ^ k))"
  using decode_raw_sbi_napot_eq_installed_entry[
          where prev=prev and start=start and prot=PMP_RWX, OF k_lo k_hi]
        installed_allow[OF k_lo k_hi, of start]
  by (simp add: base_def)

subsection \<open>SeSBI XLEN all-ones allow-all path\<close>

theorem decode_raw_xlen_allow_all_eq_allow_l0_entry:
  "decode_raw_pmp_entry prev pmpaddr_all_ones (sbi_pmpcfg_byte PMP_RWX) =
   Some (allow_l0_entry 0 ((2::nat)^64))"
  by (simp add: decode_raw_pmp_entry_def raw_region_of_def raw_entry_of_region_def
                allow_l0_entry_def cfg_addr_mode_sbi_pmpcfg_byte cfg_allow_bits)

theorem raw_decoded_current_allow_all_allows_low_priv_no_mprv:
  assumes low: "low_priv p"
      and inside: "addr + width \<le> (2::nat)^64"
      and nonempty: "0 < width"
  shows "pmp_check_scope_effective
           (prepend_decoded_raw_entry prev pmpaddr_all_ones (sbi_pmpcfg_byte PMP_RWX) rest)
           p False mpp kind addr width = PMP_Allow"
proof -
  have entries:
    "prepend_decoded_raw_entry prev pmpaddr_all_ones (sbi_pmpcfg_byte PMP_RWX) rest =
     allow_l0_entry 0 ((2::nat)^64) # rest"
    using decode_raw_xlen_allow_all_eq_allow_l0_entry[of prev]
    by (simp add: prepend_decoded_raw_entry_def)
  show ?thesis
    using scope_allow_entry_permits[of 0 addr width "(2::nat)^64" rest p kind]
          inside nonempty
    by (simp add: entries pmp_check_scope_effective_def effective_privilege_no_mprv)
qed

subsection \<open>Corrected deny-first raw decode reaches the scope theorem\<close>

theorem raw_decoded_corrected_first_isolates_effective_low_priv:
  fixes fw_start :: xlenbits and k :: nat
  defines "fw_base \<equiv> unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4"
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
      and eff_low: "low_priv (effective_privilege kind mprv mpp priv)"
      and ov: "ranges_overlap fw_base (fw_base + 2 ^ k) addr width"
  shows "pmp_check_scope_effective
           (prepend_decoded_raw_entry prev (pmp_encode_napot fw_start k) (sbi_pmpcfg_byte 0) rest)
           priv mprv mpp kind addr width = PMP_Fault"
proof -
  have entries:
    "prepend_decoded_raw_entry prev (pmp_encode_napot fw_start k) (sbi_pmpcfg_byte 0) rest =
     deny_l0_entry fw_base (fw_base + 2 ^ k) # rest"
    using decode_raw_sbi_deny_napot_eq_deny_l0_entry[
            where start=fw_start and prev=prev, OF k_lo k_hi]
    by (simp add: prepend_decoded_raw_entry_def fw_base_def)
  have fault:
    "pmp_check_scope
       (deny_l0_entry fw_base (fw_base + 2 ^ k) # rest)
       (effective_privilege kind mprv mpp priv) kind addr width = PMP_Fault"
    by (rule scope_deny_l0_faults_effective_low_priv_overlap[OF eff_low ov])
  show ?thesis
    using fault by (simp add: pmp_check_scope_effective_def entries)
qed

end
