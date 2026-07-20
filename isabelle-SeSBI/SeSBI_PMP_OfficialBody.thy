theory SeSBI_PMP_OfficialBody
  imports SeSBI_PMP_RawTable
begin

unbundle bit_operations_syntax

section \<open>Official pmpCheck function-body closure\<close>

text \<open>
  This theory models the body of the official sail-riscv PMP check over an
  explicit raw PMP table.  It keeps the official priority, partial-match fault,
  TOR reversed-bound no-match, NAPOT, RWX, lock-bit, machine-bypass, privilege,
  and access-fault branches.

  It deliberately does not model the full Sail global register monad,
  CSR write lifecycle, or @{text pmpReadAddrReg} grain/WARL behavior.  The
  generated bridge for this layer is therefore an official-function-body
  closure, not a full-register-state theorem.
\<close>

datatype OfficialPriv =
    Official_User
  | Official_VirtualUser
  | Official_Supervisor
  | Official_VirtualSupervisor
  | Official_Machine

datatype OfficialAccess =
    Official_Load_Data
  | Official_Load_Vector
  | Official_Load_PageTableEntry
  | Official_Load_ShadowStack
  | Official_LoadReserved_Data
  | Official_Store_Data
  | Official_Store_Vector
  | Official_Store_PageTableEntry
  | Official_Store_ShadowStack
  | Official_StoreConditional_Data
  | Official_Atomic_Data_Data
  | Official_Atomic_ShadowStack_ShadowStack
  | Official_InstructionFetch
  | Official_Cache_CB_manage
  | Official_Cache_CB_zero
  | Official_Cache_Prefetch_I
  | Official_Cache_Prefetch_R
  | Official_Cache_Prefetch_W

datatype OfficialException =
    Official_Fetch_Access_Fault
  | Official_Load_Access_Fault
  | Official_SAMO_Access_Fault

datatype OfficialPmpStep =
    Official_Continue
  | Official_Stop "OfficialException option"

definition official_low_priv :: "OfficialPriv \<Rightarrow> bool" where
  "official_low_priv p \<longleftrightarrow> p \<noteq> Official_Machine"

fun official_access_fault :: "OfficialAccess \<Rightarrow> OfficialException" where
  "official_access_fault Official_InstructionFetch = Official_Fetch_Access_Fault"
| "official_access_fault Official_Load_Data = Official_Load_Access_Fault"
| "official_access_fault Official_Load_Vector = Official_Load_Access_Fault"
| "official_access_fault Official_Load_PageTableEntry = Official_Load_Access_Fault"
| "official_access_fault Official_LoadReserved_Data = Official_Load_Access_Fault"
| "official_access_fault Official_Store_Data = Official_SAMO_Access_Fault"
| "official_access_fault Official_Store_Vector = Official_SAMO_Access_Fault"
| "official_access_fault Official_Store_PageTableEntry = Official_SAMO_Access_Fault"
| "official_access_fault Official_StoreConditional_Data = Official_SAMO_Access_Fault"
| "official_access_fault Official_Atomic_Data_Data = Official_SAMO_Access_Fault"
| "official_access_fault Official_Load_ShadowStack = Official_SAMO_Access_Fault"
| "official_access_fault Official_Store_ShadowStack = Official_SAMO_Access_Fault"
| "official_access_fault Official_Atomic_ShadowStack_ShadowStack = Official_SAMO_Access_Fault"
| "official_access_fault Official_Cache_CB_manage = Official_SAMO_Access_Fault"
| "official_access_fault Official_Cache_CB_zero = Official_SAMO_Access_Fault"
| "official_access_fault Official_Cache_Prefetch_R = Official_Load_Access_Fault"
| "official_access_fault Official_Cache_Prefetch_W = Official_SAMO_Access_Fault"
| "official_access_fault Official_Cache_Prefetch_I = Official_Fetch_Access_Fault"

fun official_cfg_allows :: "8 word \<Rightarrow> OfficialAccess \<Rightarrow> bool" where
  "official_cfg_allows cfg Official_Load_Data = cfg_R cfg"
| "official_cfg_allows cfg Official_Load_Vector = cfg_R cfg"
| "official_cfg_allows cfg Official_Load_PageTableEntry = cfg_R cfg"
| "official_cfg_allows cfg Official_LoadReserved_Data = cfg_R cfg"
| "official_cfg_allows cfg Official_Store_Data = cfg_W cfg"
| "official_cfg_allows cfg Official_Store_Vector = cfg_W cfg"
| "official_cfg_allows cfg Official_Store_PageTableEntry = cfg_W cfg"
| "official_cfg_allows cfg Official_StoreConditional_Data = cfg_W cfg"
| "official_cfg_allows cfg Official_Atomic_Data_Data = (cfg_R cfg \<and> cfg_W cfg)"
| "official_cfg_allows cfg Official_InstructionFetch = cfg_X cfg"
| "official_cfg_allows cfg Official_Load_ShadowStack = (cfg_R cfg \<and> cfg_W cfg)"
| "official_cfg_allows cfg Official_Store_ShadowStack = (cfg_R cfg \<and> cfg_W cfg)"
| "official_cfg_allows cfg Official_Atomic_ShadowStack_ShadowStack = (cfg_R cfg \<and> cfg_W cfg)"
| "official_cfg_allows cfg Official_Cache_CB_manage = (cfg_R cfg \<or> cfg_W cfg)"
| "official_cfg_allows cfg Official_Cache_CB_zero = cfg_W cfg"
| "official_cfg_allows cfg Official_Cache_Prefetch_I = cfg_X cfg"
| "official_cfg_allows cfg Official_Cache_Prefetch_R = cfg_R cfg"
| "official_cfg_allows cfg Official_Cache_Prefetch_W = cfg_W cfg"

definition official_raw_region_of ::
  "xlenbits \<Rightarrow> xlenbits \<Rightarrow> 8 word \<Rightarrow> (nat \<times> nat) option" where
  "official_raw_region_of prev pa cfg =
     (case cfg_addr_mode cfg of
        Raw_OFF \<Rightarrow> None
      | Raw_TOR \<Rightarrow>
          (if unat prev \<ge> unat pa then None
           else Some (pmpaddr_addr prev, pmpaddr_addr pa))
      | Raw_NA4 \<Rightarrow> Some (pmpaddr_addr pa, pmpaddr_addr pa + 4)
      | Raw_NAPOT \<Rightarrow> Some (napot_region pa))"

definition official_pmp_match_addr ::
  "xlenbits \<Rightarrow> xlenbits \<Rightarrow> 8 word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> PmpMatch" where
  "official_pmp_match_addr prev pa cfg addr width =
     (case official_raw_region_of prev pa cfg of
        None \<Rightarrow> PMP_NoMatch
      | Some (bgn, en) \<Rightarrow> pmpRangeMatch bgn en addr width)"

definition official_pmp_entry_check_raw ::
  "xlenbits \<Rightarrow> xlenbits \<Rightarrow> 8 word \<Rightarrow>
   OfficialPriv \<Rightarrow> OfficialAccess \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OfficialPmpStep" where
  "official_pmp_entry_check_raw prev pa cfg priv access addr width =
     (case official_pmp_match_addr prev pa cfg addr width of
        PMP_NoMatch \<Rightarrow> Official_Continue
      | PMP_PartialMatch \<Rightarrow> Official_Stop (Some (official_access_fault access))
      | PMP_Match \<Rightarrow>
          (if official_cfg_allows cfg access \<or>
              (priv = Official_Machine \<and> \<not> cfg_L cfg)
           then Official_Stop None
           else Official_Stop (Some (official_access_fault access))))"

fun official_pmp_check_raw_table_from_prev ::
  "xlenbits \<Rightarrow> xlenbits list \<Rightarrow> 8 word list \<Rightarrow>
   OfficialAccess \<Rightarrow> OfficialPriv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   OfficialException option" where
  "official_pmp_check_raw_table_from_prev prev [] cfgs access priv addr width =
     (if priv = Official_Machine then None else Some (official_access_fault access))"
| "official_pmp_check_raw_table_from_prev prev (pa # pas) [] access priv addr width =
     (if priv = Official_Machine then None else Some (official_access_fault access))"
| "official_pmp_check_raw_table_from_prev prev (pa # pas) (cfg # cfgs) access priv addr width =
     (case official_pmp_entry_check_raw prev pa cfg priv access addr width of
        Official_Continue \<Rightarrow>
          official_pmp_check_raw_table_from_prev pa pas cfgs access priv addr width
      | Official_Stop result \<Rightarrow> result)"

definition official_pmp_check_raw_table ::
  "xlenbits list \<Rightarrow> 8 word list \<Rightarrow>
   OfficialAccess \<Rightarrow> OfficialPriv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   OfficialException option" where
  "official_pmp_check_raw_table pas cfgs access priv addr width =
     official_pmp_check_raw_table_from_prev
       pmpaddr_zero pas cfgs access priv addr width"

lemma official_cfg_allows_deny:
  "official_cfg_allows (sbi_pmpcfg_byte 0) access = False"
  by (cases access) (simp_all add: cfg_deny_bits)

lemma official_cfg_allows_allow:
  "official_cfg_allows (sbi_pmpcfg_byte PMP_RWX) access = True"
  by (cases access) (simp_all add: cfg_allow_bits)

lemma pmpaddr_all_ones_eq_mask64:
  "pmpaddr_all_ones = (mask 64 :: xlenbits)"
  by (rule bit_word_eqI) (simp add: pmpaddr_all_ones_def bit_simps)

lemma unat_pmpaddr_all_ones:
  "unat pmpaddr_all_ones = (2::nat)^64 - 1"
proof -
  have lt: "(2::nat)^64 - 1 < 2 ^ LENGTH(64)"
    by simp
  have "unat (mask 64 :: xlenbits) = (2::nat)^64 - 1"
    by (simp add: mask_eq_decr_exp unat_of_nat lt)
  thus ?thesis
    by (simp add: pmpaddr_all_ones_eq_mask64)
qed

lemma official_napot_all_ones_covers_phys64:
  assumes inside: "addr + width \<le> (2::nat)^64"
      and nonempty: "0 < width"
  shows "pmpRangeMatch
           (fst (napot_region pmpaddr_all_ones))
           (snd (napot_region pmpaddr_all_ones))
           addr width = PMP_Match"
proof -
  have bgn_zero:
    "fst (napot_region pmpaddr_all_ones) = 0"
    by (simp add: napot_region_def pmpaddr_all_ones_def)
  have en_eq:
    "snd (napot_region pmpaddr_all_ones) =
     (unat pmpaddr_all_ones + 1) * 4"
    by (simp add: napot_region_def pmpaddr_all_ones_def)
  have en_ge:
    "(2::nat)^64 \<le> snd (napot_region pmpaddr_all_ones)"
    using en_eq by (simp add: unat_pmpaddr_all_ones)
  show ?thesis
    using inside nonempty en_ge bgn_zero
    by (simp add: pmpRangeMatch_Match_iff)
qed

theorem official_current_boot_allows_low_priv_load:
  assumes low: "official_low_priv priv"
      and inside: "addr + width \<le> (2::nat)^64"
      and nonempty: "0 < width"
  shows "official_pmp_check_raw_table
           current_boot_raw_pmpaddrs current_boot_raw_pmpcfgs
           Official_Load_Data priv addr width = None"
proof -
  have match:
    "pmpRangeMatch
       (fst (napot_region pmpaddr_all_ones))
       (snd (napot_region pmpaddr_all_ones))
       addr width = PMP_Match"
    by (rule official_napot_all_ones_covers_phys64[OF inside nonempty])
  have match':
    "(case napot_region pmpaddr_all_ones of
       (bgn, en) \<Rightarrow> pmpRangeMatch bgn en addr width) = PMP_Match"
    using match by (cases "napot_region pmpaddr_all_ones") simp
  show ?thesis
    using match' low
    by (simp add: official_pmp_check_raw_table_def
                  current_boot_raw_pmpaddrs_def current_boot_raw_pmpcfgs_def
                  official_pmp_entry_check_raw_def official_pmp_match_addr_def
                  official_raw_region_of_def cfg_addr_mode_sbi_pmpcfg_byte
                  official_low_priv_def official_cfg_allows_allow cfg_allow_bits)
qed

theorem official_corrected_boot_isolates_low_priv:
  fixes fw_start :: xlenbits and k :: nat
  defines "fw_base \<equiv> unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4"
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
      and low: "official_low_priv priv"
      and ov: "ranges_overlap fw_base (fw_base + 2 ^ k) addr width"
  shows "official_pmp_check_raw_table
           (corrected_boot_raw_pmpaddrs fw_start k) corrected_boot_raw_pmpcfgs
           access priv addr width = Some (official_access_fault access)"
proof -
  have region:
    "napot_region (pmp_encode_napot fw_start k) =
     (fw_base, fw_base + 2 ^ k)"
    using napot_interval_correct[OF k_lo k_hi, of fw_start]
    by (simp add: fw_base_def)
  have not_no:
    "pmpRangeMatch fw_base (fw_base + 2 ^ k) addr width \<noteq> PMP_NoMatch"
    using ov by (simp add: pmpRangeMatch_NoMatch_iff)
  show ?thesis
    using low not_no
    by (cases "pmpRangeMatch fw_base (fw_base + 2 ^ k) addr width")
       (simp_all add: official_pmp_check_raw_table_def
                      corrected_boot_raw_pmpaddrs_def corrected_boot_raw_pmpcfgs_def
                      official_pmp_entry_check_raw_def official_pmp_match_addr_def
                      official_raw_region_of_def cfg_addr_mode_sbi_pmpcfg_byte
                      official_low_priv_def official_cfg_allows_deny region)
qed

end
