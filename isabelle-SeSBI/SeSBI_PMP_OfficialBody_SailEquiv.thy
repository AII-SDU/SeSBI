theory SeSBI_PMP_OfficialBody_SailEquiv
  imports
    SeSBI_PMP_OfficialBody
    "sail-generated/Pmp_official_body_mw"
begin

section \<open>Generated Sail bridge for the official pmpCheck body closure\<close>

text \<open>
  This bridge connects the local official-function-body PMP model to the
  Sail/Lem-generated definitions from
  @{text "sail-generated/pmp_official_body_mw.sail"}.

  The generated Sail file preserves the official branch structure for
  @{text pmpCheck}, @{text pmpMatchAddr}, @{text pmpCheckRWX}, and
  @{text accessFaultFromAccessType}, but takes an explicit raw PMP table
  instead of reading the full official global register state.
\<close>

definition sail_ob_match_of ::
  "PmpMatch \<Rightarrow> Pmp_official_body_mw_types.pmpAddrMatch" where
  "sail_ob_match_of m =
     (case m of
        SeSBI_PMP_NAPOT.PMP_NoMatch \<Rightarrow> Pmp_official_body_mw_types.PMP_NoMatch
      | SeSBI_PMP_NAPOT.PMP_PartialMatch \<Rightarrow> Pmp_official_body_mw_types.PMP_PartialMatch
      | SeSBI_PMP_NAPOT.PMP_Match \<Rightarrow> Pmp_official_body_mw_types.PMP_Match)"

definition sail_ob_mode_of ::
  "RawPmpAddrMode \<Rightarrow> Pmp_official_body_mw_types.PmpAddrMatchType" where
  "sail_ob_mode_of m =
     (case m of
        Raw_OFF \<Rightarrow> Pmp_official_body_mw_types.OFF
      | Raw_TOR \<Rightarrow> Pmp_official_body_mw_types.TOR
      | Raw_NA4 \<Rightarrow> Pmp_official_body_mw_types.NA4
      | Raw_NAPOT \<Rightarrow> Pmp_official_body_mw_types.NAPOT)"

definition sail_ob_priv_of ::
  "OfficialPriv \<Rightarrow> Pmp_official_body_mw_types.Privilege" where
  "sail_ob_priv_of p =
     (case p of
        Official_User \<Rightarrow> Pmp_official_body_mw_types.User
      | Official_VirtualUser \<Rightarrow> Pmp_official_body_mw_types.VirtualUser
      | Official_Supervisor \<Rightarrow> Pmp_official_body_mw_types.Supervisor
      | Official_VirtualSupervisor \<Rightarrow> Pmp_official_body_mw_types.VirtualSupervisor
      | Official_Machine \<Rightarrow> Pmp_official_body_mw_types.Machine)"

definition sail_ob_access_of ::
  "OfficialAccess \<Rightarrow> Pmp_official_body_mw_types.PmpAccess" where
  "sail_ob_access_of a =
     (case a of
        Official_Load_Data \<Rightarrow> Pmp_official_body_mw_types.Access_Load_Data
      | Official_Load_Vector \<Rightarrow> Pmp_official_body_mw_types.Access_Load_Vector
      | Official_Load_PageTableEntry \<Rightarrow> Pmp_official_body_mw_types.Access_Load_PageTableEntry
      | Official_Load_ShadowStack \<Rightarrow> Pmp_official_body_mw_types.Access_Load_ShadowStack
      | Official_LoadReserved_Data \<Rightarrow> Pmp_official_body_mw_types.Access_LoadReserved_Data
      | Official_Store_Data \<Rightarrow> Pmp_official_body_mw_types.Access_Store_Data
      | Official_Store_Vector \<Rightarrow> Pmp_official_body_mw_types.Access_Store_Vector
      | Official_Store_PageTableEntry \<Rightarrow> Pmp_official_body_mw_types.Access_Store_PageTableEntry
      | Official_Store_ShadowStack \<Rightarrow> Pmp_official_body_mw_types.Access_Store_ShadowStack
      | Official_StoreConditional_Data \<Rightarrow> Pmp_official_body_mw_types.Access_StoreConditional_Data
      | Official_Atomic_Data_Data \<Rightarrow> Pmp_official_body_mw_types.Access_Atomic_Data_Data
      | Official_Atomic_ShadowStack_ShadowStack \<Rightarrow>
          Pmp_official_body_mw_types.Access_Atomic_ShadowStack_ShadowStack
      | Official_InstructionFetch \<Rightarrow> Pmp_official_body_mw_types.Access_InstructionFetch
      | Official_Cache_CB_manage \<Rightarrow> Pmp_official_body_mw_types.Access_Cache_CB_manage
      | Official_Cache_CB_zero \<Rightarrow> Pmp_official_body_mw_types.Access_Cache_CB_zero
      | Official_Cache_Prefetch_I \<Rightarrow> Pmp_official_body_mw_types.Access_Cache_Prefetch_I
      | Official_Cache_Prefetch_R \<Rightarrow> Pmp_official_body_mw_types.Access_Cache_Prefetch_R
      | Official_Cache_Prefetch_W \<Rightarrow> Pmp_official_body_mw_types.Access_Cache_Prefetch_W)"

definition sail_ob_exception_of ::
  "OfficialException \<Rightarrow> Pmp_official_body_mw_types.PmpException" where
  "sail_ob_exception_of e =
     (case e of
        Official_Fetch_Access_Fault \<Rightarrow> Pmp_official_body_mw_types.E_Fetch_Access_Fault
      | Official_Load_Access_Fault \<Rightarrow> Pmp_official_body_mw_types.E_Load_Access_Fault
      | Official_SAMO_Access_Fault \<Rightarrow> Pmp_official_body_mw_types.E_SAMO_Access_Fault)"

definition sail_ob_cfg_of ::
  "8 word \<Rightarrow> Pmp_official_body_mw_types.Pmpcfg_ent" where
  "sail_ob_cfg_of cfg =
     \<lparr> Pmpcfg_ent_cfg_R = cfg_R cfg,
       Pmpcfg_ent_cfg_W = cfg_W cfg,
       Pmpcfg_ent_cfg_X = cfg_X cfg,
       Pmpcfg_ent_cfg_A = sail_ob_mode_of (cfg_addr_mode cfg),
       Pmpcfg_ent_cfg_L = cfg_L cfg \<rparr>"

definition sail_ob_raw_entry_of ::
  "xlenbits \<Rightarrow> 8 word \<Rightarrow> Pmp_official_body_mw_types.PmpRawEntry" where
  "sail_ob_raw_entry_of pa cfg =
     \<lparr> PmpRawEntry_raw_addr = pa,
       PmpRawEntry_raw_cfg = sail_ob_cfg_of cfg \<rparr>"

fun sail_ob_raw_entries_of ::
  "xlenbits list \<Rightarrow> 8 word list \<Rightarrow> Pmp_official_body_mw_types.PmpRawEntry list" where
  "sail_ob_raw_entries_of [] cfgs = []"
| "sail_ob_raw_entries_of (pa # pas) [] = []"
| "sail_ob_raw_entries_of (pa # pas) (cfg # cfgs) =
     sail_ob_raw_entry_of pa cfg # sail_ob_raw_entries_of pas cfgs"

lemma add_vec_int_one_ob:
  "add_vec_int (a :: 64 word) 1 = a + 1"
proof -
  have "add_vec_int a (1::int) =
        word_of_int (uint a + uint (word_of_int 1 :: 64 word))"
    unfolding add_vec_int_def arith_op_bv_int_def
              instance_Sail2_values_Bitvector_Machine_word_mword_dict_def
              int_of_mword_def
    by simp
  thus ?thesis by (simp add: word_of_int_uint)
qed

lemma pmpaddrAddr_matches_ob:
  "Pmp_official_body_mw.pmpaddrAddr pa = int (pmpaddr_addr pa)"
proof -
  have uint_eq: "uint pa = int (unat pa)"
    by (simp only: uint_nat)
  show ?thesis
    by (simp only: Pmp_official_body_mw.pmpaddrAddr_def pmpaddr_addr_def
                   uint_eq of_nat_mult of_nat_numeral)
qed

lemma napotRegion_matches_ob:
  "Pmp_official_body_mw.napotRegion pa =
   (int (fst (napot_region pa)), int (snd (napot_region pa)))"
proof -
  have add1: "add_vec_int pa ((1 :: int)::ii) = pa + 1"
    by (simp add: add_vec_int_one_ob)
  define m where "m = (pa XOR (pa + 1) :: xlenbits)"
  define b where "b = (pa AND NOT m :: xlenbits)"
  have gen:
    "Pmp_official_body_mw.napotRegion pa =
     (uint b * 4, (uint b + uint m + 1) * 4)"
    unfolding Pmp_official_body_mw.napotRegion_def Let_def
    by (simp only: add1 xor_vec_def and_vec_def not_vec_def m_def b_def)
  have loc:
    "napot_region pa = (unat b * 4, (unat b + unat m + 1) * 4)"
    unfolding napot_region_def Let_def m_def b_def by simp
  have uint_b: "uint b = int (unat b)"
    by (simp only: uint_nat)
  have uint_m: "uint m = int (unat m)"
    by (simp only: uint_nat)
  show ?thesis
    using gen loc uint_b uint_m
    by (simp only: fst_conv snd_conv of_nat_add of_nat_mult
                   of_nat_1 of_nat_numeral)
qed

lemma pmpRangeMatch_matches_ob:
  "Pmp_official_body_mw.pmpRangeMatch (int bgn) (int en) (int addr) (int width) =
   sail_ob_match_of (SeSBI_PMP_NAPOT.pmpRangeMatch bgn en addr width)"
  by (auto simp: Pmp_official_body_mw.pmpRangeMatch_def
                 SeSBI_PMP_NAPOT.pmpRangeMatch_def sail_ob_match_of_def)

lemma accessFaultFromAccessType_matches:
  "Pmp_official_body_mw.accessFaultFromAccessType (sail_ob_access_of access) =
   sail_ob_exception_of (official_access_fault access)"
  by (cases access)
     (simp_all add: sail_ob_access_of_def sail_ob_exception_of_def)

lemma pmpCheckRWX_matches:
  "Pmp_official_body_mw.pmpCheckRWX
     (sail_ob_cfg_of cfg) (sail_ob_access_of access) =
   official_cfg_allows cfg access"
  by (cases access)
     (simp_all add: sail_ob_cfg_of_def sail_ob_access_of_def)

lemma pmpLocked_matches:
  "Pmp_official_body_mw.pmpLocked (sail_ob_cfg_of cfg) = cfg_L cfg"
  by (simp add: Pmp_official_body_mw.pmpLocked_def sail_ob_cfg_of_def)

lemma pmpMatchAddr_matches:
  "Pmp_official_body_mw.pmpMatchAddr
     (int addr) (int width) (sail_ob_cfg_of cfg) pa prev =
   sail_ob_match_of (official_pmp_match_addr prev pa cfg addr width)"
proof (cases "cfg_addr_mode cfg")
  case Raw_OFF
  then show ?thesis
    by (simp add: Pmp_official_body_mw.pmpMatchAddr_def
                  official_pmp_match_addr_def official_raw_region_of_def
                  sail_ob_cfg_of_def sail_ob_mode_of_def
                  sail_ob_match_of_def)
next
  case Raw_TOR
  have cmp: "(uint prev \<ge> uint pa) = (unat prev \<ge> unat pa)"
  proof -
    have prev_uint: "uint prev = int (unat prev)"
      by (simp only: uint_nat)
    have pa_uint: "uint pa = int (unat pa)"
      by (simp only: uint_nat)
    show ?thesis
      by (simp only: prev_uint pa_uint of_nat_le_iff)
  qed
  show ?thesis
    using Raw_TOR
    by (simp add: Pmp_official_body_mw.pmpMatchAddr_def
                  official_pmp_match_addr_def official_raw_region_of_def
                  sail_ob_cfg_of_def sail_ob_mode_of_def
                  pmpaddrAddr_matches_ob pmpRangeMatch_matches_ob
                  sail_ob_match_of_def cmp)
next
  case Raw_NA4
  have range:
    "Pmp_official_body_mw.pmpRangeMatch
       (int (pmpaddr_addr pa)) (int (pmpaddr_addr pa) + 4)
       (int addr) (int width) =
     sail_ob_match_of
       (SeSBI_PMP_NAPOT.pmpRangeMatch
         (pmpaddr_addr pa) (pmpaddr_addr pa + 4) addr width)"
    using pmpRangeMatch_matches_ob[
        of "pmpaddr_addr pa" "pmpaddr_addr pa + 4" addr width]
    by simp
  show ?thesis
    using Raw_NA4 range
    by (simp add: Pmp_official_body_mw.pmpMatchAddr_def
                  official_pmp_match_addr_def official_raw_region_of_def
                  sail_ob_cfg_of_def sail_ob_mode_of_def
                  pmpaddrAddr_matches_ob)
next
  case Raw_NAPOT
  then show ?thesis
    by (simp add: Pmp_official_body_mw.pmpMatchAddr_def
                  official_pmp_match_addr_def official_raw_region_of_def
                  sail_ob_cfg_of_def sail_ob_mode_of_def
                  napotRegion_matches_ob pmpRangeMatch_matches_ob)
qed

termination Pmp_official_body_mw.pmpCheckFromPrev
  by lexicographic_order

theorem pmpCheckFromPrev_matches:
  "Pmp_official_body_mw.pmpCheckFromPrev
     prev (sail_ob_raw_entries_of pas cfgs) (int addr) (int width)
     (sail_ob_access_of access) (sail_ob_priv_of priv) =
   map_option sail_ob_exception_of
     (official_pmp_check_raw_table_from_prev
       prev pas cfgs access priv addr width)"
proof (induction pas arbitrary: prev cfgs)
  case Nil
  show ?case
    by (cases priv)
       (simp_all add: sail_ob_priv_of_def accessFaultFromAccessType_matches)
next
  case (Cons pa pas)
  show ?case
  proof (cases cfgs)
    case Nil
    then show ?thesis
      by (cases priv)
         (simp_all add: sail_ob_priv_of_def accessFaultFromAccessType_matches)
  next
    case (Cons cfg cfgs')
    have IH:
      "Pmp_official_body_mw.pmpCheckFromPrev
         pa (sail_ob_raw_entries_of pas cfgs') (int addr) (int width)
         (sail_ob_access_of access) (sail_ob_priv_of priv) =
       map_option sail_ob_exception_of
         (official_pmp_check_raw_table_from_prev
           pa pas cfgs' access priv addr width)"
      using Cons.IH by simp
    show ?thesis
      using Cons IH
      by (cases "official_pmp_match_addr prev pa cfg addr width";
          cases priv; cases access)
         (simp_all add: pmpMatchAddr_matches
                        pmpCheckRWX_matches pmpLocked_matches
                        accessFaultFromAccessType_matches
                        official_pmp_entry_check_raw_def
                        sail_ob_raw_entry_of_def sail_ob_priv_of_def
                        sail_ob_match_of_def
                        )
  qed
qed

theorem pmpCheckOfficialBody_matches:
  "Pmp_official_body_mw.pmpCheckOfficialBody
     (sail_ob_raw_entries_of pas cfgs) (int addr) (int width)
     (sail_ob_access_of access) (sail_ob_priv_of priv) =
   map_option sail_ob_exception_of
     (official_pmp_check_raw_table pas cfgs access priv addr width)"
  by (simp add: Pmp_official_body_mw.pmpCheckOfficialBody_def
                official_pmp_check_raw_table_def
                pmpCheckFromPrev_matches pmpaddr_zero_def)

corollary official_body_current_boot_sail_allows_low_priv_load:
  assumes low: "official_low_priv priv"
      and inside: "addr + width \<le> (2::nat)^64"
      and nonempty: "0 < width"
  shows "Pmp_official_body_mw.pmpCheckOfficialBody
           (sail_ob_raw_entries_of
             current_boot_raw_pmpaddrs current_boot_raw_pmpcfgs)
           (int addr) (int width)
           Pmp_official_body_mw_types.Access_Load_Data
           (sail_ob_priv_of priv) = None"
proof -
  have loc:
    "official_pmp_check_raw_table
       current_boot_raw_pmpaddrs current_boot_raw_pmpcfgs
       Official_Load_Data priv addr width = None"
    by (rule official_current_boot_allows_low_priv_load[OF low inside nonempty])
  have bridge:
    "Pmp_official_body_mw.pmpCheckOfficialBody
       (sail_ob_raw_entries_of current_boot_raw_pmpaddrs current_boot_raw_pmpcfgs)
       (int addr) (int width)
       (sail_ob_access_of Official_Load_Data) (sail_ob_priv_of priv) =
     map_option sail_ob_exception_of
       (official_pmp_check_raw_table
         current_boot_raw_pmpaddrs current_boot_raw_pmpcfgs
         Official_Load_Data priv addr width)"
    by (rule pmpCheckOfficialBody_matches)
  show ?thesis
    using bridge loc by (simp add: sail_ob_access_of_def)
qed

corollary official_body_corrected_boot_sail_isolates_low_priv:
  fixes fw_start :: xlenbits and k :: nat
  defines "fw_base \<equiv> unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4"
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
      and low: "official_low_priv priv"
      and ov: "ranges_overlap fw_base (fw_base + 2 ^ k) addr width"
  shows "Pmp_official_body_mw.pmpCheckOfficialBody
           (sail_ob_raw_entries_of
             (corrected_boot_raw_pmpaddrs fw_start k)
             corrected_boot_raw_pmpcfgs)
           (int addr) (int width)
           (sail_ob_access_of access) (sail_ob_priv_of priv) =
         Some (sail_ob_exception_of (official_access_fault access))"
proof -
  have ov':
    "ranges_overlap
       (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4)
       (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4 + 2 ^ k)
       addr width"
    using ov by (simp add: fw_base_def)
  have fault:
    "official_pmp_check_raw_table
       (corrected_boot_raw_pmpaddrs fw_start k) corrected_boot_raw_pmpcfgs
       access priv addr width = Some (official_access_fault access)"
    by (rule official_corrected_boot_isolates_low_priv[OF k_lo k_hi low ov'])
  show ?thesis
    using fault by (simp add: pmpCheckOfficialBody_matches)
qed

end
