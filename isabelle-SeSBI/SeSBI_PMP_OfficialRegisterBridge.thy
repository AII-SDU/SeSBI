theory SeSBI_PMP_OfficialRegisterBridge
  imports
    SeSBI_PMP_OfficialBody
    "sail-generated/official-pmp-register/Rv64d"
begin

section \<open>Official register-state PMP bridge\<close>

text \<open>
  This layer starts the bridge from the official Sail-generated register-state
  PMP functions to the explicit raw-table model used in Experiment 16.

  The generated @{const Rv64d.pmpCheck} is a free monad over register-read
  events.  The first step is therefore an explicit read-only interpreter for
  the generated monad, plus concrete lemmas for the official PMP register
  references.  No register event is assumed away here: unsupported events simply
  make the read-only interpreter return @{const None}.
\<close>

type_synonym 'a rv64d_monad =
  "(unit, Rv64d_types.barrier_kind0, unit, unit, bitU list, unit, unit, unit,
    unit, Rv64d_types.RISCV_strong_access, Rv64d_types.register_value, 'a,
    Rv64d_types.exception) monad"

lemma bind_dom_all_bridge:
  "bind_dom (m, f)"
  by (induction m) (auto intro: bind.domintros)

lemma try_catch_dom_all_bridge:
  "try_catch_dom (m, h)"
  by (induction m) (auto intro: try_catch.domintros)

lemma bind_Done_bridge [simp]:
  "bind (Done a) f = f a"
  by (subst bind.psimps(1)) (auto intro: bind.domintros)

lemma bind_Fail_bridge [simp]:
  "bind (Fail msg) f = Fail msg"
  by (subst bind.psimps(2)) (auto intro: bind.domintros)

lemma bind_Exception_bridge [simp]:
  "bind (Exception e) f = Exception e"
  by (subst bind.psimps(3)) (auto intro: bind.domintros)

lemma bind_Read_reg_bridge:
  "bind (Read_reg r k) f = Read_reg r (\<lambda>rv. bind (k rv) f)"
  by (subst bind.psimps(5))
     (auto intro: bind_dom_all_bridge)

lemma bind_Read_reg_decode_bridge [simp]:
  "bind
     (Read_reg r
       (\<lambda>rv. case decode rv of
          None \<Rightarrow> Fail msg
        | Some x \<Rightarrow> Done x))
     f =
   Read_reg r
     (\<lambda>rv. case decode rv of
        None \<Rightarrow> Fail msg
      | Some x \<Rightarrow> f x)"
proof -
  have dom:
    "bind_dom
      (Read_reg r
        (\<lambda>rv. case decode rv of
           None \<Rightarrow> Fail msg
         | Some x \<Rightarrow> Done x),
       f)"
    by (rule bind.domintros) (auto intro: bind.domintros split: option.splits)
  show ?thesis
    by (subst bind.psimps(5)[OF dom]) (auto split: option.splits)
qed

lemma try_catch_Done_bridge [simp]:
  "try_catch (Done a) h = Done a"
  by (subst try_catch.psimps(1)) (auto intro: try_catch.domintros)

lemma try_catch_Fail_bridge [simp]:
  "try_catch (Fail msg) h = Fail msg"
  by (subst try_catch.psimps(2)) (auto intro: try_catch.domintros)

lemma try_catch_Exception_bridge [simp]:
  "try_catch (Exception e) h = h e"
  by (subst try_catch.psimps(3)) (auto intro: try_catch.domintros)

lemma try_catch_Read_reg_bridge:
  "try_catch (Read_reg r k) h =
   Read_reg r (\<lambda>rv. try_catch (k rv) h)"
  by (subst try_catch.psimps(5))
     (auto intro: try_catch_dom_all_bridge)

lemma try_catch_Read_reg_decode_bridge [simp]:
  "try_catch
     (Read_reg r
       (\<lambda>rv. case decode rv of
          None \<Rightarrow> Fail msg
        | Some x \<Rightarrow> Done x))
     h =
   Read_reg r
     (\<lambda>rv. case decode rv of
        None \<Rightarrow> Fail msg
      | Some x \<Rightarrow> Done x)"
proof -
  have dom:
    "try_catch_dom
      (Read_reg r
        (\<lambda>rv. case decode rv of
           None \<Rightarrow> Fail msg
         | Some x \<Rightarrow> Done x),
       h)"
    by (rule try_catch.domintros)
       (auto intro: try_catch.domintros split: option.splits)
  show ?thesis
    by (subst try_catch.psimps(5)[OF dom]) (auto split: option.splits)
qed

lemma liftR_read_reg_bridge [simp]:
  "liftR (read_reg reg) = read_reg reg"
  by (simp add: liftR_def read_reg_def)

lemma liftR_return_bridge [simp]:
  "liftR (return x) = return x"
  by (simp add: liftR_def return_def)

lemma liftR_Done_bridge [simp]:
  "liftR (Done x) = Done x"
  by (simp add: liftR_def)

fun run_readonly_n ::
  "nat \<Rightarrow> (string \<Rightarrow> Rv64d_types.register_value option) \<Rightarrow>
   'a rv64d_monad \<Rightarrow> 'a option" where
  "run_readonly_n 0 env m = None"
| "run_readonly_n (Suc fuel) env (Done a) = Some a"
| "run_readonly_n (Suc fuel) env (Fail msg) = None"
| "run_readonly_n (Suc fuel) env (Exception e) = None"
| "run_readonly_n (Suc fuel) env (Choose descr k) = None"
| "run_readonly_n (Suc fuel) env (Read_reg r k) =
     (case env r of
        None \<Rightarrow> None
      | Some rv \<Rightarrow> run_readonly_n fuel env (k rv))"
| "run_readonly_n (Suc fuel) env (Write_reg r rv k) = None"
| "run_readonly_n (Suc fuel) env (Mem_read_request req k) = None"
| "run_readonly_n (Suc fuel) env (Mem_write_request req k) = None"
| "run_readonly_n (Suc fuel) env (Mem_write_announce_address req k) = None"
| "run_readonly_n (Suc fuel) env (Translation_start req k) = None"
| "run_readonly_n (Suc fuel) env (Translation_end req k) = None"
| "run_readonly_n (Suc fuel) env (Branch_announce_address addr k) = None"
| "run_readonly_n (Suc fuel) env (Barrier_request req k) = None"
| "run_readonly_n (Suc fuel) env (Cache_op_request req k) = None"
| "run_readonly_n (Suc fuel) env (TLB_op_request req k) = None"
| "run_readonly_n (Suc fuel) env (Fault_announce req k) = None"
| "run_readonly_n (Suc fuel) env (Eret_announce req k) = None"

fun run_readonly_result_n ::
  "nat \<Rightarrow> (string \<Rightarrow> Rv64d_types.register_value option) \<Rightarrow>
   (unit, Rv64d_types.barrier_kind0, unit, unit, bitU list, unit, unit,
    unit, unit, Rv64d_types.RISCV_strong_access,
    Rv64d_types.register_value, 'a, 'e) monad \<Rightarrow> ('e, 'a) sum option" where
  "run_readonly_result_n 0 env m = None"
| "run_readonly_result_n (Suc fuel) env (Done a) = Some (Inr a)"
| "run_readonly_result_n (Suc fuel) env (Fail msg) = None"
| "run_readonly_result_n (Suc fuel) env (Exception e) = Some (Inl e)"
| "run_readonly_result_n (Suc fuel) env (Choose descr k) = None"
| "run_readonly_result_n (Suc fuel) env (Read_reg r k) =
     (case env r of
        None \<Rightarrow> None
      | Some rv \<Rightarrow> run_readonly_result_n fuel env (k rv))"
| "run_readonly_result_n (Suc fuel) env (Write_reg r rv k) = None"
| "run_readonly_result_n (Suc fuel) env (Mem_read_request req k) = None"
| "run_readonly_result_n (Suc fuel) env (Mem_write_request req k) = None"
| "run_readonly_result_n (Suc fuel) env (Mem_write_announce_address req k) =
     None"
| "run_readonly_result_n (Suc fuel) env (Translation_start req k) = None"
| "run_readonly_result_n (Suc fuel) env (Translation_end req k) = None"
| "run_readonly_result_n (Suc fuel) env (Branch_announce_address addr k) =
     None"
| "run_readonly_result_n (Suc fuel) env (Barrier_request req k) = None"
| "run_readonly_result_n (Suc fuel) env (Cache_op_request req k) = None"
| "run_readonly_result_n (Suc fuel) env (TLB_op_request req k) = None"
| "run_readonly_result_n (Suc fuel) env (Fault_announce req k) = None"
| "run_readonly_result_n (Suc fuel) env (Eret_announce req k) = None"

lemma run_readonly_result_return [simp]:
  "run_readonly_result_n (Suc fuel) env (return x) = Some (Inr x)"
  by (simp add: return_def)

lemma run_readonly_result_early_return [simp]:
  "run_readonly_result_n (Suc fuel) env (early_return x) =
   Some (Inl (Inl x))"
  by (simp add: early_return_def throw_def)

lemma run_readonly_result_liftR_return [simp]:
  "run_readonly_result_n (Suc fuel) env (liftR (return x)) =
   Some (Inr x)"
  by (simp add: liftR_def return_def)

lemma run_readonly_result_liftR_from_run_readonly:
  assumes "run_readonly_n fuel env m = Some x"
  shows
    "run_readonly_result_n fuel env (liftR m) = Some (Inr x)"
  using assms
proof (induction fuel arbitrary: m)
  case 0
  thus ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases m)
    case (Done a)
    thus ?thesis
      using Suc.prems by (simp add: liftR_def)
  next
    case (Read_reg r k)
    thus ?thesis
      using Suc.prems Suc.IH
      by (auto simp: liftR_def try_catch_Read_reg_bridge split: option.splits)
  qed (use Suc.prems in \<open>simp_all add: liftR_def\<close>)
qed

lemma run_readonly_result_n_mono:
  assumes run: "run_readonly_result_n fuel env m = Some r"
      and le: "fuel \<le> fuel'"
  shows "run_readonly_result_n fuel' env m = Some r"
  using run le
proof (induction fuel arbitrary: fuel' m)
  case 0
  thus ?case by simp
next
  case (Suc fuel)
  then obtain fuel'' where fuel'_eq: "fuel' = Suc fuel''"
    by (cases fuel') auto
  show ?case
  proof (cases m)
    case (Read_reg reg k)
    show ?thesis
    proof (cases "env reg")
      case None
      thus ?thesis
        using Suc.prems Read_reg by simp
    next
      case (Some rv)
      have "run_readonly_result_n fuel env (k rv) = Some r"
        using Suc.prems Read_reg Some by simp
      moreover have "fuel \<le> fuel''"
        using Suc.prems fuel'_eq by simp
      ultimately show ?thesis
        using Suc.IH[of "k rv" fuel''] Read_reg Some fuel'_eq
        by simp
    qed
  qed (use Suc.prems fuel'_eq in \<open>simp_all\<close>)
qed

lemma run_readonly_result_bind_Inr:
  assumes left: "run_readonly_result_n fuel_m env m = Some (Inr x)"
      and right: "run_readonly_result_n fuel_f env (f x) = Some r"
  shows
    "run_readonly_result_n (fuel_m + fuel_f) env (bind m f) = Some r"
  using left
proof (induction fuel_m arbitrary: m)
  case 0
  thus ?case by simp
next
  case (Suc fuel_m)
  show ?case
  proof (cases m)
    case (Done a)
    hence x_eq: "x = a"
      using Suc.prems by simp
    have "run_readonly_result_n fuel_f env (f a) = Some r"
      using right x_eq by simp
    thus ?thesis
      using Done
      by (auto intro: run_readonly_result_n_mono)
  next
    case (Read_reg reg k)
    show ?thesis
    proof (cases "env reg")
      case None
      thus ?thesis
        using Suc.prems Read_reg by simp
    next
      case (Some rv)
      have sub: "run_readonly_result_n fuel_m env (k rv) = Some (Inr x)"
        using Suc.prems Read_reg Some by simp
      show ?thesis
        using Suc.IH[OF sub] Read_reg Some
        by (simp add: bind_Read_reg_bridge)
    qed
  qed (use Suc.prems in \<open>simp_all\<close>)
qed

lemma run_readonly_result_bind_Inl:
  assumes left: "run_readonly_result_n fuel_m env m = Some (Inl e)"
  shows
    "run_readonly_result_n (fuel_m + fuel_f) env (bind m f) = Some (Inl e)"
  using left
proof (induction fuel_m arbitrary: m)
  case 0
  thus ?case by simp
next
  case (Suc fuel_m)
  show ?case
  proof (cases m)
    case (Exception e')
    thus ?thesis
      using Suc.prems by (simp add: bind_Exception_bridge)
  next
    case (Read_reg reg k)
    show ?thesis
    proof (cases "env reg")
      case None
      thus ?thesis
        using Suc.prems Read_reg by simp
    next
      case (Some rv)
      have sub: "run_readonly_result_n fuel_m env (k rv) = Some (Inl e)"
        using Suc.prems Read_reg Some by simp
      show ?thesis
        using Suc.IH[OF sub] Read_reg Some
        by (simp add: bind_Read_reg_bridge)
    qed
  qed (use Suc.prems in \<open>simp_all\<close>)
qed

definition official_pmp_register_env ::
  "(bitU list) list \<Rightarrow> (bitU list) list \<Rightarrow>
   string \<Rightarrow> Rv64d_types.register_value option" where
  "official_pmp_register_env cfgs addrs nm =
     (if nm = name Rv64d_types.pmpcfg_n_ref then
        Some (regval_of Rv64d_types.pmpcfg_n_ref cfgs)
      else if nm = name Rv64d_types.pmpaddr_n_ref then
        Some (regval_of Rv64d_types.pmpaddr_n_ref addrs)
      else None)"

lemma just_list_map_Some_bridge [simp]:
  "just_list (map Some xs) = Some xs"
  by (induction xs) auto

lemma vector_of_regval_of_vector_bitvector_8 [simp]:
  "Rv64d_types.vector_of_regval Rv64d_types.bitvector_8_of_regval
     (Rv64d_types.regval_of_vector Rv64d_types.regval_of_bitvector_8 xs) =
   Some xs"
  by (induction xs)
     (simp_all add: Rv64d_types.regval_of_vector_def
                    Rv64d_types.regval_of_bitvector_8_def)

lemma vector_of_regval_of_vector_bitvector_64 [simp]:
  "Rv64d_types.vector_of_regval Rv64d_types.bitvector_64_of_regval
     (Rv64d_types.regval_of_vector Rv64d_types.regval_of_bitvector_64 xs) =
   Some xs"
  by (induction xs)
     (simp_all add: Rv64d_types.regval_of_vector_def
                    Rv64d_types.regval_of_bitvector_64_def)

lemma official_pmp_register_env_cfg_name [simp]:
  "official_pmp_register_env cfgs addrs ''pmpcfg_n'' =
   Some (regval_of Rv64d_types.pmpcfg_n_ref cfgs)"
  by (simp add: official_pmp_register_env_def
                Rv64d_types.pmpcfg_n_ref_def Rv64d_types.pmpaddr_n_ref_def)

lemma official_pmp_register_env_addr_name [simp]:
  "official_pmp_register_env cfgs addrs ''pmpaddr_n'' =
   Some (regval_of Rv64d_types.pmpaddr_n_ref addrs)"
  by (simp add: official_pmp_register_env_def
                Rv64d_types.pmpcfg_n_ref_def Rv64d_types.pmpaddr_n_ref_def)

lemma official_pmp_register_env_cfg [simp]:
  "official_pmp_register_env cfgs addrs (name Rv64d_types.pmpcfg_n_ref) =
   Some (regval_of Rv64d_types.pmpcfg_n_ref cfgs)"
  by (simp add: official_pmp_register_env_def)

lemma official_pmp_register_env_addr [simp]:
  "official_pmp_register_env cfgs addrs (name Rv64d_types.pmpaddr_n_ref) =
   Some (regval_of Rv64d_types.pmpaddr_n_ref addrs)"
  by (simp add: official_pmp_register_env_def
                Rv64d_types.pmpcfg_n_ref_def Rv64d_types.pmpaddr_n_ref_def)

lemma run_readonly_read_pmpcfg_n:
  "run_readonly_n (Suc (Suc fuel)) (official_pmp_register_env cfgs addrs)
     (read_reg Rv64d_types.pmpcfg_n_ref) =
   Some cfgs"
  by (simp add: read_reg_def return_def Rv64d_types.pmpcfg_n_ref_def)

lemma run_readonly_read_pmpaddr_n:
  "run_readonly_n (Suc (Suc fuel)) (official_pmp_register_env cfgs addrs)
     (read_reg Rv64d_types.pmpaddr_n_ref) =
   Some addrs"
  by (simp add: read_reg_def return_def Rv64d_types.pmpaddr_n_ref_def)

theorem pmpReadAddrReg_grain0_reads_raw_addr:
  "run_readonly_n (Suc (Suc (Suc fuel)))
     (official_pmp_register_env cfgs addrs)
     (Rv64d.pmpReadAddrReg n) =
   Some (access_list_dec addrs n)"
  by (simp add: Rv64d.pmpReadAddrReg_def Rv64d.sys_pmp_grain_def
                read_reg_def return_def
                Rv64d_types.pmpcfg_n_ref_def Rv64d_types.pmpaddr_n_ref_def)

subsection \<open>Generated access and exception constructors\<close>

definition rv_priv_of :: "OfficialPriv \<Rightarrow> Rv64d_types.Privilege" where
  "rv_priv_of priv =
     (case priv of
        Official_User \<Rightarrow> Rv64d_types.User
      | Official_VirtualUser \<Rightarrow> Rv64d_types.VirtualUser
      | Official_Supervisor \<Rightarrow> Rv64d_types.Supervisor
      | Official_VirtualSupervisor \<Rightarrow> Rv64d_types.VirtualSupervisor
      | Official_Machine \<Rightarrow> Rv64d_types.Machine)"

definition rv_access_of ::
  "OfficialAccess \<Rightarrow> Rv64d_types.mem_payload Rv64d_types.MemoryAccessType" where
  "rv_access_of access =
     (case access of
        Official_Load_Data \<Rightarrow> Rv64d_types.Load Rv64d_types.Data
      | Official_Load_Vector \<Rightarrow> Rv64d_types.Load Rv64d_types.Vector
      | Official_Load_PageTableEntry \<Rightarrow>
          Rv64d_types.Load Rv64d_types.PageTableEntry
      | Official_Load_ShadowStack \<Rightarrow>
          Rv64d_types.Load Rv64d_types.ShadowStack
      | Official_LoadReserved_Data \<Rightarrow>
          Rv64d_types.LoadReserved (False, False, Rv64d_types.Data)
      | Official_Store_Data \<Rightarrow> Rv64d_types.Store Rv64d_types.Data
      | Official_Store_Vector \<Rightarrow> Rv64d_types.Store Rv64d_types.Vector
      | Official_Store_PageTableEntry \<Rightarrow>
          Rv64d_types.Store Rv64d_types.PageTableEntry
      | Official_Store_ShadowStack \<Rightarrow>
          Rv64d_types.Store Rv64d_types.ShadowStack
      | Official_StoreConditional_Data \<Rightarrow>
          Rv64d_types.StoreConditional (False, False, Rv64d_types.Data)
      | Official_Atomic_Data_Data \<Rightarrow>
          Rv64d_types.Atomic
            (Rv64d_types.AMOSWAP, False, False,
             Rv64d_types.Data, Rv64d_types.Data)
      | Official_Atomic_ShadowStack_ShadowStack \<Rightarrow>
          Rv64d_types.Atomic
            (Rv64d_types.AMOSWAP, False, False,
             Rv64d_types.ShadowStack, Rv64d_types.ShadowStack)
      | Official_InstructionFetch \<Rightarrow> Rv64d_types.InstructionFetch ()
      | Official_Cache_CB_manage \<Rightarrow>
          Rv64d_types.CacheAccess
            (Rv64d_types.CB_manage Rv64d_types.CBO_CLEAN)
      | Official_Cache_CB_zero \<Rightarrow>
          Rv64d_types.CacheAccess (Rv64d_types.CB_zero ())
      | Official_Cache_Prefetch_I \<Rightarrow>
          Rv64d_types.CacheAccess
            (Rv64d_types.CB_prefetch Rv64d_types.PREFETCH_I)
      | Official_Cache_Prefetch_R \<Rightarrow>
          Rv64d_types.CacheAccess
            (Rv64d_types.CB_prefetch Rv64d_types.PREFETCH_R)
      | Official_Cache_Prefetch_W \<Rightarrow>
          Rv64d_types.CacheAccess
            (Rv64d_types.CB_prefetch Rv64d_types.PREFETCH_W))"

definition rv_exception_of ::
  "OfficialException \<Rightarrow> Rv64d_types.ExceptionType" where
  "rv_exception_of ex =
     (case ex of
        Official_Fetch_Access_Fault \<Rightarrow>
          Rv64d_types.E_Fetch_Access_Fault ()
      | Official_Load_Access_Fault \<Rightarrow>
          Rv64d_types.E_Load_Access_Fault ()
      | Official_SAMO_Access_Fault \<Rightarrow>
          Rv64d_types.E_SAMO_Access_Fault ())"

lemma rv_priv_machine_iff [simp]:
  "rv_priv_of priv = Rv64d_types.Machine \<longleftrightarrow> priv = Official_Machine"
  by (cases priv) (simp_all add: rv_priv_of_def)

theorem rv_accessFaultFromAccessType_matches:
  "run_readonly_n (Suc fuel) env
     (Rv64d.accessFaultFromAccessType (rv_access_of access)) =
   Some (rv_exception_of (official_access_fault access))"
  by (cases access)
     (simp_all add: Rv64d.accessFaultFromAccessType_def
                    rv_access_of_def rv_exception_of_def return_def)

lemma rv_accessFaultFromAccessType_return [simp]:
  "Rv64d.accessFaultFromAccessType (rv_access_of access) =
   return (rv_exception_of (official_access_fault access))"
  by (cases access)
     (simp_all add: Rv64d.accessFaultFromAccessType_def
                    rv_access_of_def rv_exception_of_def return_def)

lemma liftR_accessFaultFromAccessType_return [simp]:
  "liftR (Rv64d.accessFaultFromAccessType (rv_access_of access)) =
   return (rv_exception_of (official_access_fault access))"
  by simp

definition rv_bit_set :: "bitU list \<Rightarrow> bool" where
  "rv_bit_set b \<longleftrightarrow> eq_vec b [B1]"

fun rv_cfg_allows_bits ::
  "bitU list \<Rightarrow> OfficialAccess \<Rightarrow> bool" where
  "rv_cfg_allows_bits cfg Official_Load_Data =
     rv_bit_set (Rv64d.get_Pmpcfg_ent_R cfg)"
| "rv_cfg_allows_bits cfg Official_Load_Vector =
     rv_bit_set (Rv64d.get_Pmpcfg_ent_R cfg)"
| "rv_cfg_allows_bits cfg Official_Load_PageTableEntry =
     rv_bit_set (Rv64d.get_Pmpcfg_ent_R cfg)"
| "rv_cfg_allows_bits cfg Official_LoadReserved_Data =
     rv_bit_set (Rv64d.get_Pmpcfg_ent_R cfg)"
| "rv_cfg_allows_bits cfg Official_Store_Data =
     rv_bit_set (Rv64d.get_Pmpcfg_ent_W cfg)"
| "rv_cfg_allows_bits cfg Official_Store_Vector =
     rv_bit_set (Rv64d.get_Pmpcfg_ent_W cfg)"
| "rv_cfg_allows_bits cfg Official_Store_PageTableEntry =
     rv_bit_set (Rv64d.get_Pmpcfg_ent_W cfg)"
| "rv_cfg_allows_bits cfg Official_StoreConditional_Data =
     rv_bit_set (Rv64d.get_Pmpcfg_ent_W cfg)"
| "rv_cfg_allows_bits cfg Official_Atomic_Data_Data =
     (rv_bit_set (Rv64d.get_Pmpcfg_ent_R cfg) \<and>
      rv_bit_set (Rv64d.get_Pmpcfg_ent_W cfg))"
| "rv_cfg_allows_bits cfg Official_InstructionFetch =
     rv_bit_set (Rv64d.get_Pmpcfg_ent_X cfg)"
| "rv_cfg_allows_bits cfg Official_Load_ShadowStack =
     (rv_bit_set (Rv64d.get_Pmpcfg_ent_R cfg) \<and>
      rv_bit_set (Rv64d.get_Pmpcfg_ent_W cfg))"
| "rv_cfg_allows_bits cfg Official_Store_ShadowStack =
     (rv_bit_set (Rv64d.get_Pmpcfg_ent_R cfg) \<and>
      rv_bit_set (Rv64d.get_Pmpcfg_ent_W cfg))"
| "rv_cfg_allows_bits cfg Official_Atomic_ShadowStack_ShadowStack =
     (rv_bit_set (Rv64d.get_Pmpcfg_ent_R cfg) \<and>
      rv_bit_set (Rv64d.get_Pmpcfg_ent_W cfg))"
| "rv_cfg_allows_bits cfg Official_Cache_CB_manage =
     (rv_bit_set (Rv64d.get_Pmpcfg_ent_R cfg) \<or>
      rv_bit_set (Rv64d.get_Pmpcfg_ent_W cfg))"
| "rv_cfg_allows_bits cfg Official_Cache_CB_zero =
     rv_bit_set (Rv64d.get_Pmpcfg_ent_W cfg)"
| "rv_cfg_allows_bits cfg Official_Cache_Prefetch_I =
     rv_bit_set (Rv64d.get_Pmpcfg_ent_X cfg)"
| "rv_cfg_allows_bits cfg Official_Cache_Prefetch_R =
     rv_bit_set (Rv64d.get_Pmpcfg_ent_R cfg)"
| "rv_cfg_allows_bits cfg Official_Cache_Prefetch_W =
     rv_bit_set (Rv64d.get_Pmpcfg_ent_W cfg)"

theorem rv_pmpCheckRWX_matches_bits:
  "run_readonly_n (Suc fuel) env
     (Rv64d.pmpCheckRWX cfg (rv_access_of access)) =
   Some (rv_cfg_allows_bits cfg access)"
  by (cases access)
     (simp_all add: Rv64d.pmpCheckRWX_def rv_access_of_def
                    rv_cfg_allows_bits.simps rv_bit_set_def return_def)

lemma rv_pmpCheckRWX_return_bits [simp]:
  "Rv64d.pmpCheckRWX cfg (rv_access_of access) =
   return (rv_cfg_allows_bits cfg access)"
  by (cases access)
     (simp_all add: Rv64d.pmpCheckRWX_def rv_access_of_def
                    rv_cfg_allows_bits.simps rv_bit_set_def return_def)

subsection \<open>PMP cfg-byte bit order\<close>

definition rv_cfg_bits_of_word :: "8 word \<Rightarrow> bitU list" where
  "rv_cfg_bits_of_word cfg =
     [bitU_of_bool (bit cfg 7), bitU_of_bool (bit cfg 6),
      bitU_of_bool (bit cfg 5), bitU_of_bool (bit cfg 4),
      bitU_of_bool (bit cfg 3), bitU_of_bool (bit cfg 2),
      bitU_of_bool (bit cfg 1), bitU_of_bool (bit cfg 0)]"

lemma rv_cfg_bits_of_word_len [simp]:
  "length (rv_cfg_bits_of_word cfg) = 8"
  by (simp add: rv_cfg_bits_of_word_def)

lemma rv_cfg_single_bit_0 [simp]:
  "subrange_vec_dec (rv_cfg_bits_of_word cfg) 0 0 =
   [bitU_of_bool (bit cfg 0)]"
  by (simp add: rv_cfg_bits_of_word_def subrange_vec_dec_def
                subrange_bv_dec_def subrange_list_def subrange_list_dec_def
                subrange_list_inc_def access_list_dec_def access_list_inc_def
                instance_Sail2_values_Bitvector_list_dict_def
                instance_Sail2_values_BitU_Sail2_values_bitU_dict_def
                split_at_def nat_of_int_def bitU_of_bool_def)

lemma rv_cfg_single_bit_1 [simp]:
  "subrange_vec_dec (rv_cfg_bits_of_word cfg) 1 1 =
   [bitU_of_bool (bit cfg 1)]"
  by (simp add: rv_cfg_bits_of_word_def subrange_vec_dec_def
                subrange_bv_dec_def subrange_list_def subrange_list_dec_def
                subrange_list_inc_def access_list_dec_def access_list_inc_def
                instance_Sail2_values_Bitvector_list_dict_def
                instance_Sail2_values_BitU_Sail2_values_bitU_dict_def
                split_at_def nat_of_int_def bitU_of_bool_def)

lemma rv_cfg_single_bit_2 [simp]:
  "subrange_vec_dec (rv_cfg_bits_of_word cfg) 2 2 =
   [bitU_of_bool (bit cfg 2)]"
  by (simp add: rv_cfg_bits_of_word_def subrange_vec_dec_def
                subrange_bv_dec_def subrange_list_def subrange_list_dec_def
                subrange_list_inc_def access_list_dec_def access_list_inc_def
                instance_Sail2_values_Bitvector_list_dict_def
                instance_Sail2_values_BitU_Sail2_values_bitU_dict_def
                split_at_def nat_of_int_def bitU_of_bool_def)

lemma rv_cfg_single_bit_7 [simp]:
  "subrange_vec_dec (rv_cfg_bits_of_word cfg) 7 7 =
   [bitU_of_bool (bit cfg 7)]"
  by (simp add: rv_cfg_bits_of_word_def subrange_vec_dec_def
                subrange_bv_dec_def subrange_list_def subrange_list_dec_def
                subrange_list_inc_def access_list_dec_def access_list_inc_def
                instance_Sail2_values_Bitvector_list_dict_def
                instance_Sail2_values_BitU_Sail2_values_bitU_dict_def
                split_at_def nat_of_int_def bitU_of_bool_def)

lemma rv_cfg_A_bits [simp]:
  "Rv64d.get_Pmpcfg_ent_A (rv_cfg_bits_of_word cfg) =
   [bitU_of_bool (bit cfg 4), bitU_of_bool (bit cfg 3)]"
  by (simp add: rv_cfg_bits_of_word_def Rv64d.get_Pmpcfg_ent_A_def
                subrange_vec_dec_def subrange_bv_dec_def subrange_list_def
                subrange_list_dec_def subrange_list_inc_def split_at_def
                nat_of_int_def
                instance_Sail2_values_Bitvector_list_dict_def
                instance_Sail2_values_BitU_Sail2_values_bitU_dict_def
                bitU_of_bool_def)

lemma rv_bit_set_bool [simp]:
  "rv_bit_set [bitU_of_bool b] = b"
  by (cases b)
     (simp_all add: rv_bit_set_def eq_vec_def eq_bv_def bitU_of_bool_def
                    instance_Sail2_values_Bitvector_list_dict_def
                    instance_Sail2_values_BitU_Sail2_values_bitU_dict_def)

lemma rv_cfg_R_matches [simp]:
  "rv_bit_set (Rv64d.get_Pmpcfg_ent_R (rv_cfg_bits_of_word cfg)) = cfg_R cfg"
  by (simp add: Rv64d.get_Pmpcfg_ent_R_def cfg_R_def)

lemma rv_cfg_W_matches [simp]:
  "rv_bit_set (Rv64d.get_Pmpcfg_ent_W (rv_cfg_bits_of_word cfg)) = cfg_W cfg"
  by (simp add: Rv64d.get_Pmpcfg_ent_W_def cfg_W_def)

lemma rv_cfg_X_matches [simp]:
  "rv_bit_set (Rv64d.get_Pmpcfg_ent_X (rv_cfg_bits_of_word cfg)) = cfg_X cfg"
  by (simp add: Rv64d.get_Pmpcfg_ent_X_def cfg_X_def)

lemma rv_cfg_L_matches [simp]:
  "rv_bit_set (Rv64d.get_Pmpcfg_ent_L (rv_cfg_bits_of_word cfg)) = cfg_L cfg"
  by (simp add: Rv64d.get_Pmpcfg_ent_L_def cfg_L_def)

theorem rv_cfg_allows_bits_matches_official:
  "rv_cfg_allows_bits (rv_cfg_bits_of_word cfg) access =
   official_cfg_allows cfg access"
  by (cases access) simp_all

theorem rv_pmpCheckRWX_matches:
  "run_readonly_n (Suc fuel) env
     (Rv64d.pmpCheckRWX (rv_cfg_bits_of_word cfg) (rv_access_of access)) =
   Some (official_cfg_allows cfg access)"
  using rv_cfg_allows_bits_matches_official[of cfg access]
  by (simp add: return_def)

lemma rv_pmpCheckRWX_return [simp]:
  "Rv64d.pmpCheckRWX (rv_cfg_bits_of_word cfg) (rv_access_of access) =
   return (official_cfg_allows cfg access)"
  using rv_cfg_allows_bits_matches_official[of cfg access]
  by (simp add: return_def)

lemma liftR_pmpCheckRWX_return [simp]:
  "liftR
     (Rv64d.pmpCheckRWX (rv_cfg_bits_of_word cfg) (rv_access_of access)) =
   return (official_cfg_allows cfg access)"
  using rv_cfg_allows_bits_matches_official[of cfg access]
  by (simp add: liftR_def return_def)

lemma run_readonly_result_liftR_accessFault:
  "run_readonly_result_n (Suc fuel) env
     (liftR (Rv64d.accessFaultFromAccessType (rv_access_of access))) =
   Some (Inr (rv_exception_of (official_access_fault access)))"
  by (cases access)
     (simp_all add: liftR_def Rv64d.accessFaultFromAccessType_def
                    rv_access_of_def rv_exception_of_def return_def)

lemma run_readonly_result_liftR_pmpCheckRWX:
  "run_readonly_result_n (Suc fuel) env
     (liftR
       (Rv64d.pmpCheckRWX (rv_cfg_bits_of_word cfg)
          (rv_access_of access))) =
   Some (Inr (official_cfg_allows cfg access))"
  using rv_cfg_allows_bits_matches_official[of cfg access]
  by (simp add: liftR_def return_def)

definition rv_addr_mode_of ::
  "RawPmpAddrMode \<Rightarrow> Rv64d_types.PmpAddrMatchType" where
  "rv_addr_mode_of mode =
     (case mode of
        Raw_OFF \<Rightarrow> Rv64d_types.OFF
      | Raw_TOR \<Rightarrow> Rv64d_types.TOR
      | Raw_NA4 \<Rightarrow> Rv64d_types.NA4
      | Raw_NAPOT \<Rightarrow> Rv64d_types.NAPOT)"

lemma cfg_A_field_by_bits:
  "cfg_A_field cfg =
   (if bit cfg 4 then
      if bit cfg 3 then PMP_A_NAPOT else PMP_A_NA4
    else
      if bit cfg 3 then PMP_A_TOR else PMP_A_OFF)"
proof (rule bit_word_eqI)
  fix n
  assume n: "n < LENGTH(8)"
  have n8: "n < 8"
    using n by simp
  hence "n = 0 \<or> n = 1 \<or> n = 2 \<or> n = 3 \<or>
         n = 4 \<or> n = 5 \<or> n = 6 \<or> n = 7"
    by arith
  thus "bit (cfg_A_field cfg) n =
        bit (if bit cfg 4 then
               if bit cfg 3 then PMP_A_NAPOT else PMP_A_NA4
             else
               if bit cfg 3 then PMP_A_TOR else PMP_A_OFF) n"
    by (auto simp: cfg_A_field_def PMP_A_def PMP_A_OFF_def PMP_A_TOR_def
                   PMP_A_NA4_def PMP_A_NAPOT_def bit_simps)
qed

theorem rv_addr_mode_matches:
  "Rv64d.pmpAddrMatchType_encdec_backwards
     (Rv64d.get_Pmpcfg_ent_A (rv_cfg_bits_of_word cfg)) =
   rv_addr_mode_of (cfg_addr_mode cfg)"
  by (cases "bit cfg 4"; cases "bit cfg 3")
     (simp_all add: Rv64d.pmpAddrMatchType_encdec_backwards_def
                    rv_addr_mode_of_def cfg_addr_mode_def cfg_A_field_by_bits
                    PMP_A_def PMP_A_OFF_def PMP_A_TOR_def PMP_A_NA4_def
                    PMP_A_NAPOT_def eq_vec_def eq_bv_def bitU_of_bool_def
                    instance_Sail2_values_Bitvector_list_dict_def
                    instance_Sail2_values_BitU_Sail2_values_bitU_dict_def
                    bit_simps)

definition rv_pmp_match_of :: "PmpMatch \<Rightarrow> Rv64d_types.pmpAddrMatch" where
  "rv_pmp_match_of m =
     (case m of
        SeSBI_PMP_NAPOT.PMP_NoMatch \<Rightarrow> Rv64d_types.PMP_NoMatch
      | SeSBI_PMP_NAPOT.PMP_PartialMatch \<Rightarrow> Rv64d_types.PMP_PartialMatch
      | SeSBI_PMP_NAPOT.PMP_Match \<Rightarrow> Rv64d_types.PMP_Match)"

theorem rv_pmpRangeMatch_matches:
  "Rv64d.pmpRangeMatch (int bgn) (int en) (int addr) (int width) =
   rv_pmp_match_of (SeSBI_PMP_NAPOT.pmpRangeMatch bgn en addr width)"
  by (auto simp: Rv64d.pmpRangeMatch_def
                 SeSBI_PMP_NAPOT.pmpRangeMatch_def rv_pmp_match_of_def)

lemma rv_uint_le_unat_iff:
  fixes x y :: "64 word"
  shows "(uint x \<le> uint y) = (unat x \<le> unat y)"
  by (simp only: uint_nat of_nat_le_iff)

lemma rv_pmpRangeMatch_word_bounds:
  fixes bgn en :: "64 word"
  shows
    "Rv64d.pmpRangeMatch (uint bgn * 4) (uint en * 4)
       (int addr) (int width) =
     rv_pmp_match_of
       (SeSBI_PMP_NAPOT.pmpRangeMatch
         (unat bgn * 4) (unat en * 4) addr width)"
proof -
  have bgn_eq: "uint bgn * 4 = int (unat bgn * 4)"
    by (simp only: uint_nat of_nat_mult of_nat_numeral)
  have en_eq: "uint en * 4 = int (unat en * 4)"
    by (simp only: uint_nat of_nat_mult of_nat_numeral)
  show ?thesis
    by (simp only: bgn_eq en_eq rv_pmpRangeMatch_matches)
qed

lemma rv_pmpRangeMatch_word_na4:
  fixes pa :: "64 word"
  shows
    "Rv64d.pmpRangeMatch (uint pa * 4) (uint pa * 4 + 4)
       (int addr) (int width) =
     rv_pmp_match_of
       (SeSBI_PMP_NAPOT.pmpRangeMatch
         (unat pa * 4) (unat pa * 4 + 4) addr width)"
proof -
  have bgn_eq: "uint pa * 4 = int (unat pa * 4)"
    by (simp only: uint_nat of_nat_mult of_nat_numeral)
  have en_eq: "uint pa * 4 + 4 = int (unat pa * 4 + 4)"
    by (simp only: uint_nat of_nat_mult of_nat_add of_nat_numeral)
  have en_eq': "int (unat pa * 4) + 4 = int (unat pa * 4 + 4)"
    by simp
  show ?thesis
    by (simp only: bgn_eq en_eq en_eq' rv_pmpRangeMatch_matches)
qed

lemma rv_pmpRangeMatch_word_napot:
  fixes b m :: "64 word"
  shows
    "Rv64d.pmpRangeMatch (uint b * 4) ((uint b + uint m + 1) * 4)
       (int addr) (int width) =
     rv_pmp_match_of
       (SeSBI_PMP_NAPOT.pmpRangeMatch
         (unat b * 4) ((unat b + unat m + 1) * 4) addr width)"
proof -
  have bgn_eq: "uint b * 4 = int (unat b * 4)"
    by (simp only: uint_nat of_nat_mult of_nat_numeral)
  have en_eq:
    "(uint b + uint m + 1) * 4 =
     int ((unat b + unat m + 1) * 4)"
    by (simp only: uint_nat of_nat_add of_nat_1 of_nat_mult
                   of_nat_numeral)
  show ?thesis
    by (simp only: bgn_eq en_eq rv_pmpRangeMatch_matches)
qed

lemma rv_pmpRangeMatch_word_napot_distrib:
  fixes b m :: "64 word"
  shows
    "Rv64d.pmpRangeMatch (uint b * 4) (uint b * 4 + uint m * 4 + 4)
       (int addr) (int width) =
     rv_pmp_match_of
       (SeSBI_PMP_NAPOT.pmpRangeMatch
         (unat b * 4) (4 + (unat b * 4 + unat m * 4)) addr width)"
proof -
  have bgn_eq: "uint b * 4 = int (unat b * 4)"
    by (simp only: uint_nat of_nat_mult of_nat_numeral)
  have en_eq:
    "uint b * 4 + uint m * 4 + 4 =
     int (4 + (unat b * 4 + unat m * 4))"
    by (simp only: uint_nat of_nat_add of_nat_mult of_nat_numeral)
  have en_eq':
    "int (unat b * 4) + uint m * 4 + 4 =
     int (4 + (unat b * 4 + unat m * 4))"
    by (simp only: uint_nat of_nat_add of_nat_mult of_nat_numeral)
  show ?thesis
    by (simp only: bgn_eq en_eq en_eq' rv_pmpRangeMatch_matches)
qed

definition rv_bits_of_word64 :: "64 word \<Rightarrow> bitU list" where
  "rv_bits_of_word64 w = map bitU_of_bool (to_bl w)"

lemma rv_bits_of_word64_len [simp]:
  "length (rv_bits_of_word64 w) = 64"
  by (simp add: rv_bits_of_word64_def)

lemma rv_nat_of_bools_aux_bl_to_bin_aux:
  "nat_of_bools_aux acc bs = nat (bl_to_bin_aux bs (int acc))"
  by (induction acc bs rule: nat_of_bools_aux.induct) auto

lemma rv_nat_of_bools_bl_to_bin:
  "nat_of_bools bs = nat (bl_to_bin bs)"
  by (simp add: nat_of_bools_def bl_to_bin_def
                rv_nat_of_bools_aux_bl_to_bin_aux)

lemma rv_bools_of_nat_aux_simps [simp]:
  "\<And>len. len \<le> 0 \<Longrightarrow> bools_of_nat_aux len x acc = acc"
  "\<And>len. bools_of_nat_aux (int (Suc len)) x acc =
     bools_of_nat_aux (int len) (x div 2)
       ((if x mod 2 = 1 then True else False) # acc)"
  by auto

declare bools_of_nat_aux.simps [simp del]

lemma rv_bools_of_nat_aux_bin_to_bl_aux:
  "bools_of_nat_aux len n acc = bin_to_bl_aux (nat len) (int n) acc"
proof (cases len)
  case (nonneg len')
  show ?thesis unfolding nonneg
  proof (induction len' arbitrary: n acc)
    case (Suc len'' n acc)
    then show ?case
      using zmod_int[of n 2]
      by (cases "odd n") (auto simp del: of_nat_simps simp add: zdiv_int)
  qed auto
qed auto

lemma rv_bools_of_nat_bin_to_bl:
  "bools_of_nat len n = bin_to_bl (nat len) (int n)"
  by (simp add: bools_of_nat_def rv_bools_of_nat_aux_bin_to_bl_aux
                bin_to_bl_def)

lemma rv_add_one_bool_ignore_overflow_aux_rbl_succ [simp]:
  "add_one_bool_ignore_overflow_aux xs = rbl_succ xs"
  by (induction xs) auto

lemma rv_add_one_bool_ignore_overflow_rbl_succ [simp]:
  "add_one_bool_ignore_overflow xs = rev (rbl_succ (rev xs))"
  by (simp add: add_one_bool_ignore_overflow_def)

lemma rv_map_Not_bin_to_bl:
  "map Not (bin_to_bl_aux len n acc) =
   bin_to_bl_aux len (- n - 1) (map Not acc)"
proof (induction len arbitrary: n acc)
  case (Suc len n acc)
  moreover have "(- (n div 2) - 1) = ((- n - 1) div 2)" by auto
  moreover have "(n mod 2 = 0) = ((- n - 1) mod 2 = 1)" by presburger
  ultimately show ?case by (auto simp: bin_last_def)
qed auto

lemma rv_bools_of_int_bin_to_bl:
  "bools_of_int len n = bin_to_bl (nat len) n"
  by (auto simp: bools_of_int_def Let_def rv_bools_of_nat_bin_to_bl
                 rv_map_Not_bin_to_bl rbl_succ[unfolded bin_to_bl_def])

lemma rv_bool_of_bitU_bitU_of_bool [simp]:
  "bool_of_bitU (bitU_of_bool b) = Some b"
  by (cases b) (simp_all add: bool_of_bitU_def bitU_of_bool_def)

lemma rv_bits_of_int_64_word:
  "bits_of_int 64 n = rv_bits_of_word64 (word_of_int n :: 64 word)"
  by (simp add: bits_of_int_def rv_bits_of_word64_def
                rv_bools_of_int_bin_to_bl to_bl_of_bin)

lemma unsigned_of_bits_rv_bits_of_word64 [simp]:
  "unsigned_of_bits (rv_bits_of_word64 w) = Some (uint w)"
  by (simp add: rv_bits_of_word64_def unsigned_of_bits_def
                unsigned_of_bools_def rv_nat_of_bools_bl_to_bin
                to_bl_to_bin comp_def)

lemma uint0_rv_bits_of_word64 [simp]:
  "uint0 (rv_bits_of_word64 w) = uint w"
  by (simp add: rv_bits_of_word64_def uint0_def uint_maybe_def
                maybe_failwith_def unsigned_of_bits_def unsigned_of_bools_def
                rv_nat_of_bools_bl_to_bin to_bl_to_bin comp_def)

lemma rv_int_of_bits_false_bits_of_word64 [simp]:
  "int_of_bits False (rv_bits_of_word64 w) = Some (uint w)"
  by (simp add: int_of_bits_def)

lemma rv_int_of_bits_false_bits_of_int_64_one [simp]:
  "int_of_bits False (bits_of_int 64 1) = Some 1"
  by (simp add: int_of_bits_def rv_bits_of_int_64_word)

lemma rv_add_vec_int_word64_one_bits:
  "add_vec_int (rv_bits_of_word64 w) 1 = bits_of_int 64 (uint w + 1)"
  by (simp add: add_vec_int_def arith_op_bv_int_def
                instance_Sail2_values_Bitvector_list_dict_def
                instance_Sail2_values_BitU_Sail2_values_bitU_dict_def
                arith_op_bits_def)

lemma rv_add_vec_int_word64_one [simp]:
  "add_vec_int (rv_bits_of_word64 w) 1 = rv_bits_of_word64 (w + 1)"
proof -
  have word_eq: "(word_of_int (uint w + 1) :: 64 word) = w + 1"
  proof -
    have "w + (1 :: 64 word) = word_of_int (uint w + uint (1 :: 64 word))"
      by (simp only: word_arith_wis)
    also have "\<dots> = word_of_int (uint w + 1)"
      by (simp only: uint_1)
    finally show ?thesis by (rule sym)
  qed
  show ?thesis
    by (simp add: rv_add_vec_int_word64_one_bits rv_bits_of_int_64_word
                  word_eq)
qed

lemma rv_binop_list_eq_map2:
  "binop_list f xs ys = map2 f xs ys"
proof (induction xs arbitrary: ys)
  case Nil
  show ?case by (simp add: binop_list_def)
next
  case (Cons x xs)
  show ?case
  proof (cases ys)
    case Nil
    show ?thesis by (simp add: binop_list_def Nil)
  next
    case (Cons y ys')
    show ?thesis
      using Cons.IH[of ys']
      by (simp add: binop_list_def Cons)
  qed
qed

lemma rv_and_bit_bitU_of_bool [simp]:
  "and_bit (bitU_of_bool x) (bitU_of_bool y) = bitU_of_bool (x \<and> y)"
  by (cases x; cases y) (simp_all add: bitU_of_bool_def)

lemma rv_xor_bit_bitU_of_bool [simp]:
  "xor_bit (bitU_of_bool x) (bitU_of_bool y) = bitU_of_bool (x \<noteq> y)"
  by (cases x; cases y) (simp_all add: bitU_of_bool_def)

lemma rv_not_bit_bitU_of_bool [simp]:
  "not_bit (bitU_of_bool x) = bitU_of_bool (\<not> x)"
  by (cases x) (simp_all add: bitU_of_bool_def not_bit_def)

lemma rv_map2_xor_bitU_of_bool:
  "map2 xor_bit (map bitU_of_bool xs) (map bitU_of_bool ys) =
   map bitU_of_bool (map2 (\<lambda>x y. x \<noteq> y) xs ys)"
proof (induction xs arbitrary: ys)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases ys)
    case Nil
    show ?thesis by (simp add: Nil)
  next
    case (Cons y ys')
    show ?thesis
      using Cons.IH[of ys']
      by (simp add: Cons comp_def)
  qed
qed

lemma rv_map2_and_bitU_of_bool:
  "map2 and_bit (map bitU_of_bool xs) (map bitU_of_bool ys) =
   map bitU_of_bool (map2 (\<lambda>x y. x \<and> y) xs ys)"
proof (induction xs arbitrary: ys)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases ys)
    case Nil
    show ?thesis by (simp add: Nil)
  next
    case (Cons y ys')
    show ?thesis
      using Cons.IH[of ys']
      by (simp add: Cons comp_def)
  qed
qed

lemma rv_not_vec_bits_of_word64 [simp]:
  "not_vec (rv_bits_of_word64 w) = rv_bits_of_word64 (NOT w)"
  by (simp add: rv_bits_of_word64_def not_vec_def bl_word_not)

lemma rv_xor_vec_bits_of_word64 [simp]:
  "xor_vec (rv_bits_of_word64 x) (rv_bits_of_word64 y) =
   rv_bits_of_word64 (x XOR y)"
  by (simp add: rv_bits_of_word64_def xor_vec_def rv_binop_list_eq_map2
                bl_word_xor rv_map2_xor_bitU_of_bool)

lemma rv_and_vec_bits_of_word64 [simp]:
  "and_vec (rv_bits_of_word64 x) (rv_bits_of_word64 y) =
   rv_bits_of_word64 (x AND y)"
  by (simp add: rv_bits_of_word64_def and_vec_def rv_binop_list_eq_map2
                bl_word_and rv_map2_and_bitU_of_bool)

subsection \<open>Generated address matching, non-NAPOT branches\<close>

theorem rv_pmpMatchAddr_OFF:
  assumes mode: "cfg_addr_mode cfg = Raw_OFF"
  shows
    "run_readonly_n (Suc fuel) env
       (Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
          (rv_cfg_bits_of_word cfg) pa_bits prev_bits) =
     Some (rv_pmp_match_of
       (official_pmp_match_addr prev pa cfg addr width))"
proof -
  have amode:
    "Rv64d.pmpAddrMatchType_encdec_backwards
       (Rv64d.get_Pmpcfg_ent_A (rv_cfg_bits_of_word cfg)) = Rv64d_types.OFF"
    using mode
    by (simp del: rv_cfg_A_bits
        add: rv_addr_mode_matches rv_addr_mode_of_def)
  show ?thesis
    using mode
    by (simp del: rv_cfg_A_bits
        add: Rv64d.pmpMatchAddr.simps return_def amode
             official_pmp_match_addr_def official_raw_region_of_def
             rv_pmp_match_of_def)
qed

theorem rv_pmpMatchAddr_TOR:
  assumes mode: "cfg_addr_mode cfg = Raw_TOR"
      and prev_u: "uint0 prev_bits = int (unat prev)"
      and pa_u: "uint0 pa_bits = int (unat pa)"
      and addr_u: "uint0 addr_bits = int addr"
      and width_u: "uint0 width_bits = int width"
  shows
    "run_readonly_n (Suc fuel) env
       (Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
          (rv_cfg_bits_of_word cfg) pa_bits prev_bits) =
     Some (rv_pmp_match_of
       (official_pmp_match_addr prev pa cfg addr width))"
proof -
  have amode:
    "Rv64d.pmpAddrMatchType_encdec_backwards
       (Rv64d.get_Pmpcfg_ent_A (rv_cfg_bits_of_word cfg)) = Rv64d_types.TOR"
    using mode
    by (simp del: rv_cfg_A_bits
        add: rv_addr_mode_matches rv_addr_mode_of_def)
  show ?thesis
    using mode prev_u pa_u addr_u width_u
    by (simp del: rv_cfg_A_bits
        add: Rv64d.pmpMatchAddr.simps return_def amode
             Rv64d.zopz0zKzJ_u_def official_pmp_match_addr_def
             official_raw_region_of_def pmpaddr_addr_def
             rv_uint_le_unat_iff rv_pmpRangeMatch_word_bounds
             rv_pmp_match_of_def)
qed

theorem rv_pmpMatchAddr_NA4:
  assumes mode: "cfg_addr_mode cfg = Raw_NA4"
      and pa_u: "uint0 pa_bits = int (unat pa)"
      and addr_u: "uint0 addr_bits = int addr"
      and width_u: "uint0 width_bits = int width"
  shows
    "run_readonly_n (Suc fuel) env
       (Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
          (rv_cfg_bits_of_word cfg) pa_bits prev_bits) =
     Some (rv_pmp_match_of
       (official_pmp_match_addr prev pa cfg addr width))"
proof -
  have amode:
    "Rv64d.pmpAddrMatchType_encdec_backwards
       (Rv64d.get_Pmpcfg_ent_A (rv_cfg_bits_of_word cfg)) = Rv64d_types.NA4"
    using mode
    by (simp del: rv_cfg_A_bits
        add: rv_addr_mode_matches rv_addr_mode_of_def)
  show ?thesis
    using mode pa_u addr_u width_u
    by (simp del: rv_cfg_A_bits
        add: Rv64d.pmpMatchAddr.simps return_def assert_exp_def
             Rv64d.sys_pmp_grain_def amode official_pmp_match_addr_def
             official_raw_region_of_def pmpaddr_addr_def
             rv_pmpRangeMatch_word_na4)
qed

theorem rv_pmpMatchAddr_NAPOT:
  assumes mode: "cfg_addr_mode cfg = Raw_NAPOT"
      and addr_u: "uint0 addr_bits = int addr"
      and width_u: "uint0 width_bits = int width"
  shows
    "run_readonly_n (Suc fuel) env
       (Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
          (rv_cfg_bits_of_word cfg) (rv_bits_of_word64 pa) prev_bits) =
     Some (rv_pmp_match_of
       (official_pmp_match_addr prev pa cfg addr width))"
proof -
  have amode:
    "Rv64d.pmpAddrMatchType_encdec_backwards
       (Rv64d.get_Pmpcfg_ent_A (rv_cfg_bits_of_word cfg)) = Rv64d_types.NAPOT"
    using mode
    by (simp del: rv_cfg_A_bits
        add: rv_addr_mode_matches rv_addr_mode_of_def)
  show ?thesis
    using mode addr_u width_u
    by (simp del: rv_cfg_A_bits
        add: Rv64d.pmpMatchAddr.simps return_def amode
             official_pmp_match_addr_def official_raw_region_of_def
             napot_region_def Let_def rv_pmpRangeMatch_word_napot
             rv_pmpRangeMatch_word_napot_distrib)
qed

theorem rv_pmpMatchAddr_matches:
  assumes addr_u: "uint0 addr_bits = int addr"
      and width_u: "uint0 width_bits = int width"
  shows
    "run_readonly_n (Suc fuel) env
       (Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
          (rv_cfg_bits_of_word cfg) (rv_bits_of_word64 pa)
          (rv_bits_of_word64 prev)) =
     Some (rv_pmp_match_of
       (official_pmp_match_addr prev pa cfg addr width))"
proof (cases "cfg_addr_mode cfg")
  case Raw_OFF
  show ?thesis
    by (rule rv_pmpMatchAddr_OFF[OF Raw_OFF])
next
  case Raw_TOR
  have prev_u: "uint0 (rv_bits_of_word64 prev) = int (unat prev)"
    by (simp only: uint0_rv_bits_of_word64 uint_nat)
  have pa_u: "uint0 (rv_bits_of_word64 pa) = int (unat pa)"
    by (simp only: uint0_rv_bits_of_word64 uint_nat)
  show ?thesis
    by (rule rv_pmpMatchAddr_TOR[OF Raw_TOR prev_u pa_u addr_u width_u])
next
  case Raw_NA4
  have pa_u: "uint0 (rv_bits_of_word64 pa) = int (unat pa)"
    by (simp only: uint0_rv_bits_of_word64 uint_nat)
  show ?thesis
    by (rule rv_pmpMatchAddr_NA4[OF Raw_NA4 pa_u addr_u width_u])
next
  case Raw_NAPOT
  show ?thesis
    by (rule rv_pmpMatchAddr_NAPOT[OF Raw_NAPOT addr_u width_u])
qed

theorem rv_pmpMatchAddr_return_OFF:
  assumes mode: "cfg_addr_mode cfg = Raw_OFF"
  shows
    "Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
       (rv_cfg_bits_of_word cfg) pa_bits prev_bits =
     return (rv_pmp_match_of
       (official_pmp_match_addr prev pa cfg addr width))"
proof -
  have amode:
    "Rv64d.pmpAddrMatchType_encdec_backwards
       (Rv64d.get_Pmpcfg_ent_A (rv_cfg_bits_of_word cfg)) = Rv64d_types.OFF"
    using mode
    by (simp del: rv_cfg_A_bits
        add: rv_addr_mode_matches rv_addr_mode_of_def)
  show ?thesis
    using mode
    by (simp del: rv_cfg_A_bits
        add: Rv64d.pmpMatchAddr.simps return_def amode
             official_pmp_match_addr_def official_raw_region_of_def
             rv_pmp_match_of_def)
qed

theorem rv_pmpMatchAddr_return_TOR:
  assumes mode: "cfg_addr_mode cfg = Raw_TOR"
      and prev_u: "uint0 prev_bits = int (unat prev)"
      and pa_u: "uint0 pa_bits = int (unat pa)"
      and addr_u: "uint0 addr_bits = int addr"
      and width_u: "uint0 width_bits = int width"
  shows
    "Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
       (rv_cfg_bits_of_word cfg) pa_bits prev_bits =
     return (rv_pmp_match_of
       (official_pmp_match_addr prev pa cfg addr width))"
proof -
  have amode:
    "Rv64d.pmpAddrMatchType_encdec_backwards
       (Rv64d.get_Pmpcfg_ent_A (rv_cfg_bits_of_word cfg)) = Rv64d_types.TOR"
    using mode
    by (simp del: rv_cfg_A_bits
        add: rv_addr_mode_matches rv_addr_mode_of_def)
  show ?thesis
    using mode prev_u pa_u addr_u width_u
    by (simp del: rv_cfg_A_bits
        add: Rv64d.pmpMatchAddr.simps return_def amode
             Rv64d.zopz0zKzJ_u_def official_pmp_match_addr_def
             official_raw_region_of_def pmpaddr_addr_def
             rv_uint_le_unat_iff rv_pmpRangeMatch_word_bounds
             rv_pmp_match_of_def)
qed

theorem rv_pmpMatchAddr_return_NA4:
  assumes mode: "cfg_addr_mode cfg = Raw_NA4"
      and pa_u: "uint0 pa_bits = int (unat pa)"
      and addr_u: "uint0 addr_bits = int addr"
      and width_u: "uint0 width_bits = int width"
  shows
    "Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
       (rv_cfg_bits_of_word cfg) pa_bits prev_bits =
     return (rv_pmp_match_of
       (official_pmp_match_addr prev pa cfg addr width))"
proof -
  have amode:
    "Rv64d.pmpAddrMatchType_encdec_backwards
       (Rv64d.get_Pmpcfg_ent_A (rv_cfg_bits_of_word cfg)) = Rv64d_types.NA4"
    using mode
    by (simp del: rv_cfg_A_bits
        add: rv_addr_mode_matches rv_addr_mode_of_def)
  show ?thesis
    using mode pa_u addr_u width_u
    by (simp del: rv_cfg_A_bits
        add: Rv64d.pmpMatchAddr.simps return_def assert_exp_def
             Rv64d.sys_pmp_grain_def amode official_pmp_match_addr_def
             official_raw_region_of_def pmpaddr_addr_def
             rv_pmpRangeMatch_word_na4)
qed

theorem rv_pmpMatchAddr_return_NAPOT:
  assumes mode: "cfg_addr_mode cfg = Raw_NAPOT"
      and addr_u: "uint0 addr_bits = int addr"
      and width_u: "uint0 width_bits = int width"
  shows
    "Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
       (rv_cfg_bits_of_word cfg) (rv_bits_of_word64 pa) prev_bits =
     return (rv_pmp_match_of
       (official_pmp_match_addr prev pa cfg addr width))"
proof -
  have amode:
    "Rv64d.pmpAddrMatchType_encdec_backwards
       (Rv64d.get_Pmpcfg_ent_A (rv_cfg_bits_of_word cfg)) = Rv64d_types.NAPOT"
    using mode
    by (simp del: rv_cfg_A_bits
        add: rv_addr_mode_matches rv_addr_mode_of_def)
  show ?thesis
    using mode addr_u width_u
    by (simp del: rv_cfg_A_bits
        add: Rv64d.pmpMatchAddr.simps return_def amode
             official_pmp_match_addr_def official_raw_region_of_def
             napot_region_def Let_def rv_pmpRangeMatch_word_napot
             rv_pmpRangeMatch_word_napot_distrib)
qed

theorem rv_pmpMatchAddr_return:
  assumes addr_u: "uint0 addr_bits = int addr"
      and width_u: "uint0 width_bits = int width"
  shows
    "Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
       (rv_cfg_bits_of_word cfg) (rv_bits_of_word64 pa)
       (rv_bits_of_word64 prev) =
     return (rv_pmp_match_of
       (official_pmp_match_addr prev pa cfg addr width))"
proof (cases "cfg_addr_mode cfg")
  case Raw_OFF
  show ?thesis
    by (rule rv_pmpMatchAddr_return_OFF[OF Raw_OFF])
next
  case Raw_TOR
  have prev_u: "uint0 (rv_bits_of_word64 prev) = int (unat prev)"
    by (simp only: uint0_rv_bits_of_word64 uint_nat)
  have pa_u: "uint0 (rv_bits_of_word64 pa) = int (unat pa)"
    by (simp only: uint0_rv_bits_of_word64 uint_nat)
  show ?thesis
    by (rule rv_pmpMatchAddr_return_TOR[OF Raw_TOR prev_u pa_u addr_u width_u])
next
  case Raw_NA4
  have pa_u: "uint0 (rv_bits_of_word64 pa) = int (unat pa)"
    by (simp only: uint0_rv_bits_of_word64 uint_nat)
  show ?thesis
    by (rule rv_pmpMatchAddr_return_NA4[OF Raw_NA4 pa_u addr_u width_u])
next
  case Raw_NAPOT
  show ?thesis
    by (rule rv_pmpMatchAddr_return_NAPOT[OF Raw_NAPOT addr_u width_u])
qed

subsection \<open>Generated PMP table-vector order\<close>

definition rv_cfg_vector :: "8 word list \<Rightarrow> bitU list list" where
  "rv_cfg_vector cfgs = rev (map rv_cfg_bits_of_word cfgs)"

definition rv_addr_vector :: "64 word list \<Rightarrow> bitU list list" where
  "rv_addr_vector addrs = rev (map rv_bits_of_word64 addrs)"

lemma access_list_dec_rev_map_nth:
  assumes i_nonneg: "0 \<le> i"
      and i_lt: "nat i < length xs"
  shows "access_list_dec (rev (map f xs)) i = f (xs ! nat i)"
proof -
  have idx:
    "length xs - nat (i + 1) = length xs - Suc (nat i)"
    using i_nonneg by simp
  have i_eq: "i = int (nat i)"
    using i_nonneg by simp
  have top_not_less:
    "\<not> int (length xs) - 1 < i"
    using i_lt i_eq by linarith
  have nat_abs_idx:
    "nat \<bar>int (length xs) - 1 - i\<bar> =
     length xs - nat (i + 1)"
    using i_nonneg i_lt i_eq idx
    by simp
  have "access_list_dec (rev (map f xs)) i =
        rev (map f xs) ! (length xs - nat (i + 1))"
    using i_nonneg i_lt top_not_less nat_abs_idx
    by (simp add: access_list_dec_def access_list_inc_def nat_of_int_def
                  Let_def)
  also have "\<dots> = f (xs ! nat i)"
    using i_lt idx
    by (simp add: rev_nth)
  finally show ?thesis .
qed

lemma access_rv_cfg_vector:
  assumes "0 \<le> i" and "nat i < length cfgs"
  shows "access_list_dec (rv_cfg_vector cfgs) i =
         rv_cfg_bits_of_word (cfgs ! nat i)"
  using assms
  by (simp add: rv_cfg_vector_def access_list_dec_rev_map_nth)

lemma access_rv_addr_vector:
  assumes "0 \<le> i" and "nat i < length addrs"
  shows "access_list_dec (rv_addr_vector addrs) i =
         rv_bits_of_word64 (addrs ! nat i)"
  using assms
  by (simp add: rv_addr_vector_def access_list_dec_rev_map_nth)

lemma rv_pmpLocked_matches [simp]:
  "Rv64d.pmpLocked (rv_cfg_bits_of_word cfg) = cfg_L cfg"
proof -
  have "rv_bit_set (Rv64d.get_Pmpcfg_ent_L (rv_cfg_bits_of_word cfg)) =
        cfg_L cfg"
    by simp
  thus ?thesis
    by (simp add: Rv64d.pmpLocked_def rv_bit_set_def)
qed

lemma rv_zeros64_word0 [simp]:
  "Rv64d.zeros' 64 = rv_bits_of_word64 (0 :: 64 word)"
  by (simp add: Rv64d.zeros'_def zeros_def rv_bits_of_word64_def
                bitU_of_bool_def repeat.simps replicate.simps
                numeral_eq_Suc)

lemma rv_length_bin_to_bl_aux [simp]:
  "length (bin_to_bl_aux len n acc) = len + length acc"
  by (induction len arbitrary: n acc) auto

lemma rv_length_bools_of_int_64 [simp]:
  "length (bools_of_int 64 n) = 64"
  by (simp add: rv_bools_of_int_bin_to_bl bin_to_bl_def)

lemma rv_to_bits64_bits_of_int:
  "Rv64d.to_bits 64 n = bits_of_int 64 n"
  by (simp add: Rv64d.to_bits_def get_slice_int_def get_slice_int_bv_def
                bits_of_int_def subrange_list_def subrange_list_dec_def
                subrange_list_inc_def split_at_def nat_of_int_def
                instance_Sail2_values_Bitvector_list_dict_def
                instance_Sail2_values_BitU_Sail2_values_bitU_dict_def)

lemma uint0_to_bits64_nat:
  assumes "w < (2::nat)^64"
  shows "uint0 (Rv64d.to_bits 64 (int w)) = int w"
proof -
  have uint_eq: "uint (of_nat w :: 64 word) = int w"
    using assms
    by (simp add: uint_nat unat_of_nat)
  show ?thesis
    by (simp add: rv_to_bits64_bits_of_int rv_bits_of_int_64_word
                  uint_eq)
qed

lemma run_readonly_pmpReadAddrReg_rv_addr_vector:
  assumes i_nonneg: "0 \<le> i"
      and i_lt: "nat i < length addrs"
  shows
    "run_readonly_n (Suc (Suc (Suc fuel)))
       (official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs))
       (Rv64d.pmpReadAddrReg i) =
     Some (rv_bits_of_word64 (addrs ! nat i))"
  using assms
  by (simp add: pmpReadAddrReg_grain0_reads_raw_addr
                access_rv_addr_vector)

lemma run_readonly_result_liftR_pmpReadAddrReg_rv_addr_vector:
  assumes i_nonneg: "0 \<le> i"
      and i_lt: "nat i < length addrs"
  shows
    "run_readonly_result_n (Suc (Suc (Suc fuel)))
       (official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs))
       (liftR (Rv64d.pmpReadAddrReg i)) =
     Some (Inr (rv_bits_of_word64 (addrs ! nat i)))"
  by (rule run_readonly_result_liftR_from_run_readonly)
     (simp add: run_readonly_pmpReadAddrReg_rv_addr_vector assms)

lemma run_readonly_read_pmpcfg_rv_cfg_vector:
  "run_readonly_n (Suc (Suc fuel))
     (official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs))
     (read_reg Rv64d_types.pmpcfg_n_ref) =
   Some (rv_cfg_vector cfgs)"
  by (simp add: run_readonly_read_pmpcfg_n)

lemma run_readonly_result_liftR_read_pmpcfg_rv_cfg_vector:
  "run_readonly_result_n (Suc (Suc fuel))
     (official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs))
     (liftR (read_reg Rv64d_types.pmpcfg_n_ref)) =
   Some (Inr (rv_cfg_vector cfgs))"
  by (simp add: liftR_def read_reg_def return_def
                Rv64d_types.pmpcfg_n_ref_def)

definition rv_prev_addr_at :: "64 word list \<Rightarrow> int \<Rightarrow> 64 word" where
  "rv_prev_addr_at addrs i =
     (if nat i = 0 then pmpaddr_zero else addrs ! (nat i - 1))"

lemma rv_prev_addr_bits:
  assumes i_nonneg: "0 \<le> i"
      and i_lt: "nat i < length addrs"
  shows
    "(if i > 0 then access_list_dec (rv_addr_vector addrs) (i - 1)
      else Rv64d.zeros' 64) =
     rv_bits_of_word64 (rv_prev_addr_at addrs i)"
proof (cases "nat i")
  case 0
  hence "i = 0"
    using i_nonneg by simp
  thus ?thesis
    by (simp add: rv_prev_addr_at_def pmpaddr_zero_def)
next
  case (Suc n)
  hence i_eq: "i = int (Suc n)"
    using i_nonneg by simp
  hence im1: "i - 1 = int n"
    by simp
  have n_lt: "n < length addrs"
    using i_lt Suc by simp
  show ?thesis
    using Suc i_eq im1 n_lt
    by (simp add: rv_prev_addr_at_def access_rv_addr_vector i_eq)
qed

lemma run_readonly_result_prev_pmpaddr_at_index:
  assumes i_nonneg: "0 \<le> i"
      and i_lt: "nat i < length addrs"
  shows
    "run_readonly_result_n (Suc (Suc (Suc fuel)))
       (official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs))
       (if i > 0 then liftR (Rv64d.pmpReadAddrReg (i - 1))
        else return (Rv64d.zeros' 64)) =
     Some (Inr (rv_bits_of_word64 (rv_prev_addr_at addrs i)))"
proof (cases "nat i")
  case 0
  hence i_zero: "i = 0"
    using i_nonneg by simp
  show ?thesis
    by (simp add: i_zero rv_prev_addr_at_def pmpaddr_zero_def return_def)
next
  case (Suc n)
  hence i_eq: "i = int (Suc n)"
    using i_nonneg by simp
  hence im1: "i - 1 = int n"
    by simp
  have im1_nonneg: "0 \<le> i - 1"
    using i_eq by simp
  have im1_lt: "nat (i - 1) < length addrs"
    using i_lt i_eq by simp
  have nat_i: "nat (1 + int n) = Suc n"
    by simp
  have prev_eq: "rv_prev_addr_at addrs (1 + int n) = addrs ! n"
    by (simp add: rv_prev_addr_at_def nat_i)
  show ?thesis
    using run_readonly_result_liftR_pmpReadAddrReg_rv_addr_vector
            [OF im1_nonneg im1_lt, of fuel cfgs]
    by (simp add: i_eq im1 prev_eq)
qed

theorem rv_pmpMatchAddr_at_index:
  assumes i_nonneg: "0 \<le> i"
      and i_lt_cfg: "nat i < length cfgs"
      and i_lt_addr: "nat i < length addrs"
      and addr_u: "uint0 addr_bits = int addr"
      and width_u: "uint0 width_bits = int width"
  shows
    "run_readonly_n (Suc fuel) env
       (Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
          (access_list_dec (rv_cfg_vector cfgs) i)
          (access_list_dec (rv_addr_vector addrs) i)
          (if i > 0 then access_list_dec (rv_addr_vector addrs) (i - 1)
           else Rv64d.zeros' 64)) =
     Some (rv_pmp_match_of
       (official_pmp_match_addr
          (rv_prev_addr_at addrs i) (addrs ! nat i) (cfgs ! nat i)
          addr width))"
proof -
  have cfg_i:
    "access_list_dec (rv_cfg_vector cfgs) i =
     rv_cfg_bits_of_word (cfgs ! nat i)"
    using i_nonneg i_lt_cfg by (rule access_rv_cfg_vector)
  have addr_i:
    "access_list_dec (rv_addr_vector addrs) i =
     rv_bits_of_word64 (addrs ! nat i)"
    using i_nonneg i_lt_addr by (rule access_rv_addr_vector)
  have prev_i:
    "(if i > 0 then access_list_dec (rv_addr_vector addrs) (i - 1)
      else Rv64d.zeros' 64) =
     rv_bits_of_word64 (rv_prev_addr_at addrs i)"
    using i_nonneg i_lt_addr by (rule rv_prev_addr_bits)
  show ?thesis
    unfolding cfg_i addr_i prev_i
    by (rule rv_pmpMatchAddr_matches[OF addr_u width_u])
qed

theorem rv_pmpMatchAddr_return_at_index:
  assumes i_nonneg: "0 \<le> i"
      and i_lt_cfg: "nat i < length cfgs"
      and i_lt_addr: "nat i < length addrs"
      and addr_u: "uint0 addr_bits = int addr"
      and width_u: "uint0 width_bits = int width"
  shows
    "Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
       (access_list_dec (rv_cfg_vector cfgs) i)
       (access_list_dec (rv_addr_vector addrs) i)
       (if i > 0 then access_list_dec (rv_addr_vector addrs) (i - 1)
        else Rv64d.zeros' 64) =
     return (rv_pmp_match_of
       (official_pmp_match_addr
          (rv_prev_addr_at addrs i) (addrs ! nat i) (cfgs ! nat i)
          addr width))"
proof -
  have cfg_i:
    "access_list_dec (rv_cfg_vector cfgs) i =
     rv_cfg_bits_of_word (cfgs ! nat i)"
    using i_nonneg i_lt_cfg by (rule access_rv_cfg_vector)
  have addr_i:
    "access_list_dec (rv_addr_vector addrs) i =
     rv_bits_of_word64 (addrs ! nat i)"
    using i_nonneg i_lt_addr by (rule access_rv_addr_vector)
  have prev_i:
    "(if i > 0 then access_list_dec (rv_addr_vector addrs) (i - 1)
      else Rv64d.zeros' 64) =
     rv_bits_of_word64 (rv_prev_addr_at addrs i)"
    using i_nonneg i_lt_addr by (rule rv_prev_addr_bits)
  have ret:
    "Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
       (rv_cfg_bits_of_word (cfgs ! nat i))
       (rv_bits_of_word64 (addrs ! nat i))
       (rv_bits_of_word64 (rv_prev_addr_at addrs i)) =
     return (rv_pmp_match_of
       (official_pmp_match_addr
          (rv_prev_addr_at addrs i) (addrs ! nat i) (cfgs ! nat i)
          addr width))"
    by (rule rv_pmpMatchAddr_return[OF addr_u width_u])
  show ?thesis
    by (simp only: cfg_i addr_i prev_i ret)
qed

lemma liftR_pmpMatchAddr_return_at_index:
  assumes i_nonneg: "0 \<le> i"
      and i_lt_cfg: "nat i < length cfgs"
      and i_lt_addr: "nat i < length addrs"
      and addr_u: "uint0 addr_bits = int addr"
      and width_u: "uint0 width_bits = int width"
  shows
    "liftR
       (Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
          (access_list_dec (rv_cfg_vector cfgs) i)
          (access_list_dec (rv_addr_vector addrs) i)
          (if i > 0 then access_list_dec (rv_addr_vector addrs) (i - 1)
           else Rv64d.zeros' 64)) =
     return (rv_pmp_match_of
       (official_pmp_match_addr
          (rv_prev_addr_at addrs i) (addrs ! nat i) (cfgs ! nat i)
          addr width))"
  by (subst rv_pmpMatchAddr_return_at_index[OF assms]) simp

lemma rv_entry_machine_unlocked_matches:
  "(rv_priv_of priv = Rv64d_types.Machine \<and>
    Rv64d.not' (Rv64d.pmpLocked (rv_cfg_bits_of_word cfg))) =
   (priv = Official_Machine \<and> \<not> cfg_L cfg)"
  by (simp add: Rv64d.not'_def)

lemma rv_entry_match_result_matches:
  "(if official_cfg_allows cfg access \<or>
       (rv_priv_of priv = Rv64d_types.Machine \<and>
        Rv64d.not' (Rv64d.pmpLocked (rv_cfg_bits_of_word cfg)))
    then None
    else Some (rv_exception_of (official_access_fault access))) =
   map_option rv_exception_of
     (if official_cfg_allows cfg access \<or>
         (priv = Official_Machine \<and> \<not> cfg_L cfg)
      then None
      else Some (official_access_fault access))"
  by (cases priv; cases "cfg_L cfg"; cases "official_cfg_allows cfg access")
     (simp_all add: Rv64d.not'_def)

definition rv_loop_step_result ::
  "OfficialPmpStep \<Rightarrow>
   ((Rv64d_types.ExceptionType option, Rv64d_types.exception) sum, unit) sum" where
  "rv_loop_step_result step =
     (case step of
        Official_Continue \<Rightarrow> Inr ()
      | Official_Stop result \<Rightarrow>
          Inl (Inl (map_option rv_exception_of result)))"

definition rv_pmpCheck_match_result_body where
  "rv_pmpCheck_match_result_body access priv cfg match =
     (case match of
        Rv64d_types.PMP_NoMatch \<Rightarrow> return ()
      | Rv64d_types.PMP_PartialMatch \<Rightarrow>
          liftR (Rv64d.accessFaultFromAccessType access) \<bind>
            (\<lambda>w__4. (early_return (Some w__4) ::
              (unit, Rv64d_types.ExceptionType option) Rv64d_types.MR))
      | Rv64d_types.PMP_Match \<Rightarrow>
          or_boolM (liftR (Rv64d.pmpCheckRWX cfg access))
            (return
              (priv = Rv64d_types.Machine \<and>
               Rv64d.not' (Rv64d.pmpLocked cfg))) \<bind>
            (\<lambda>w__6.
              (if w__6 then return None
               else
                 liftR (Rv64d.accessFaultFromAccessType access) \<bind>
                   (\<lambda>w__7. return (Some w__7))) \<bind>
              (\<lambda>w__8. (early_return w__8 ::
                (unit, Rv64d_types.ExceptionType option) Rv64d_types.MR))))"

definition rv_pmpCheck_loop_body where
  "rv_pmpCheck_loop_body addr width access priv i unit_var =
     ((if i > 0 then liftR (Rv64d.pmpReadAddrReg (i - 1))
       else return (Rv64d.zeros' 64)) \<bind>
      (\<lambda>prev_pmpaddr.
        liftR (read_reg Rv64d_types.pmpcfg_n_ref) \<bind>
        (\<lambda>w__1.
          let cfg = access_list_dec w__1 i in
          liftR (Rv64d.pmpReadAddrReg i) \<bind>
          (\<lambda>w__2.
            liftR (Rv64d.pmpMatchAddr addr width cfg w__2 prev_pmpaddr) \<bind>
            (\<lambda>w__3.
              rv_pmpCheck_match_result_body access priv cfg w__3)))))"

lemma rv_pmpCheck_match_result_body_matches:
  fixes match :: PmpMatch
  shows
  "run_readonly_result_n (Suc fuel) env
     (rv_pmpCheck_match_result_body
       (rv_access_of access) (rv_priv_of priv)
       (rv_cfg_bits_of_word cfg) (rv_pmp_match_of match)) =
   Some
     (rv_loop_step_result
      (case (match :: PmpMatch) of
          SeSBI_PMP_NAPOT.PMP_NoMatch \<Rightarrow> Official_Continue
        | SeSBI_PMP_NAPOT.PMP_PartialMatch \<Rightarrow>
            Official_Stop (Some (official_access_fault access))
        | SeSBI_PMP_NAPOT.PMP_Match \<Rightarrow>
            Official_Stop
              (if official_cfg_allows cfg access \<or>
                  (priv = Official_Machine \<and> \<not> cfg_L cfg)
               then None
               else Some (official_access_fault access))))"
  by (cases match; cases "official_cfg_allows cfg access";
      cases priv; cases "cfg_L cfg")
     (simp_all add: rv_pmpCheck_match_result_body_def
                    rv_loop_step_result_def rv_pmp_match_of_def
                    rv_cfg_allows_bits_matches_official
                    or_boolM_def rv_entry_machine_unlocked_matches
                    Rv64d.not'_def early_return_def throw_def return_def)

lemma rv_pmpCheck_match_result_body_entry:
  "run_readonly_result_n (Suc fuel) env
     (rv_pmpCheck_match_result_body
       (rv_access_of access) (rv_priv_of priv)
       (rv_cfg_bits_of_word cfg)
       (rv_pmp_match_of
         (official_pmp_match_addr prev pa cfg addr width))) =
   Some
     (rv_loop_step_result
       (official_pmp_entry_check_raw prev pa cfg priv access addr width))"
  by (cases "official_pmp_match_addr prev pa cfg addr width")
     (simp_all add: rv_pmpCheck_match_result_body_matches
                    official_pmp_entry_check_raw_def)

definition rv_loop_body_fuel :: nat where
  "rv_loop_body_fuel =
   Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))"

theorem rv_pmpCheck_loop_body_matches_entry:
  assumes i_nonneg: "0 \<le> i"
      and i_lt_cfg: "nat i < length cfgs"
      and i_lt_addr: "nat i < length addrs"
      and addr_u: "uint0 addr_bits = int addr"
      and width_u: "uint0 width_bits = int width"
  shows
    "run_readonly_result_n rv_loop_body_fuel
       (official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs))
       (rv_pmpCheck_loop_body
          (Rv64d_types.Physaddr addr_bits) width_bits
          (rv_access_of access) (rv_priv_of priv) i ()) =
     Some
       (rv_loop_step_result
         (official_pmp_entry_check_raw
            (rv_prev_addr_at addrs i) (addrs ! nat i) (cfgs ! nat i)
            priv access addr width))"
proof -
  let ?env =
    "official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs)"
  let ?prev_bits = "rv_bits_of_word64 (rv_prev_addr_at addrs i)"
  let ?cfg_bits = "rv_cfg_bits_of_word (cfgs ! nat i)"
  let ?addr_bits_i = "rv_bits_of_word64 (addrs ! nat i)"
  let ?match =
    "official_pmp_match_addr
       (rv_prev_addr_at addrs i) (addrs ! nat i) (cfgs ! nat i)
       addr width"
  let ?result =
    "rv_loop_step_result
       (official_pmp_entry_check_raw
          (rv_prev_addr_at addrs i) (addrs ! nat i) (cfgs ! nat i)
          priv access addr width)"
  have prev_run:
    "run_readonly_result_n (Suc (Suc (Suc 0))) ?env
       (if i > 0 then liftR (Rv64d.pmpReadAddrReg (i - 1))
        else return (Rv64d.zeros' 64)) =
     Some (Inr ?prev_bits)"
    using run_readonly_result_prev_pmpaddr_at_index
            [OF i_nonneg i_lt_addr, of 0 cfgs]
    by simp
  have cfg_run:
    "run_readonly_result_n (Suc (Suc 0)) ?env
       (liftR (read_reg Rv64d_types.pmpcfg_n_ref)) =
     Some (Inr (rv_cfg_vector cfgs))"
    using run_readonly_result_liftR_read_pmpcfg_rv_cfg_vector
            [of 0 cfgs addrs]
    by simp
  have addr_run:
    "run_readonly_result_n (Suc (Suc (Suc 0))) ?env
       (liftR (Rv64d.pmpReadAddrReg i)) =
     Some (Inr ?addr_bits_i)"
    using run_readonly_result_liftR_pmpReadAddrReg_rv_addr_vector
            [OF i_nonneg i_lt_addr, of 0 cfgs]
    by simp
  have cfg_i:
    "access_list_dec (rv_cfg_vector cfgs) i = ?cfg_bits"
    using i_nonneg i_lt_cfg by (rule access_rv_cfg_vector)
  have addr_i:
    "access_list_dec (rv_addr_vector addrs) i = ?addr_bits_i"
    using i_nonneg i_lt_addr by (rule access_rv_addr_vector)
  have prev_i:
    "(if i > 0 then access_list_dec (rv_addr_vector addrs) (i - 1)
      else Rv64d.zeros' 64) = ?prev_bits"
    using i_nonneg i_lt_addr by (rule rv_prev_addr_bits)
  have match_lift:
    "liftR
       (Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
          ?cfg_bits ?addr_bits_i ?prev_bits) =
     return (rv_pmp_match_of ?match)"
    using liftR_pmpMatchAddr_return_at_index
            [OF i_nonneg i_lt_cfg i_lt_addr addr_u width_u]
    by (simp only: cfg_i addr_i prev_i)
  have match_run:
    "run_readonly_result_n (Suc 0) ?env
       (liftR
         (Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
            ?cfg_bits ?addr_bits_i ?prev_bits)) =
     Some (Inr (rv_pmp_match_of ?match))"
    by (subst match_lift) simp
  have branch_run:
    "run_readonly_result_n (Suc 0) ?env
       (rv_pmpCheck_match_result_body
          (rv_access_of access) (rv_priv_of priv) ?cfg_bits
          (rv_pmp_match_of ?match)) =
     Some ?result"
    by (rule rv_pmpCheck_match_result_body_entry)
  have match_then_branch:
    "run_readonly_result_n ((Suc 0) + (Suc 0)) ?env
       (liftR
         (Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
            ?cfg_bits ?addr_bits_i ?prev_bits) \<bind>
        (\<lambda>w__3.
          rv_pmpCheck_match_result_body
            (rv_access_of access) (rv_priv_of priv) ?cfg_bits w__3)) =
     Some ?result"
    apply (rule run_readonly_result_bind_Inr
          [where x = "rv_pmp_match_of ?match"
             and f = "\<lambda>w__3.
               rv_pmpCheck_match_result_body
                 (rv_access_of access) (rv_priv_of priv) ?cfg_bits w__3"])
     apply (rule match_run)
    apply (rule branch_run)
    done
  have addr_then_rest:
    "run_readonly_result_n
       ((Suc (Suc (Suc 0))) + ((Suc 0) + (Suc 0))) ?env
       (liftR (Rv64d.pmpReadAddrReg i) \<bind>
        (\<lambda>w__2.
          liftR
            (Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
               ?cfg_bits w__2 ?prev_bits) \<bind>
          (\<lambda>w__3.
            rv_pmpCheck_match_result_body
              (rv_access_of access) (rv_priv_of priv) ?cfg_bits w__3))) =
     Some ?result"
    apply (rule run_readonly_result_bind_Inr
          [where x = "?addr_bits_i"
             and f = "\<lambda>w__2.
               liftR
                 (Rv64d.pmpMatchAddr
                   (Rv64d_types.Physaddr addr_bits) width_bits
                   ?cfg_bits w__2 ?prev_bits) \<bind>
               (\<lambda>w__3.
                 rv_pmpCheck_match_result_body
                   (rv_access_of access) (rv_priv_of priv) ?cfg_bits w__3)"])
     apply (rule addr_run)
    apply (rule match_then_branch)
    done
  have cfg_then_rest:
    "run_readonly_result_n
       ((Suc (Suc 0)) +
        ((Suc (Suc (Suc 0))) + ((Suc 0) + (Suc 0)))) ?env
       (liftR (read_reg Rv64d_types.pmpcfg_n_ref) \<bind>
        (\<lambda>w__1.
          let cfg = access_list_dec w__1 i in
          liftR (Rv64d.pmpReadAddrReg i) \<bind>
          (\<lambda>w__2.
            liftR
              (Rv64d.pmpMatchAddr (Rv64d_types.Physaddr addr_bits) width_bits
                 cfg w__2 ?prev_bits) \<bind>
            (\<lambda>w__3.
              rv_pmpCheck_match_result_body
                (rv_access_of access) (rv_priv_of priv) cfg w__3)))) =
     Some ?result"
    apply (rule run_readonly_result_bind_Inr
          [where x = "rv_cfg_vector cfgs"
             and f = "\<lambda>w__1.
               let cfg = access_list_dec w__1 i in
               liftR (Rv64d.pmpReadAddrReg i) \<bind>
               (\<lambda>w__2.
                 liftR
                   (Rv64d.pmpMatchAddr
                     (Rv64d_types.Physaddr addr_bits) width_bits
                     cfg w__2 ?prev_bits) \<bind>
                 (\<lambda>w__3.
                   rv_pmpCheck_match_result_body
                     (rv_access_of access) (rv_priv_of priv) cfg w__3))"])
     apply (rule cfg_run)
    apply (simp only: cfg_i Let_def addr_then_rest)
    done
  have prev_then_rest:
    "run_readonly_result_n
       ((Suc (Suc (Suc 0))) +
        ((Suc (Suc 0)) +
         ((Suc (Suc (Suc 0))) + ((Suc 0) + (Suc 0))))) ?env
       ((if i > 0 then liftR (Rv64d.pmpReadAddrReg (i - 1))
         else return (Rv64d.zeros' 64)) \<bind>
        (\<lambda>prev_pmpaddr.
          liftR (read_reg Rv64d_types.pmpcfg_n_ref) \<bind>
          (\<lambda>w__1.
            let cfg = access_list_dec w__1 i in
            liftR (Rv64d.pmpReadAddrReg i) \<bind>
            (\<lambda>w__2.
              liftR
                (Rv64d.pmpMatchAddr
                  (Rv64d_types.Physaddr addr_bits) width_bits
                  cfg w__2 prev_pmpaddr) \<bind>
              (\<lambda>w__3.
                rv_pmpCheck_match_result_body
                  (rv_access_of access) (rv_priv_of priv) cfg w__3))))) =
     Some ?result"
    apply (rule run_readonly_result_bind_Inr
          [where x = "?prev_bits"
             and f = "\<lambda>prev_pmpaddr.
               liftR (read_reg Rv64d_types.pmpcfg_n_ref) \<bind>
               (\<lambda>w__1.
                 let cfg = access_list_dec w__1 i in
                 liftR (Rv64d.pmpReadAddrReg i) \<bind>
                 (\<lambda>w__2.
                   liftR
                     (Rv64d.pmpMatchAddr
                       (Rv64d_types.Physaddr addr_bits) width_bits
                       cfg w__2 prev_pmpaddr) \<bind>
                   (\<lambda>w__3.
                     rv_pmpCheck_match_result_body
                       (rv_access_of access) (rv_priv_of priv) cfg w__3)))"])
     apply (rule prev_run)
    apply (simp only: cfg_then_rest)
    done
  show ?thesis
    using prev_then_rest
    by (simp add: rv_loop_body_fuel_def rv_pmpCheck_loop_body_def)
qed

fun rv_foreach_fuel :: "int list \<Rightarrow> nat" where
  "rv_foreach_fuel [] = Suc 0"
| "rv_foreach_fuel (i # idx_tail) =
     rv_loop_body_fuel + rv_foreach_fuel idx_tail"

fun official_pmp_loop_indices ::
  "int list \<Rightarrow> 64 word list \<Rightarrow> 8 word list \<Rightarrow>
   OfficialAccess \<Rightarrow> OfficialPriv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   OfficialPmpStep" where
  "official_pmp_loop_indices [] addrs cfgs access priv addr width =
     Official_Continue"
| "official_pmp_loop_indices (i # idx_tail) addrs cfgs access priv addr width =
     (case official_pmp_entry_check_raw
        (rv_prev_addr_at addrs i) (addrs ! nat i) (cfgs ! nat i)
        priv access addr width of
        Official_Continue \<Rightarrow>
          official_pmp_loop_indices idx_tail addrs cfgs access priv addr width
      | Official_Stop result \<Rightarrow> Official_Stop result)"

theorem rv_pmpCheck_foreachM_indices_matches:
  assumes valid:
    "\<And>i. i \<in> set idxs \<Longrightarrow>
      0 \<le> i \<and> nat i < length cfgs \<and> nat i < length addrs"
      and addr_u: "uint0 addr_bits = int addr"
      and width_u: "uint0 width_bits = int width"
  shows
    "run_readonly_result_n (rv_foreach_fuel idxs)
       (official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs))
       (foreachM idxs ()
          (rv_pmpCheck_loop_body
            (Rv64d_types.Physaddr addr_bits) width_bits
            (rv_access_of access) (rv_priv_of priv))) =
     Some
       (rv_loop_step_result
         (official_pmp_loop_indices idxs addrs cfgs access priv addr width))"
  using valid
proof (induction idxs)
  case Nil
  show ?case
    by (simp add: rv_loop_step_result_def return_def)
next
  case (Cons i idx_tail)
  have i_valid:
    "0 \<le> i" "nat i < length cfgs" "nat i < length addrs"
    using Cons.prems by auto
  have rest_valid:
    "\<And>j. j \<in> set idx_tail \<Longrightarrow>
      0 \<le> j \<and> nat j < length cfgs \<and> nat j < length addrs"
    using Cons.prems by auto
  let ?entry =
    "official_pmp_entry_check_raw
       (rv_prev_addr_at addrs i) (addrs ! nat i) (cfgs ! nat i)
       priv access addr width"
  have body:
    "run_readonly_result_n rv_loop_body_fuel
       (official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs))
       (rv_pmpCheck_loop_body
          (Rv64d_types.Physaddr addr_bits) width_bits
          (rv_access_of access) (rv_priv_of priv) i ()) =
     Some (rv_loop_step_result ?entry)"
    by (rule rv_pmpCheck_loop_body_matches_entry
          [OF i_valid addr_u width_u])
  have rest:
    "run_readonly_result_n (rv_foreach_fuel idx_tail)
       (official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs))
       (foreachM idx_tail ()
          (rv_pmpCheck_loop_body
            (Rv64d_types.Physaddr addr_bits) width_bits
            (rv_access_of access) (rv_priv_of priv))) =
     Some
       (rv_loop_step_result
         (official_pmp_loop_indices idx_tail addrs cfgs access priv addr width))"
    by (rule Cons.IH[OF rest_valid])
  show ?case
  proof (cases ?entry)
    case Official_Continue
    let ?env =
      "official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs)"
    let ?body =
      "rv_pmpCheck_loop_body
        (Rv64d_types.Physaddr addr_bits) width_bits
        (rv_access_of access) (rv_priv_of priv)"
    have body_inr:
      "run_readonly_result_n rv_loop_body_fuel
         ?env (?body i ()) =
       Some (Inr ())"
      using body Official_Continue
      by (simp add: rv_loop_step_result_def)
    have bind_rest:
      "run_readonly_result_n (rv_loop_body_fuel + rv_foreach_fuel idx_tail)
         ?env
         (?body i () \<bind> (\<lambda>_. foreachM idx_tail () ?body)) =
       Some
         (rv_loop_step_result
           (official_pmp_loop_indices
             idx_tail addrs cfgs access priv addr width))"
      apply (rule run_readonly_result_bind_Inr
            [where x = "()" and f = "\<lambda>_. foreachM idx_tail () ?body"])
       apply (rule body_inr)
      apply (rule rest)
      done
    show ?thesis
      using bind_rest
      by (simp add: Official_Continue)
  next
    case (Official_Stop result)
    let ?env =
      "official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs)"
    let ?body =
      "rv_pmpCheck_loop_body
        (Rv64d_types.Physaddr addr_bits) width_bits
        (rv_access_of access) (rv_priv_of priv)"
    have body_inl:
      "run_readonly_result_n rv_loop_body_fuel
         ?env (?body i ()) =
       Some (Inl (Inl (map_option rv_exception_of result)))"
      using body Official_Stop
      by (simp add: rv_loop_step_result_def)
    have bind_stop:
      "run_readonly_result_n (rv_loop_body_fuel + rv_foreach_fuel idx_tail)
         ?env
         (?body i () \<bind> (\<lambda>_. foreachM idx_tail () ?body)) =
       Some (Inl (Inl (map_option rv_exception_of result)))"
      apply (rule run_readonly_result_bind_Inl
            [where f = "\<lambda>_. foreachM idx_tail () ?body"])
      apply (rule body_inl)
      done
    show ?thesis
      using bind_stop
      by (simp add: Official_Stop rv_loop_step_result_def)
  qed
qed

definition official_pmp_default_result ::
  "OfficialAccess \<Rightarrow> OfficialPriv \<Rightarrow> OfficialException option" where
  "official_pmp_default_result access priv =
     (if priv = Official_Machine then None
      else Some (official_access_fault access))"

definition official_pmp_loop_indices_result ::
  "int list \<Rightarrow> 64 word list \<Rightarrow> 8 word list \<Rightarrow>
   OfficialAccess \<Rightarrow> OfficialPriv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   OfficialException option" where
  "official_pmp_loop_indices_result idxs addrs cfgs access priv addr width =
     (case official_pmp_loop_indices idxs addrs cfgs access priv addr width of
        Official_Continue \<Rightarrow> official_pmp_default_result access priv
      | Official_Stop result \<Rightarrow> result)"

definition rv_pmpCheck_default where
  "rv_pmpCheck_default access priv =
     (if priv = Rv64d_types.Machine then return None
      else
        liftR (Rv64d.accessFaultFromAccessType access) \<bind>
        (\<lambda>w__9. return (Some w__9)))"

lemma run_readonly_result_pmpCheck_default:
  "run_readonly_result_n (Suc 0) env
     (rv_pmpCheck_default (rv_access_of access) (rv_priv_of priv)) =
   Some
     (Inr (map_option rv_exception_of
       (official_pmp_default_result access priv)))"
  by (cases priv)
     (simp_all add: rv_pmpCheck_default_def
                    official_pmp_default_result_def rv_priv_of_def
                    return_def)

lemma run_readonly_catch_early_return_Inr:
  assumes run: "run_readonly_result_n fuel env m = Some (Inr x)"
  shows "run_readonly_n fuel env (catch_early_return m) = Some x"
  using run
proof (induction fuel arbitrary: m)
  case 0
  thus ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases m)
    case (Done a)
    thus ?thesis
      using Suc.prems by (simp add: catch_early_return_def)
  next
    case (Read_reg reg k)
    show ?thesis
    proof (cases "env reg")
      case None
      thus ?thesis
        using Suc.prems Read_reg by simp
    next
      case (Some rv)
      have sub: "run_readonly_result_n fuel env (k rv) = Some (Inr x)"
        using Suc.prems Read_reg Some by simp
      show ?thesis
        using Suc.IH[OF sub] Read_reg Some
        by (simp add: catch_early_return_def try_catch_Read_reg_bridge)
    qed
  qed (use Suc.prems in \<open>simp_all add: catch_early_return_def\<close>)
qed

lemma run_readonly_catch_early_return_Inl_Inl:
  assumes run: "run_readonly_result_n fuel env m = Some (Inl (Inl x))"
  shows "run_readonly_n fuel env (catch_early_return m) = Some x"
  using run
proof (induction fuel arbitrary: m)
  case 0
  thus ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases m)
    case (Exception e)
    thus ?thesis
      using Suc.prems
      by (cases e) (simp_all add: catch_early_return_def return_def)
  next
    case (Read_reg reg k)
    show ?thesis
    proof (cases "env reg")
      case None
      thus ?thesis
        using Suc.prems Read_reg by simp
    next
      case (Some rv)
      have sub: "run_readonly_result_n fuel env (k rv) = Some (Inl (Inl x))"
        using Suc.prems Read_reg Some by simp
      show ?thesis
        using Suc.IH[OF sub] Read_reg Some
        by (simp add: catch_early_return_def try_catch_Read_reg_bridge)
    qed
  qed (use Suc.prems in \<open>simp_all add: catch_early_return_def\<close>)
qed

theorem rv_pmpCheck_body_indices_matches:
  assumes valid:
    "\<And>i. i \<in> set idxs \<Longrightarrow>
      0 \<le> i \<and> nat i < length cfgs \<and> nat i < length addrs"
      and addr_u: "uint0 addr_bits = int addr"
      and width_u: "uint0 width_bits = int width"
  shows
    "run_readonly_n (rv_foreach_fuel idxs + Suc 0)
       (official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs))
       (catch_early_return
         (foreachM idxs ()
            (rv_pmpCheck_loop_body
              (Rv64d_types.Physaddr addr_bits) width_bits
              (rv_access_of access) (rv_priv_of priv)) \<then>
          rv_pmpCheck_default (rv_access_of access) (rv_priv_of priv))) =
     Some
       (map_option rv_exception_of
         (official_pmp_loop_indices_result
           idxs addrs cfgs access priv addr width))"
proof -
  let ?env =
    "official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs)"
  let ?body =
    "rv_pmpCheck_loop_body
      (Rv64d_types.Physaddr addr_bits) width_bits
      (rv_access_of access) (rv_priv_of priv)"
  let ?loop =
    "official_pmp_loop_indices idxs addrs cfgs access priv addr width"
  have loop_run:
    "run_readonly_result_n (rv_foreach_fuel idxs) ?env
       (foreachM idxs () ?body) =
     Some (rv_loop_step_result ?loop)"
    by (rule rv_pmpCheck_foreachM_indices_matches
          [OF valid addr_u width_u])
  have default_run:
    "run_readonly_result_n (Suc 0) ?env
       (rv_pmpCheck_default (rv_access_of access) (rv_priv_of priv)) =
     Some
       (Inr (map_option rv_exception_of
         (official_pmp_default_result access priv)))"
    by (rule run_readonly_result_pmpCheck_default)
  show ?thesis
  proof (cases ?loop)
    case Official_Continue
    have loop_inr:
      "run_readonly_result_n (rv_foreach_fuel idxs) ?env
         (foreachM idxs () ?body) = Some (Inr ())"
      using loop_run Official_Continue
      by (simp add: rv_loop_step_result_def)
    have body_run:
      "run_readonly_result_n (rv_foreach_fuel idxs + Suc 0) ?env
         (foreachM idxs () ?body \<then>
          rv_pmpCheck_default (rv_access_of access) (rv_priv_of priv)) =
       Some
         (Inr (map_option rv_exception_of
           (official_pmp_default_result access priv)))"
      apply (rule run_readonly_result_bind_Inr
            [where x = "()"
               and f = "\<lambda>_.
                 rv_pmpCheck_default
                   (rv_access_of access) (rv_priv_of priv)"])
       apply (rule loop_inr)
      apply (rule default_run)
      done
    show ?thesis
      using run_readonly_catch_early_return_Inr[OF body_run]
            Official_Continue
      by (simp add: official_pmp_loop_indices_result_def)
  next
    case (Official_Stop result)
    have loop_inl:
      "run_readonly_result_n (rv_foreach_fuel idxs) ?env
         (foreachM idxs () ?body) =
       Some (Inl (Inl (map_option rv_exception_of result)))"
      using loop_run Official_Stop
      by (simp add: rv_loop_step_result_def)
    have body_run:
      "run_readonly_result_n (rv_foreach_fuel idxs + Suc 0) ?env
         (foreachM idxs () ?body \<then>
          rv_pmpCheck_default (rv_access_of access) (rv_priv_of priv)) =
       Some (Inl (Inl (map_option rv_exception_of result)))"
      apply (rule run_readonly_result_bind_Inl
            [where f = "\<lambda>_.
              rv_pmpCheck_default
                (rv_access_of access) (rv_priv_of priv)"])
      apply (rule loop_inl)
      done
    show ?thesis
      using run_readonly_catch_early_return_Inl_Inl[OF body_run]
            Official_Stop
      by (simp add: official_pmp_loop_indices_result_def)
  qed
qed

termination index_list
  by (relation "measure (\<lambda>(i, j, step). nat ((j - i + step) * sgn step))")
     auto

definition rv_pmpCheck_fuel :: nat where
  "rv_pmpCheck_fuel = rv_foreach_fuel [0::int..15] + Suc 0"

lemma rv_pmpCheck_indices_0_15 [simp]:
  "index_list 0 (Rv64d.sys_pmp_count - 1) 1 = [0::int..15]"
  by (simp add: Rv64d.sys_pmp_count_def index_list.simps upto.simps)

lemma rv_pmpCheck_index_valid_16:
  assumes cfg_len: "16 \<le> length cfgs"
      and addr_len: "16 \<le> length addrs"
      and i_set: "i \<in> set [0::int..15]"
  shows "0 \<le> i \<and> nat i < length cfgs \<and> nat i < length addrs"
  using cfg_len addr_len i_set
  by auto

lemma take_eq_map_nth_upt:
  assumes "n \<le> length xs"
  shows "take n xs = map (\<lambda>i. xs ! i) [0..<n]"
proof (rule nth_equalityI)
  show "length (take n xs) = length (map (\<lambda>i. xs ! i) [0..<n])"
    using assms by simp
next
  fix i
  assume i_lt: "i < length (take n xs)"
  show "take n xs ! i = map (\<lambda>i. xs ! i) [0..<n] ! i"
    using assms i_lt by simp
qed

lemma official_pmp_loop_indices_result_Cons:
  "official_pmp_loop_indices_result
     (i # idx_tail) addrs cfgs access priv addr width =
   (case official_pmp_entry_check_raw
      (rv_prev_addr_at addrs i) (addrs ! nat i) (cfgs ! nat i)
      priv access addr width of
      Official_Continue \<Rightarrow>
        official_pmp_loop_indices_result
          idx_tail addrs cfgs access priv addr width
    | Official_Stop result \<Rightarrow> result)"
  by (simp add: official_pmp_loop_indices_result_def
           split: OfficialPmpStep.splits)

lemma upt_add_Suc_head:
  "[k..<k+Suc n] = k # [Suc k..<Suc k+n]"
proof -
  have "[k..<k+Suc n] = k # [Suc k..<k+Suc n]"
    by (rule upt_conv_Cons) simp
  also have "\<dots> = k # [Suc k..<Suc k+n]"
    by simp
  finally show ?thesis .
qed

lemma official_pmp_loop_indices_result_upt_from_prev:
  "official_pmp_loop_indices_result
     (map int [k..<k+n]) addrs cfgs access priv addr width =
   official_pmp_check_raw_table_from_prev
     (if k = 0 then pmpaddr_zero else addrs ! (k - 1))
     (map (\<lambda>j. addrs ! j) [k..<k+n])
     (map (\<lambda>j. cfgs ! j) [k..<k+n])
     access priv addr width"
proof (induction n arbitrary: k)
  case 0
  show ?case
    by (simp add: official_pmp_loop_indices_result_def
                  official_pmp_default_result_def)
next
  case (Suc n)
  have idxs:
    "map int [k..<k+Suc n] =
     int k # map int [Suc k..<Suc k+n]"
    by (simp only: upt_add_Suc_head list.simps)
  have addrs_map:
    "map (\<lambda>j. addrs ! j) [k..<k+Suc n] =
     addrs ! k # map (\<lambda>j. addrs ! j) [Suc k..<Suc k+n]"
    by (simp only: upt_add_Suc_head list.simps)
  have cfgs_map:
    "map (\<lambda>j. cfgs ! j) [k..<k+Suc n] =
     cfgs ! k # map (\<lambda>j. cfgs ! j) [Suc k..<Suc k+n]"
    by (simp only: upt_add_Suc_head list.simps)
  have ih:
    "official_pmp_loop_indices_result
       (map int [Suc k..<Suc k+n]) addrs cfgs access priv addr width =
     official_pmp_check_raw_table_from_prev
       (addrs ! k)
       (map (\<lambda>j. addrs ! j) [Suc k..<Suc k+n])
       (map (\<lambda>j. cfgs ! j) [Suc k..<Suc k+n])
       access priv addr width"
    using Suc.IH[of "Suc k"] by simp
  let ?prev = "if k = 0 then pmpaddr_zero else addrs ! (k - 1)"
  let ?entry =
    "official_pmp_entry_check_raw
       ?prev (addrs ! k) (cfgs ! k) priv access addr width"
  have prev_eq:
    "rv_prev_addr_at addrs (int k) = ?prev"
    by (simp add: rv_prev_addr_at_def)
  have lhs:
    "official_pmp_loop_indices_result
       (map int [k..<k+Suc n]) addrs cfgs access priv addr width =
     (case ?entry of
        Official_Continue \<Rightarrow>
          official_pmp_loop_indices_result
            (map int [Suc k..<Suc k+n]) addrs cfgs access priv addr width
      | Official_Stop result \<Rightarrow> result)"
    by (simp only: idxs official_pmp_loop_indices_result_Cons
                   prev_eq nat_int)
  have rhs:
    "official_pmp_check_raw_table_from_prev
       ?prev
       (map (\<lambda>j. addrs ! j) [k..<k+Suc n])
       (map (\<lambda>j. cfgs ! j) [k..<k+Suc n])
       access priv addr width =
     (case ?entry of
        Official_Continue \<Rightarrow>
          official_pmp_check_raw_table_from_prev
            (addrs ! k)
            (map (\<lambda>j. addrs ! j) [Suc k..<Suc k+n])
            (map (\<lambda>j. cfgs ! j) [Suc k..<Suc k+n])
            access priv addr width
      | Official_Stop result \<Rightarrow> result)"
    by (simp only: addrs_map cfgs_map
                   official_pmp_check_raw_table_from_prev.simps)
  show ?case
    using lhs rhs ih
    by (cases ?entry) simp_all
qed

lemma int_range_0_15_map_upt [simp]:
  "[0::int..15] = map int [0..<16]"
  by (simp add: upto.simps upt_rec)

lemma official_pmp_loop_indices_result_0_15_raw_table:
  assumes cfg_len: "16 \<le> length cfgs"
      and addr_len: "16 \<le> length addrs"
  shows
    "official_pmp_loop_indices_result
       [0::int..15] addrs cfgs access priv addr width =
     official_pmp_check_raw_table
       (take 16 addrs) (take 16 cfgs) access priv addr width"
proof -
  have addrs_take:
    "take 16 addrs = map (\<lambda>j. addrs ! j) [0..<16]"
    by (rule take_eq_map_nth_upt[OF addr_len])
  have cfgs_take:
    "take 16 cfgs = map (\<lambda>j. cfgs ! j) [0..<16]"
    by (rule take_eq_map_nth_upt[OF cfg_len])
  show ?thesis
    using official_pmp_loop_indices_result_upt_from_prev
          [of 0 16 addrs cfgs access priv addr width]
    by (simp add: official_pmp_check_raw_table_def
                  addrs_take cfgs_take)
qed

theorem rv_pmpCheck_generated_matches_indices:
  assumes cfg_len: "16 \<le> length cfgs"
      and addr_len: "16 \<le> length addrs"
      and addr_u: "uint0 addr_bits = int addr"
      and width_lt: "width < (2::nat)^64"
  shows
    "run_readonly_n rv_pmpCheck_fuel
       (official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs))
       (Rv64d.pmpCheck
          (Rv64d_types.Physaddr addr_bits) (int width)
          (rv_access_of access) (rv_priv_of priv)) =
     Some
       (map_option rv_exception_of
         (official_pmp_loop_indices_result
           [0::int..15] addrs cfgs access priv addr width))"
proof -
  have valid:
    "\<And>i. i \<in> set [0::int..15] \<Longrightarrow>
      0 \<le> i \<and> nat i < length cfgs \<and> nat i < length addrs"
    using cfg_len addr_len
    by (rule rv_pmpCheck_index_valid_16)
  have width_u:
    "uint0 (Rv64d.to_bits 64 (int width)) = int width"
    by (rule uint0_to_bits64_nat[OF width_lt])
  have body:
    "run_readonly_n (rv_foreach_fuel [0::int..15] + Suc 0)
       (official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs))
       (catch_early_return
         (foreachM [0::int..15] ()
            (rv_pmpCheck_loop_body
              (Rv64d_types.Physaddr addr_bits)
              (Rv64d.to_bits 64 (int width))
              (rv_access_of access) (rv_priv_of priv)) \<then>
          rv_pmpCheck_default (rv_access_of access) (rv_priv_of priv))) =
     Some
       (map_option rv_exception_of
         (official_pmp_loop_indices_result
           [0::int..15] addrs cfgs access priv addr width))"
    by (rule rv_pmpCheck_body_indices_matches
          [OF valid addr_u width_u])
  have pmp_unfold:
    "Rv64d.pmpCheck
       (Rv64d_types.Physaddr addr_bits) (int width)
       (rv_access_of access) (rv_priv_of priv) =
     catch_early_return
       (foreachM [0::int..15] ()
          (\<lambda>i unit_var.
            rv_pmpCheck_loop_body
              (Rv64d_types.Physaddr addr_bits)
              (Rv64d.to_bits 64 (int width))
              (rv_access_of access) (rv_priv_of priv) i unit_var) \<then>
        rv_pmpCheck_default (rv_access_of access) (rv_priv_of priv))"
    by (simp add: Rv64d.pmpCheck_def Rv64d.sys_pmp_count_def
                  rv_pmpCheck_loop_body_def
                  rv_pmpCheck_match_result_body_def
                  rv_pmpCheck_default_def upto.simps
             del: foreachM.simps
                  rv_priv_machine_iff
                  rv_accessFaultFromAccessType_return
                  liftR_accessFaultFromAccessType_return
                  rv_pmpCheckRWX_return_bits
                  rv_pmpCheckRWX_return
                  liftR_pmpCheckRWX_return)
  show ?thesis
    using body
    by (simp add: rv_pmpCheck_fuel_def pmp_unfold del: foreachM.simps)
qed

theorem rv_pmpCheck_generated_matches_raw_table:
  assumes cfg_len: "16 \<le> length cfgs"
      and addr_len: "16 \<le> length addrs"
      and addr_u: "uint0 addr_bits = int addr"
      and width_lt: "width < (2::nat)^64"
  shows
    "run_readonly_n rv_pmpCheck_fuel
       (official_pmp_register_env (rv_cfg_vector cfgs) (rv_addr_vector addrs))
       (Rv64d.pmpCheck
          (Rv64d_types.Physaddr addr_bits) (int width)
          (rv_access_of access) (rv_priv_of priv)) =
     Some
       (map_option rv_exception_of
         (official_pmp_check_raw_table
           (take 16 addrs) (take 16 cfgs) access priv addr width))"
  using rv_pmpCheck_generated_matches_indices
          [OF cfg_len addr_len addr_u width_lt]
        official_pmp_loop_indices_result_0_15_raw_table
          [OF cfg_len addr_len, of access priv addr width]
  by simp

text \<open>
  The theorem above closes the read-only official-register-state bridge for
  generated @{const Rv64d.pmpCheck}: when the generated PMP register environment
  exposes the supplied cfg/address vectors, the interpreted generated function
  agrees with the Experiment 16 explicit raw-table model over the first
  @{term 16} PMP entries.
\<close>

end
