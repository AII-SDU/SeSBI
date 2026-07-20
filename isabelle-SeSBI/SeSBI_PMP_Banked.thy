theory SeSBI_PMP_Banked
  imports SeSBI_PMP_CfgPack
begin

unbundle bit_operations_syntax

section \<open>Total signed-index RV64 PMP bank update\<close>

text \<open>
  This theory combines the previously proved 64-bit configuration-byte
  target/frame operation with the two-bank selector and the sixteen-entry
  address table used by SeSBI.  The transition is total over signed indices
  and request parameters: every rejected request returns an error and is the
  identity on the complete modeled PMP state.
\<close>

definition pmp_entry_count :: int where
  "pmp_entry_count = 16"

definition valid_signed_index :: "int \<Rightarrow> bool" where
  "valid_signed_index idx \<longleftrightarrow> 0 \<le> idx \<and> idx < pmp_entry_count"

definition cfg_bank :: "int \<Rightarrow> nat" where
  "cfg_bank idx = (if idx < 8 then 0 else 2)"

definition cfg_offset :: "int \<Rightarrow> nat" where
  "cfg_offset idx = nat idx mod 8"

definition is_power_of_two_nat :: "nat \<Rightarrow> bool" where
  "is_power_of_two_nat n \<longleftrightarrow> n > 0 \<and> (\<exists>k. n = 2 ^ k)"

definition allow_all_region :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "allow_all_region start sz \<longleftrightarrow>
     start = 0 \<and> sz = 2 ^ (64 :: nat) - 1"

definition ordinary_region :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "ordinary_region start sz \<longleftrightarrow>
     4 \<le> sz \<and>
     is_power_of_two_nat sz \<and>
     start mod sz = 0 \<and>
     start + sz \<le> 2 ^ (64 :: nat)"

definition valid_region_request :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_region_request start sz \<longleftrightarrow>
     allow_all_region start sz \<or> ordinary_region start sz"

definition supported_prot :: "nat \<Rightarrow> bool" where
  "supported_prot prot \<longleftrightarrow>
     prot < 8 \<and> (bit prot 1 \<longrightarrow> bit prot 0)"

definition valid_pmp_request :: "int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_pmp_request idx start sz prot \<longleftrightarrow>
     valid_signed_index idx \<and>
     valid_region_request start sz \<and>
     supported_prot prot"

record banked_pmp_state =
  bank_cfg0 :: "64 word"
  bank_cfg2 :: "64 word"
  bank_addrs :: "64 word list"

definition well_formed_banked_state :: "banked_pmp_state \<Rightarrow> bool" where
  "well_formed_banked_state s \<longleftrightarrow> length (bank_addrs s) = 16"

datatype pmp_update_result = Pmp_Update_Success | Pmp_Update_Error

definition banked_pmp_update ::
  "int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   8 word \<Rightarrow> 64 word \<Rightarrow> banked_pmp_state \<Rightarrow>
   pmp_update_result \<times> banked_pmp_state" where
  "banked_pmp_update idx start sz prot new_cfg new_addr s =
     (if \<not> valid_pmp_request idx start sz prot \<or>
          \<not> well_formed_banked_state s
      then (Pmp_Update_Error, s)
      else
        let n = nat idx;
            off = cfg_offset idx;
            addrs' = (bank_addrs s)[n := new_addr]
        in if cfg_bank idx = 0
           then
             (Pmp_Update_Success,
              s\<lparr>bank_cfg0 := pmpcfg_write (bank_cfg0 s) off new_cfg,
                bank_addrs := addrs'\<rparr>)
           else
             (Pmp_Update_Success,
              s\<lparr>bank_cfg2 := pmpcfg_write (bank_cfg2 s) off new_cfg,
                bank_addrs := addrs'\<rparr>))"

lemma valid_index_bounds:
  assumes "valid_signed_index idx"
  shows "0 \<le> idx" "idx < 16" "nat idx < 16"
proof -
  show nonneg: "0 \<le> idx"
    using assms by (simp add: valid_signed_index_def)
  show upper: "idx < 16"
    using assms by (simp add: valid_signed_index_def pmp_entry_count_def)
  show "nat idx < 16"
    using nat_less_iff[OF nonneg, of 16] upper by simp
qed

lemma low_index_selects_cfg0:
  assumes "0 \<le> idx" "idx < 8"
  shows "cfg_bank idx = 0" "cfg_offset idx = nat idx"
  using assms by (simp_all add: cfg_bank_def cfg_offset_def)

lemma high_index_selects_cfg2:
  assumes "8 \<le> idx" "idx < 16"
  shows "cfg_bank idx = 2" "cfg_offset idx = nat idx - 8"
proof -
  show "cfg_bank idx = 2"
    using assms by (simp add: cfg_bank_def)
  have n: "nat idx < 16" "8 \<le> nat idx"
    using assms by simp_all
  have split: "nat idx = 8 + (nat idx - 8)"
    using n by simp
  have delta: "nat idx - 8 < 8"
    using n by linarith
  show "cfg_offset idx = nat idx - 8"
    unfolding cfg_offset_def
  proof -
    have "nat idx mod 8 = (8 + (nat idx - 8)) mod 8"
      by (rule arg_cong[OF split])
    also have "\<dots> = (nat idx - 8) mod 8"
      by simp
    also have "\<dots> = nat idx - 8"
      using delta by simp
    finally show "nat idx mod 8 = nat idx - 8" .
  qed
qed

theorem invalid_request_returns_error_and_preserves_state:
  assumes "\<not> valid_pmp_request idx start sz prot"
  shows "banked_pmp_update idx start sz prot new_cfg new_addr s =
         (Pmp_Update_Error, s)"
  using assms by (simp add: banked_pmp_update_def)

corollary negative_index_returns_error_and_preserves_state:
  assumes "idx < 0"
  shows "banked_pmp_update idx start sz prot new_cfg new_addr s =
         (Pmp_Update_Error, s)"
  using assms
  by (intro invalid_request_returns_error_and_preserves_state)
     (simp add: valid_pmp_request_def valid_signed_index_def)

corollary upper_index_returns_error_and_preserves_state:
  assumes "16 \<le> idx"
  shows "banked_pmp_update idx start sz prot new_cfg new_addr s =
         (Pmp_Update_Error, s)"
  using assms
  by (intro invalid_request_returns_error_and_preserves_state)
     (simp add: valid_pmp_request_def valid_signed_index_def pmp_entry_count_def)

theorem valid_request_returns_success:
  assumes req: "valid_pmp_request idx start sz prot"
      and wf: "well_formed_banked_state s"
  shows "fst (banked_pmp_update idx start sz prot new_cfg new_addr s) =
         Pmp_Update_Success"
proof -
  have idx: "0 \<le> idx" "idx < 16"
    using req by (auto simp: valid_pmp_request_def valid_signed_index_def
                            pmp_entry_count_def)
  show ?thesis
    using req wf idx
    by (simp add: banked_pmp_update_def cfg_bank_def Let_def)
qed

theorem address_write_target:
  fixes new_cfg :: "8 word" and new_addr :: "64 word"
  assumes req: "valid_pmp_request idx start sz prot"
      and wf: "well_formed_banked_state s"
  defines "s' \<equiv> snd (banked_pmp_update idx start sz prot new_cfg new_addr s)"
  shows "bank_addrs s' ! nat idx = new_addr"
proof -
  have valid_idx: "valid_signed_index idx"
    using req by (simp add: valid_pmp_request_def)
  have idx16: "nat idx < 16"
    using valid_index_bounds(3)[OF valid_idx] .
  have idx: "nat idx < length (bank_addrs s)"
    using idx16 wf by (simp add: well_formed_banked_state_def)
  show ?thesis
    using req wf idx
    by (simp add: s'_def banked_pmp_update_def Let_def)
qed

theorem address_write_frame:
  fixes new_cfg :: "8 word" and new_addr :: "64 word"
  assumes req: "valid_pmp_request idx start sz prot"
      and wf: "well_formed_banked_state s"
      and j: "j < 16" "j \<noteq> nat idx"
  defines "s' \<equiv> snd (banked_pmp_update idx start sz prot new_cfg new_addr s)"
  shows "bank_addrs s' ! j = bank_addrs s ! j"
proof -
  have jlen: "j < length (bank_addrs s)"
    using wf j by (simp add: well_formed_banked_state_def)
  show ?thesis
    using req wf j jlen
    by (simp add: s'_def banked_pmp_update_def Let_def)
qed

theorem low_bank_target_and_cross_bank_frame:
  fixes new_cfg :: "8 word" and new_addr :: "64 word"
  assumes req: "valid_pmp_request idx start sz prot"
      and low: "idx < 8"
      and wf: "well_formed_banked_state s"
  defines "s' \<equiv> snd (banked_pmp_update idx start sz prot new_cfg new_addr s)"
  shows "cfg_byte (bank_cfg0 s') (nat idx) = new_cfg"
    and "bank_cfg2 s' = bank_cfg2 s"
proof -
  have bounds: "0 \<le> idx" "nat idx < 8"
    using req low
    by (auto simp: valid_pmp_request_def valid_signed_index_def
                   pmp_entry_count_def)
  have bank: "cfg_bank idx = 0" and off: "cfg_offset idx = nat idx"
    using low_index_selects_cfg0[OF bounds(1) low] by simp_all
  show "cfg_byte (bank_cfg0 s') (nat idx) = new_cfg"
    using req wf bounds bank off cfg_byte_write_target[of "nat idx"]
    by (simp add: s'_def banked_pmp_update_def Let_def)
  show "bank_cfg2 s' = bank_cfg2 s"
    using req wf bank by (simp add: s'_def banked_pmp_update_def Let_def)
qed

theorem low_bank_byte_frame:
  fixes new_cfg :: "8 word" and new_addr :: "64 word"
  assumes req: "valid_pmp_request idx start sz prot"
      and low: "idx < 8"
      and wf: "well_formed_banked_state s"
      and j: "j < 8" "j \<noteq> nat idx"
  defines "s' \<equiv> snd (banked_pmp_update idx start sz prot new_cfg new_addr s)"
  shows "cfg_byte (bank_cfg0 s') j = cfg_byte (bank_cfg0 s) j"
proof -
  have bounds: "0 \<le> idx" "nat idx < 8"
    using req low
    by (auto simp: valid_pmp_request_def valid_signed_index_def
                   pmp_entry_count_def)
  have bank: "cfg_bank idx = 0" and off: "cfg_offset idx = nat idx"
    using low_index_selects_cfg0[OF bounds(1) low] by simp_all
  show ?thesis
    using req wf j bounds bank off
          cfg_byte_write_frame[of "nat idx" j]
    by (simp add: s'_def banked_pmp_update_def Let_def)
qed

theorem high_bank_target_and_cross_bank_frame:
  fixes new_cfg :: "8 word" and new_addr :: "64 word"
  assumes req: "valid_pmp_request idx start sz prot"
      and high: "8 \<le> idx"
      and wf: "well_formed_banked_state s"
  defines "s' \<equiv> snd (banked_pmp_update idx start sz prot new_cfg new_addr s)"
  shows "cfg_byte (bank_cfg2 s') (nat idx - 8) = new_cfg"
    and "bank_cfg0 s' = bank_cfg0 s"
proof -
  have upper: "idx < 16"
    using req
    by (simp add: valid_pmp_request_def valid_signed_index_def
                  pmp_entry_count_def)
  have bounds: "nat idx - 8 < 8"
    using high upper by simp
  have bank: "cfg_bank idx = 2" and off: "cfg_offset idx = nat idx - 8"
    using high_index_selects_cfg2[OF high upper] by simp_all
  show "cfg_byte (bank_cfg2 s') (nat idx - 8) = new_cfg"
    using req wf bounds bank off
          cfg_byte_write_target[of "nat idx - 8"]
    by (simp add: s'_def banked_pmp_update_def Let_def)
  show "bank_cfg0 s' = bank_cfg0 s"
    using req wf bank by (simp add: s'_def banked_pmp_update_def Let_def)
qed

theorem high_bank_byte_frame:
  fixes new_cfg :: "8 word" and new_addr :: "64 word"
  assumes req: "valid_pmp_request idx start sz prot"
      and high: "8 \<le> idx"
      and wf: "well_formed_banked_state s"
      and j: "j < 8" "j \<noteq> nat idx - 8"
  defines "s' \<equiv> snd (banked_pmp_update idx start sz prot new_cfg new_addr s)"
  shows "cfg_byte (bank_cfg2 s') j = cfg_byte (bank_cfg2 s) j"
proof -
  have upper: "idx < 16"
    using req
    by (simp add: valid_pmp_request_def valid_signed_index_def
                  pmp_entry_count_def)
  have bounds: "nat idx - 8 < 8"
    using high upper by simp
  have bank: "cfg_bank idx = 2" and off: "cfg_offset idx = nat idx - 8"
    using high_index_selects_cfg2[OF high upper] by simp_all
  show ?thesis
    using req wf j bounds bank off
          cfg_byte_write_frame[of "nat idx - 8" j]
    by (simp add: s'_def banked_pmp_update_def Let_def)
qed

lemma write_without_read_is_rejected:
  assumes "bit prot 1" "\<not> bit prot 0"
  shows "\<not> valid_pmp_request idx start sz prot"
  using assms by (auto simp: valid_pmp_request_def supported_prot_def)

lemma boot_requests_are_valid:
  "valid_pmp_request 0 0 (2 ^ (64 :: nat) - 1) 7"
  "valid_pmp_request 1 0x80000000 0x40000 7"
proof -
  show "valid_pmp_request 0 0 (2 ^ (64 :: nat) - 1) 7"
    by (simp add: valid_pmp_request_def valid_signed_index_def
                  pmp_entry_count_def valid_region_request_def
                  allow_all_region_def supported_prot_def)
  show "valid_pmp_request 1 0x80000000 0x40000 7"
  proof -
    have pow: "is_power_of_two_nat (0x40000 :: nat)"
      unfolding is_power_of_two_nat_def
    proof
      show "(0x40000 :: nat) > 0" by simp
      show "\<exists>k. (0x40000 :: nat) = 2 ^ k"
        by (rule exI[where x = 18]) simp
    qed
    show ?thesis
      using pow
      by (simp add: valid_pmp_request_def valid_signed_index_def
                    pmp_entry_count_def valid_region_request_def
                    ordinary_region_def supported_prot_def)
  qed
qed

end
