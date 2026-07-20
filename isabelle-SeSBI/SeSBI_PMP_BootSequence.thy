theory SeSBI_PMP_BootSequence
  imports SeSBI_PMP_BootConfig SeSBI_PMP_Mstatus
begin

unbundle bit_operations_syntax

section \<open>S5-lite boot sequence facts\<close>

text \<open>
  This theory composes the already checked PMP-configuration and mstatus-field
  facts into a small boot-sequence postcondition model.  It deliberately proves
  two separate facts:

    * the current SeSBI boot layout prepares an S-mode entry, but its first PMP
      entry is allow-all, so low-privilege accesses to firmware memory are
      allowed rather than faulted;
    * a corrected boot layout with a deny-first firmware-region entry combines
      the same S-mode-entry setup with the previously proved PMP isolation
      theorem.

  Scope: this is not a full Sail instruction-semantics proof of mret.  It is the
  S5-lite CSR/postcondition layer above the already checked PMP and mstatus
  bit-field lemmas.
\<close>

subsection \<open>Boot CSR state model\<close>

record BootState =
  bs_entries :: "PmpEntry list"
  bs_mstatus :: "64 word"
  bs_mepc :: "64 word"
  bs_stvec :: "64 word"
  bs_sie :: "64 word"
  bs_satp :: "64 word"

definition FW_JUMP_ADDR :: "64 word" where
  "FW_JUMP_ADDR = 0x80200000"

definition PAYLOAD_START :: xlenbits where
  "PAYLOAD_START = 0x80000000"

definition sbi_main_mstatus_after :: "64 word \<Rightarrow> 64 word" where
  "sbi_main_mstatus_after old =
     insert_field (insert_field old MSTATUS_MPP PRV_S) MSTATUS_MPIE 1"

definition smode_entry_setup :: "BootState \<Rightarrow> bool" where
  "smode_entry_setup s \<longleftrightarrow>
     get_field (bs_mstatus s) 11 2 = PRV_S \<and>
     get_field (bs_mstatus s) 7 1 = 1 \<and>
     bs_mepc s = FW_JUMP_ADDR \<and>
     bs_stvec s = FW_JUMP_ADDR \<and>
     bs_sie s = 0 \<and>
     bs_satp s = 0"

subsection \<open>Composing the two mstatus INSERT_FIELD writes\<close>

lemma get_field_mpp_after_mpie_set:
  "get_field (insert_field val MSTATUS_MPIE 1) 11 2 = get_field val 11 2"
  unfolding insert_MPIE_1
  apply (unfold get_field_def MSTATUS_MPIE_def)
  apply (rule bit_word_eqI)
  apply (simp only: bit_simps possible_bit_word len64 comp_def)
  apply (case_tac "bit (val::64 word) (11 + n)"; presburger)
  done

theorem sbi_main_mstatus_mpp_set:
  "get_field (sbi_main_mstatus_after old) 11 2 = PRV_S"
  by (simp add: sbi_main_mstatus_after_def
                get_field_mpp_after_mpie_set mstatus_mpp_set)

theorem sbi_main_mstatus_mpie_set:
  "get_field (sbi_main_mstatus_after old) 7 1 = 1"
  unfolding sbi_main_mstatus_after_def
  using mstatus_mpie_set[of "insert_field old MSTATUS_MPP PRV_S"] by simp

subsection \<open>Current boot: allow-all PMP entry 0\<close>

text \<open>
  The current firmware's first PMP call is:

    sbi_set_pmp(0, 0, -1UL, PMP_RWX)

  In the real C path, size = -1UL makes log2roundup choose order = RISCV_XLEN,
  and the firmware writes pmpaddr = -1UL.  At this S5-lite boot-sequence layer
  we represent the resulting entry by its architectural effect: an L=0 RWX
  allow entry over the whole RV64 physical address space.  The non-XLEN NAPOT
  encoder path remains handled by @{const installed_entry}; this abstraction
  does not prove the raw XLEN-path encoding equation @{text "pmpaddr = -1"}.
\<close>

definition current_boot_entries :: "PmpEntry list" where
  "current_boot_entries =
     [allow_l0_entry 0 ((2::nat)^64),
      installed_entry PAYLOAD_START 18 PMP_RWX]"

definition current_boot_state :: "64 word \<Rightarrow> BootState" where
  "current_boot_state old_mstatus =
     \<lparr> bs_entries = current_boot_entries,
       bs_mstatus = sbi_main_mstatus_after old_mstatus,
       bs_mepc = FW_JUMP_ADDR,
       bs_stvec = FW_JUMP_ADDR,
       bs_sie = 0,
       bs_satp = 0 \<rparr>"

theorem current_boot_prepares_smode_entry:
  "smode_entry_setup (current_boot_state old_mstatus)"
proof -
  have mpp: "get_field (sbi_main_mstatus_after old_mstatus) 11 2 = PRV_S"
    by (rule sbi_main_mstatus_mpp_set)
  have mpie: "get_field (sbi_main_mstatus_after old_mstatus) 7 1 = 1"
    by (rule sbi_main_mstatus_mpie_set)
  show ?thesis
    using mpp mpie by (simp add: smode_entry_setup_def current_boot_state_def)
qed

theorem current_boot_allows_any_low_priv_access_inside_phys:
  assumes low: "low_priv p"
      and inside: "addr + width \<le> (2::nat) ^ 64"
      and nonempty: "0 < width"
  shows "pmp_check_entries current_boot_entries p kind addr width = PMP_Allow"
proof -
  have allow0:
    "pmp_check_entries
       (allow_l0_entry 0 ((2::nat)^64) # [installed_entry PAYLOAD_START 18 PMP_RWX])
       p kind addr width = PMP_Allow"
    by (rule allow_entry_permits_low_priv[OF low _ inside nonempty]) simp
  show ?thesis
    using allow0 by (simp add: current_boot_entries_def)
qed

theorem current_boot_does_not_isolate_firmware_region:
  assumes low: "low_priv p"
      and fw_inside: "fw_bgn \<le> addr" "addr + width \<le> fw_en"
      and fw_in_phys: "fw_en \<le> (2::nat) ^ 64"
      and nonempty: "0 < width"
  shows "pmp_check_entries (bs_entries (current_boot_state old_mstatus)) p kind addr width
           = PMP_Allow"
proof -
  have "addr + width \<le> (2::nat) ^ 64"
    using fw_inside fw_in_phys by linarith
  thus ?thesis
    using current_boot_allows_any_low_priv_access_inside_phys[OF low _ nonempty, of addr kind]
    by (simp add: current_boot_state_def)
qed

theorem current_boot_smode_setup_but_not_isolating:
  assumes low: "low_priv p"
      and fw_inside: "fw_bgn \<le> addr" "addr + width \<le> fw_en"
      and fw_in_phys: "fw_en \<le> (2::nat) ^ 64"
      and nonempty: "0 < width"
  shows "smode_entry_setup (current_boot_state old_mstatus) \<and>
         pmp_check_entries (bs_entries (current_boot_state old_mstatus)) p kind addr width
           = PMP_Allow"
  using current_boot_prepares_smode_entry
        current_boot_does_not_isolate_firmware_region[OF low fw_inside fw_in_phys nonempty]
  by simp

subsection \<open>Corrected boot: deny firmware region first\<close>

definition corrected_boot_entries ::
  "xlenbits \<Rightarrow> nat \<Rightarrow> PmpEntry list \<Rightarrow> PmpEntry list" where
  "corrected_boot_entries fw_start k rest = installed_entry fw_start k 0 # rest"

definition corrected_boot_state ::
  "64 word \<Rightarrow> xlenbits \<Rightarrow> nat \<Rightarrow> PmpEntry list \<Rightarrow> BootState" where
  "corrected_boot_state old_mstatus fw_start k rest =
     \<lparr> bs_entries = corrected_boot_entries fw_start k rest,
       bs_mstatus = sbi_main_mstatus_after old_mstatus,
       bs_mepc = FW_JUMP_ADDR,
       bs_stvec = FW_JUMP_ADDR,
       bs_sie = 0,
       bs_satp = 0 \<rparr>"

theorem corrected_boot_prepares_smode_entry:
  "smode_entry_setup (corrected_boot_state old_mstatus fw_start k rest)"
proof -
  have mpp: "get_field (sbi_main_mstatus_after old_mstatus) 11 2 = PRV_S"
    by (rule sbi_main_mstatus_mpp_set)
  have mpie: "get_field (sbi_main_mstatus_after old_mstatus) 7 1 = 1"
    by (rule sbi_main_mstatus_mpie_set)
  show ?thesis
    using mpp mpie by (simp add: smode_entry_setup_def corrected_boot_state_def)
qed

theorem corrected_boot_state_isolates_firmware:
  fixes fw_start :: xlenbits and k :: nat
  defines "fw_base \<equiv> unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4"
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
      and low: "low_priv p"
      and ov: "ranges_overlap fw_base (fw_base + 2 ^ k) addr width"
  shows "pmp_check_entries
           (bs_entries (corrected_boot_state old_mstatus fw_start k rest))
           p kind addr width = PMP_Fault"
proof -
  have ov':
    "ranges_overlap
       (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4)
       (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4 + 2 ^ k)
       addr width"
    using ov by (simp add: fw_base_def)
  have iso: "pmp_check_entries (installed_entry fw_start k 0 # rest) p kind addr width =
             PMP_Fault"
    by (rule corrected_boot_isolates_firmware[OF k_lo k_hi low ov'])
  show ?thesis
    using iso by (simp add: corrected_boot_state_def corrected_boot_entries_def)
qed

theorem corrected_boot_smode_setup_and_isolation:
  fixes fw_start :: xlenbits and k :: nat
  defines "fw_base \<equiv> unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4"
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
      and low: "low_priv p"
      and ov: "ranges_overlap fw_base (fw_base + 2 ^ k) addr width"
  shows "smode_entry_setup (corrected_boot_state old_mstatus fw_start k rest) \<and>
         pmp_check_entries
           (bs_entries (corrected_boot_state old_mstatus fw_start k rest))
           p kind addr width = PMP_Fault"
proof -
  have ov':
    "ranges_overlap
       (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4)
       (unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4 + 2 ^ k)
       addr width"
    using ov by (simp add: fw_base_def)
  have iso:
    "pmp_check_entries
       (bs_entries (corrected_boot_state old_mstatus fw_start k rest))
       p kind addr width = PMP_Fault"
    using corrected_boot_state_isolates_firmware[OF k_lo k_hi low ov'] by simp
  show ?thesis using corrected_boot_prepares_smode_entry iso by simp
qed

end
