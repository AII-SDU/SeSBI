theory SeSBI_PMP_BootConfig
  imports SeSBI_PMP_NAPOT SeSBI_PMP_Isolation
begin

unbundle bit_operations_syntax

section \<open>Bridging the SeSBI firmware CSR encoding to the abstract PMP entry model\<close>

text \<open>
  Experiment 05.  SeSBI_PMP_Isolation reasons about abstract @{typ PmpEntry}
  records (bgn, en, R, W, X, L).  The firmware writes the @{text pmpaddr} /
  @{text pmpcfg} CSRs.  Here we model the actual @{text sbi_set_pmp} encoding
  (SeSBI-code/sbi/sbi_main.c) and prove what abstract entry it installs, then
  connect to the proven isolation theorems.

  SCOPE (kept honest, per the anti-surface-success discipline):
   * We model the per-entry pmpcfg BYTE value computed by sbi_set_pmp
     (prot &= ~PMP_A; prot |= PMP_A_NAPOT) and the pmpaddr NAPOT encoding.
   * The full read-modify-write byte PACKING into the 64-bit pmpcfg CSR
     (pmpcfg_shift / cfgmask, and the no-neighbour-clobber frame property)
     is a SEPARATE, later experiment; it is NOT claimed here.
   * R/W/X/L semantics and entry priority are those of SeSBI_PMP_Isolation,
     which is a faithful but partial model of the official pmpCheck.
\<close>

subsection \<open>PMP cfg bit constants (SeSBI-code/include/asm/csr.h)\<close>

definition PMP_R     :: "8 word" where "PMP_R     = 0x01"
definition PMP_W     :: "8 word" where "PMP_W     = 0x02"
definition PMP_X     :: "8 word" where "PMP_X     = 0x04"
definition PMP_A     :: "8 word" where "PMP_A     = 0x18"
definition PMP_A_NAPOT :: "8 word" where "PMP_A_NAPOT = 0x18"
definition PMP_L     :: "8 word" where "PMP_L     = 0x80"
definition PMP_RWX   :: "8 word" where "PMP_RWX   = PMP_R OR PMP_W OR PMP_X"  \<comment> \<open>0x07\<close>

subsection \<open>sbi_set_pmp's pmpcfg byte and its decoding\<close>

text \<open>sbi_main.c: \<open>prot &= ~PMP_A; prot |= PMP_A_NAPOT\<close> -- the byte written for the
      entry (R/W/X/L taken from the caller's prot, A field forced to NAPOT).\<close>
definition sbi_pmpcfg_byte :: "8 word \<Rightarrow> 8 word" where
  "sbi_pmpcfg_byte prot = (prot AND NOT PMP_A) OR PMP_A_NAPOT"

definition cfg_R :: "8 word \<Rightarrow> bool" where "cfg_R c = bit c 0"
definition cfg_W :: "8 word \<Rightarrow> bool" where "cfg_W c = bit c 1"
definition cfg_X :: "8 word \<Rightarrow> bool" where "cfg_X c = bit c 2"
definition cfg_L :: "8 word \<Rightarrow> bool" where "cfg_L c = bit c 7"

text \<open>The abstract PMP entry installed by \<open>sbi_set_pmp(idx, start, size=2^k, prot)\<close>:
      address range from the NAPOT encoding, R/W/X/L from the cfg byte.\<close>
definition installed_entry :: "xlenbits \<Rightarrow> nat \<Rightarrow> 8 word \<Rightarrow> PmpEntry" where
  "installed_entry start k prot =
     (let c = sbi_pmpcfg_byte prot in
      \<lparr> pmp_bgn = fst (napot_region (pmp_encode_napot start k)),
        pmp_en  = snd (napot_region (pmp_encode_napot start k)),
        pmp_R = cfg_R c, pmp_W = cfg_W c, pmp_X = cfg_X c, pmp_L = cfg_L c \<rparr>)"

subsection \<open>What the deny (prot=0) and allow (prot=RWX) writes install\<close>

lemma sbi_pmpcfg_byte_deny: "sbi_pmpcfg_byte 0 = 0x18"
  by (simp add: sbi_pmpcfg_byte_def PMP_A_def PMP_A_NAPOT_def)

lemma sbi_pmpcfg_byte_allow: "sbi_pmpcfg_byte PMP_RWX = 0x1f"
  by (simp add: sbi_pmpcfg_byte_def PMP_A_def PMP_A_NAPOT_def
                PMP_RWX_def PMP_R_def PMP_W_def PMP_X_def)

lemma cfg_deny_bits:
  "cfg_R (sbi_pmpcfg_byte 0) = False" "cfg_W (sbi_pmpcfg_byte 0) = False"
  "cfg_X (sbi_pmpcfg_byte 0) = False" "cfg_L (sbi_pmpcfg_byte 0) = False"
  by (simp_all add: sbi_pmpcfg_byte_deny cfg_R_def cfg_W_def cfg_X_def cfg_L_def)

lemma cfg_allow_bits:
  "cfg_R (sbi_pmpcfg_byte PMP_RWX) = True" "cfg_W (sbi_pmpcfg_byte PMP_RWX) = True"
  "cfg_X (sbi_pmpcfg_byte PMP_RWX) = True" "cfg_L (sbi_pmpcfg_byte PMP_RWX) = False"
  by (simp_all add: sbi_pmpcfg_byte_allow cfg_R_def cfg_W_def cfg_X_def cfg_L_def)

text \<open>A prot=0 write installs exactly a high-priority L=0 deny entry over the
      NAPOT-encoded region.\<close>
theorem installed_deny:
  fixes start :: xlenbits and k :: nat
  assumes "3 \<le> k" and "k \<le> 63"
  defines "base \<equiv> unat (drop_bit 2 start AND NOT (mask (k-2))) * 4"
  shows "installed_entry start k 0 = deny_l0_entry base (base + 2 ^ k)"
  using napot_interval_correct[OF assms(1,2), of start]
  by (simp add: installed_entry_def deny_l0_entry_def cfg_deny_bits base_def)

text \<open>A prot=RWX write installs an allow entry over the NAPOT-encoded region.\<close>
theorem installed_allow:
  fixes start :: xlenbits and k :: nat
  assumes "3 \<le> k" and "k \<le> 63"
  defines "base \<equiv> unat (drop_bit 2 start AND NOT (mask (k-2))) * 4"
  shows "installed_entry start k PMP_RWX = allow_l0_entry base (base + 2 ^ k)"
  using napot_interval_correct[OF assms(1,2), of start]
  by (simp add: installed_entry_def allow_l0_entry_def cfg_allow_bits base_def)

subsection \<open>Corrected boot config: deny firmware region first, then allow\<close>

text \<open>
  The CORRECTED SeSBI boot must install, BEFORE any allow entry, a deny entry
  (prot=0) covering the M-mode firmware region.  Then any S/U access overlapping
  the firmware region faults -- regardless of later allow entries.
\<close>
theorem corrected_boot_isolates_firmware:
  fixes fw_start :: xlenbits and k :: nat
  defines "fw_base \<equiv> unat (drop_bit 2 fw_start AND NOT (mask (k-2))) * 4"
  assumes k_lo: "3 \<le> k" and k_hi: "k \<le> 63"
      and low: "low_priv p"
      and ov:  "ranges_overlap fw_base (fw_base + 2 ^ k) addr width"
  shows "pmp_check_entries
           (installed_entry fw_start k 0 # rest)
           p kind addr width = PMP_Fault"
proof -
  have "installed_entry fw_start k 0 = deny_l0_entry fw_base (fw_base + 2 ^ k)"
    using installed_deny[OF k_lo k_hi, of fw_start] fw_base_def by simp
  thus ?thesis
    using deny_l0_first_entry_faults_overlap[OF low ov] by simp
qed

subsection \<open>Counterexample: the current allow-all boot does NOT isolate\<close>

text \<open>
  The actual SeSBI boot (sbi_main.c) calls
    sbi_set_pmp(0, 0, -1UL, PMP_RWX);
    sbi_set_pmp(1, 0x80000000, 0x40000, PMP_RWX);
  i.e. entry 0 grants RWX over the whole space at top priority.  An allow entry
  (RWX, L=0) covering the firmware region PERMITS low-privilege access to it --
  so this configuration establishes no firmware isolation.
\<close>
theorem allow_entry_permits_low_priv:
  assumes low: "low_priv p"
      and inside: "bgn \<le> addr" "addr + width \<le> en"
      and nonempty: "0 < width"
  shows "pmp_check_entries (allow_l0_entry bgn en # rest) p kind addr width = PMP_Allow"
proof -
  have nm: "p \<noteq> Machine" using low by (auto simp: low_priv_def)
  have "pmpRangeMatch bgn en addr width = PMP_Match"
    using inside nonempty by (simp add: pmpRangeMatch_Match_iff)
  hence "pmp_entry_check (allow_l0_entry bgn en) p kind addr width = PMP_Allow"
    using nm
    by (cases kind)
       (simp_all add: pmp_entry_check_def allow_l0_entry_def entry_allows_def)
  thus ?thesis by simp
qed

corollary current_allowall_does_not_isolate:
  assumes low: "low_priv p"
      and fw: "fw_bgn \<le> addr" "addr + width \<le> fw_en"
      and nonempty: "0 < width"
  shows "pmp_check_entries (allow_l0_entry fw_bgn fw_en # rest) p kind addr width
           = PMP_Allow"  \<comment> \<open>i.e. NOT PMP_Fault: S/U reaches the firmware region\<close>
  by (rule allow_entry_permits_low_priv[OF low fw nonempty])

end
