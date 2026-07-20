#ifndef _SBI_ECALL_H
#define _SBI_ECALL_H

#include "asm/sbi.h"

struct sbi_trap_regs;

struct sbiret sbi_ecall_dispatch(struct sbi_trap_regs *regs);
int sbi_extension_supported(unsigned long eid);
int sbi_hart_mask_targets_boot_hart_only(unsigned long hart_mask,
					 unsigned long hart_mask_base);

struct sbiret sbi_ecall_base(unsigned long fid, struct sbi_trap_regs *regs);
struct sbiret sbi_ecall_time(unsigned long fid, struct sbi_trap_regs *regs);
struct sbiret sbi_ecall_dbcn(unsigned long fid, struct sbi_trap_regs *regs);
struct sbiret sbi_ecall_ipi(unsigned long fid, struct sbi_trap_regs *regs);
struct sbiret sbi_ecall_rfence(unsigned long fid, struct sbi_trap_regs *regs);
struct sbiret sbi_ecall_hsm(unsigned long fid, struct sbi_trap_regs *regs);
struct sbiret sbi_ecall_srst(unsigned long fid, struct sbi_trap_regs *regs);

#endif
