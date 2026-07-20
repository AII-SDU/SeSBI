#include "sbi_ecall.h"
#include "sbi_trap.h"
#include "sbi_error.h"

int sbi_extension_supported(unsigned long eid)
{
	switch (eid) {
	case SBI_EXT_BASE:
	case SBI_EXT_TIME:
	case SBI_EXT_DBCN:
	case SBI_EXT_IPI:
	case SBI_EXT_RFENCE:
	case SBI_EXT_HSM:
	case SBI_EXT_SRST:
		return 1;
	default:
		return 0;
	}
}

int sbi_hart_mask_targets_boot_hart_only(unsigned long hart_mask,
					 unsigned long hart_mask_base)
{
	if (hart_mask == 0)
		return 1;

	if (hart_mask_base == (unsigned long)-1)
		return 1;

	if (hart_mask_base == 0 && (hart_mask & ~1UL) == 0)
		return 1;

	return 0;
}

struct sbiret sbi_ecall_dispatch(struct sbi_trap_regs *regs)
{
	unsigned long eid = regs->a7;
	unsigned long fid = regs->a6;

	switch (eid) {
	case SBI_EXT_BASE:
		return sbi_ecall_base(fid, regs);
	case SBI_EXT_TIME:
		return sbi_ecall_time(fid, regs);
	case SBI_EXT_DBCN:
		return sbi_ecall_dbcn(fid, regs);
	case SBI_EXT_IPI:
		return sbi_ecall_ipi(fid, regs);
	case SBI_EXT_RFENCE:
		return sbi_ecall_rfence(fid, regs);
	case SBI_EXT_HSM:
		return sbi_ecall_hsm(fid, regs);
	case SBI_EXT_SRST:
		return sbi_ecall_srst(fid, regs);
	default:
		return (struct sbiret){ .error = SBI_ERR_NOT_SUPPORTED };
	}
}
