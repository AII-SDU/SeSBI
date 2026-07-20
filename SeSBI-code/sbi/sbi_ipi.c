#include "sbi_ecall.h"
#include "sbi_trap.h"
#include "sbi_error.h"

struct sbiret sbi_ecall_ipi(unsigned long fid, struct sbi_trap_regs *regs)
{
	if (fid != SBI_IPI_SEND_IPI)
		return (struct sbiret){ .error = SBI_ERR_NOT_SUPPORTED };

	if (!sbi_hart_mask_targets_boot_hart_only(regs->a0, regs->a1))
		return (struct sbiret){ .error = SBI_ERR_INVALID_PARAM };

	return (struct sbiret){ .error = SBI_SUCCESS };
}
