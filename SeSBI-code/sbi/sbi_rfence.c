#include "sbi_ecall.h"
#include "sbi_trap.h"
#include "sbi_error.h"

static int rfence_range_valid(unsigned long start_addr, unsigned long size)
{
	if (size == 0 || size == (unsigned long)-1)
		return 1;

	if (start_addr + size < start_addr)
		return 0;

	return 1;
}

struct sbiret sbi_ecall_rfence(unsigned long fid, struct sbi_trap_regs *regs)
{
	if (!sbi_hart_mask_targets_boot_hart_only(regs->a0, regs->a1))
		return (struct sbiret){ .error = SBI_ERR_INVALID_PARAM };

	switch (fid) {
	case SBI_RFENCE_REMOTE_FENCE_I:
		asm volatile ("" ::: "memory");
		return (struct sbiret){ .error = SBI_SUCCESS };
	case SBI_RFENCE_REMOTE_SFENCE_VMA:
	case SBI_RFENCE_REMOTE_SFENCE_VMA_ASID:
		if (!rfence_range_valid(regs->a2, regs->a3))
			return (struct sbiret){ .error = SBI_ERR_INVALID_ADDRESS };
		asm volatile ("sfence.vma" ::: "memory");
		return (struct sbiret){ .error = SBI_SUCCESS };
	case SBI_RFENCE_REMOTE_HFENCE_GVMA_VMID:
	case SBI_RFENCE_REMOTE_HFENCE_GVMA:
	case SBI_RFENCE_REMOTE_HFENCE_VVMA_ASID:
	case SBI_RFENCE_REMOTE_HFENCE_VVMA:
		return (struct sbiret){ .error = SBI_ERR_NOT_SUPPORTED };
	default:
		return (struct sbiret){ .error = SBI_ERR_NOT_SUPPORTED };
	}
}
