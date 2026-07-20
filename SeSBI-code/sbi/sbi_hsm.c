#include "sbi_ecall.h"
#include "sbi_trap.h"
#include "sbi_error.h"

struct sbiret sbi_ecall_hsm(unsigned long fid, struct sbi_trap_regs *regs)
{
	switch (fid) {
	case SBI_HSM_HART_START:
		if (regs->a0 == 0)
			return (struct sbiret){ .error = SBI_ERR_ALREADY_AVAILABLE };
		return (struct sbiret){ .error = SBI_ERR_INVALID_PARAM };
	case SBI_HSM_HART_STOP:
		return (struct sbiret){ .error = SBI_ERR_FAILED };
	case SBI_HSM_HART_GET_STATUS:
		if (regs->a0 != 0)
			return (struct sbiret){ .error = SBI_ERR_INVALID_PARAM };
		return (struct sbiret){ .error = SBI_SUCCESS,
					.value = SBI_HSM_STATE_STARTED };
	case SBI_HSM_HART_SUSPEND:
		return (struct sbiret){ .error = SBI_ERR_NOT_SUPPORTED };
	default:
		return (struct sbiret){ .error = SBI_ERR_NOT_SUPPORTED };
	}
}
