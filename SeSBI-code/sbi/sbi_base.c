#include "sbi_ecall.h"
#include "sbi_trap.h"
#include "sbi_error.h"

struct sbiret sbi_ecall_base(unsigned long fid, struct sbi_trap_regs *regs)
{
	switch (fid) {
	case SBI_BASE_GET_SPEC_VERSION:
		return (struct sbiret){ .error = SBI_SUCCESS,
					.value = SBI_SPEC_VERSION };
	case SBI_BASE_GET_IMPL_ID:
		return (struct sbiret){ .error = SBI_SUCCESS,
					.value = SBI_IMPL_ID_SESBI };
	case SBI_BASE_GET_IMPL_VERSION:
		return (struct sbiret){ .error = SBI_SUCCESS,
					.value = SBI_IMPL_VERSION };
	case SBI_BASE_PROBE_EXTENSION:
		return (struct sbiret){ .error = SBI_SUCCESS,
					.value = sbi_extension_supported(regs->a0) };
	case SBI_BASE_GET_MVENDORID:
	case SBI_BASE_GET_MARCHID:
	case SBI_BASE_GET_MIMPID:
		return (struct sbiret){ .error = SBI_SUCCESS, .value = 0 };
	default:
		return (struct sbiret){ .error = SBI_ERR_NOT_SUPPORTED };
	}
}
