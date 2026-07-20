#include "sbi_ecall.h"
#include "sbi_trap.h"
#include "sbi_error.h"
#include "io.h"

#define QEMU_TEST_FINISHER	0x100000UL
#define QEMU_FINISHER_FAIL	0x3333U
#define QEMU_FINISHER_PASS	0x5555U
#define QEMU_FINISHER_RESET	0x7777U

static int srst_type_valid(unsigned long reset_type)
{
	return reset_type == SBI_SRST_RESET_TYPE_SHUTDOWN ||
	       reset_type == SBI_SRST_RESET_TYPE_COLD_REBOOT ||
	       reset_type == SBI_SRST_RESET_TYPE_WARM_REBOOT;
}

static int srst_reason_valid(unsigned long reset_reason)
{
	return reset_reason == SBI_SRST_RESET_REASON_NONE ||
	       reset_reason == SBI_SRST_RESET_REASON_FAILURE;
}

struct sbiret sbi_ecall_srst(unsigned long fid, struct sbi_trap_regs *regs)
{
	unsigned long reset_type = regs->a0;
	unsigned long reset_reason = regs->a1;

	if (fid != SBI_SRST_SYSTEM_RESET)
		return (struct sbiret){ .error = SBI_ERR_NOT_SUPPORTED };

	if (!srst_type_valid(reset_type) || !srst_reason_valid(reset_reason))
		return (struct sbiret){ .error = SBI_ERR_INVALID_PARAM };

	if (reset_type == SBI_SRST_RESET_TYPE_SHUTDOWN)
		writel(QEMU_FINISHER_PASS, QEMU_TEST_FINISHER);
	else
		writel(QEMU_FINISHER_RESET, QEMU_TEST_FINISHER);

	writel(QEMU_FINISHER_FAIL, QEMU_TEST_FINISHER);
	return (struct sbiret){ .error = SBI_ERR_FAILED };
}
