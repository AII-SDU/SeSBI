#include "sbi_ecall.h"
#include "sbi_trap.h"
#include "sbi_error.h"
#include "sbi_timer.h"

struct sbiret sbi_ecall_time(unsigned long fid, struct sbi_trap_regs *regs)
{
	if (fid != SBI_TIME_SET_TIMER)
		return (struct sbiret){ .error = SBI_ERR_NOT_SUPPORTED };

	clint_timer_event_start(regs->a0);
	return (struct sbiret){ .error = SBI_SUCCESS };
}
