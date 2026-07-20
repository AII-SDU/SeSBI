#include "io.h"
#include "sbi_trap.h"
#include "sbi_timer.h"
#include "asm/csr.h"
#include "asm/clint.h"

/*
 * Cold-start timer initialization (M-mode, before supervisor handoff).
 *
 * This establishes a deterministic, silent "no deadline" timer-service
 * readiness state.  It does NOT program the first periodic deadline: that is
 * the responsibility of the post-handoff service path
 * (S-mode timer_init -> sbi_set_timer -> ecall -> M-mode handler ->
 * clint_timer_event_start).
 *
 * Post-conditions established here:
 *   - the free-running mtime is left unmodified;
 *   - the boot hart's mtimecmp is set to UINT64_MAX (no comparator match);
 *   - mie.MTIE is cleared (machine timer interrupt disabled);
 *   - any stale mip.STIP is cleared (no pending supervisor timer signal);
 *   - all other bits of mie and mip are preserved;
 *   - no spurious timer interrupt is produced before handoff.
 *
 * Scope note: this is the QEMU 'virt', RV64, single-hart (boot hart) path.
 * VIRT_CLINT_TIMER_CMP addresses the boot hart's comparator; a general
 * multi-hart/platform implementation would index a per-hart comparator.  This
 * is deliberately not presented as a generic multi-hart implementation.
 *
 * Ordering rationale (spurious-interrupt-free):
 *   1. raise mtimecmp to UINT64_MAX first, so mtime < mtimecmp and the
 *      hardware deasserts MTIP before interrupts are touched;
 *   2. then clear mie.MTIE so the machine timer interrupt stays masked;
 *   3. then clear any leftover mip.STIP.
 */
void sbi_timer_init(void)
{
	/*
	 * UINT64_MAX comparator: on RV64 the CLINT compare register is 64-bit,
	 * so a full-ones value can never be reached by the running mtime during
	 * boot.  This does not touch the free-running mtime counter itself.
	 */
	writeq((unsigned long)-1, VIRT_CLINT_TIMER_CMP);

	/*
	 * Mask the machine timer interrupt.  MIP_MTIP is the single MTIP/MTIE
	 * bit (IRQ_M_TIMER); csr_clear only clears that bit, leaving every other
	 * mie bit untouched.
	 */
	csr_clear(mie, MIP_MTIP);

	/*
	 * Clear any residual pending supervisor timer bit so the supervisor does
	 * not observe a phantom timer interrupt immediately after mret.  Other
	 * mip bits are preserved.
	 */
	csr_clear(mip, MIP_STIP);
}

int sbi_timer_has_expired(unsigned long mtimecmp, unsigned long current_time)
{
	return mtimecmp < current_time;
}

void sbi_timer_process(void)
{
	/* 关闭M模式timer的中断，然后设置S模式的timer pending中断*/
	csr_clear(mie, MIP_MTIP);
	csr_set(mip, MIP_STIP);
}

void clint_timer_event_start(unsigned long next_event)
{
	unsigned long current_time = readq(VIRT_CLINT_TIMER_VAL);

	if (sbi_timer_has_expired(next_event, current_time)) {
		csr_set(mip, MIP_STIP);
		return;
	}

	/* Program CLINT Time Compare */
	writeq(next_event, VIRT_CLINT_TIMER_CMP);

	/* 清S模式的timer pending中断，然后使能M模式的timer中断 */
	csr_clear(mip, MIP_STIP);
	csr_set(mie, MIP_MTIP);
}
