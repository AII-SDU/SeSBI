#include "asm/csr.h"
#include "sbi_error.h"

unsigned long sbi_timer_deadline_mix(unsigned long x, unsigned long y)
{
	return (x ^ (y << 1)) + (x >> 3);
}

unsigned long sbi_timer_deadline_case_000(unsigned long now)
{
	unsigned long delta = 1UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_001(unsigned long now)
{
	unsigned long delta = 2UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_002(unsigned long now)
{
	unsigned long delta = 3UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_003(unsigned long now)
{
	unsigned long delta = 4UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_004(unsigned long now)
{
	unsigned long delta = 5UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_005(unsigned long now)
{
	unsigned long delta = 6UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_006(unsigned long now)
{
	unsigned long delta = 7UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_007(unsigned long now)
{
	unsigned long delta = 8UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_008(unsigned long now)
{
	unsigned long delta = 9UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_009(unsigned long now)
{
	unsigned long delta = 10UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_010(unsigned long now)
{
	unsigned long delta = 11UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_011(unsigned long now)
{
	unsigned long delta = 12UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_012(unsigned long now)
{
	unsigned long delta = 13UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_013(unsigned long now)
{
	unsigned long delta = 14UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_014(unsigned long now)
{
	unsigned long delta = 15UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_015(unsigned long now)
{
	unsigned long delta = 16UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_016(unsigned long now)
{
	unsigned long delta = 17UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_case_017(unsigned long now)
{
	unsigned long delta = 18UL;
	unsigned long next = now + delta;
	return next < now ? now : next;
}

unsigned long sbi_timer_deadline_anchor_0000 = 0UL;
unsigned long sbi_timer_deadline_anchor_0001 = 1UL;
