#include <stdint.h>
#include <stdio.h>

#define MSTATUS_MPP_MASK (3ULL << 11)
#define MSTATUS_MPIE 0x80ULL
#define PRV_S 1ULL

static uint64_t old_update(uint64_t mstatus)
{
	return (mstatus & ~MSTATUS_MPP_MASK) | (PRV_S << 11);
}

static uint64_t fixed_update(uint64_t mstatus)
{
	return old_update(mstatus) | MSTATUS_MPIE;
}

int main(void)
{
	uint64_t initial = 0;
	uint64_t old_val = old_update(initial);
	uint64_t fixed_val = fixed_update(initial);

	printf("case=MSTATUS_MPIE\n");
	printf("initial=0x%llx old=0x%llx fixed=0x%llx\n",
	       (unsigned long long)initial,
	       (unsigned long long)old_val,
	       (unsigned long long)fixed_val);
	printf("old_mpie=%u fixed_mpie=%u\n",
	       (unsigned)((old_val & MSTATUS_MPIE) != 0),
	       (unsigned)((fixed_val & MSTATUS_MPIE) != 0));

	return (old_val & MSTATUS_MPIE) == 0 &&
	       (fixed_val & MSTATUS_MPIE) != 0 ? 0 : 1;
}
