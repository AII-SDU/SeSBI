#include <stdint.h>
#include <stdio.h>

static int expired_signed(uint64_t mtimecmp, uint64_t current_time)
{
	return (int64_t)mtimecmp < (int64_t)current_time;
}

static int expired_unsigned(uint64_t mtimecmp, uint64_t current_time)
{
	return mtimecmp < current_time;
}

int main(void)
{
	uint64_t mtimecmp = 0x8000000000000010ULL;
	uint64_t current_time = 0x7ffffffffffffff0ULL;
	int signed_result = expired_signed(mtimecmp, current_time);
	int unsigned_result = expired_unsigned(mtimecmp, current_time);

	printf("case=TIMER_SIGNEDNESS\n");
	printf("mtimecmp=0x%llx current_time=0x%llx\n",
	       (unsigned long long)mtimecmp,
	       (unsigned long long)current_time);
	printf("signed_expired=%d unsigned_expired=%d\n",
	       signed_result, unsigned_result);

	return signed_result != unsigned_result &&
	       unsigned_result == 0 ? 0 : 1;
}
