#include <stdint.h>
#include <stdio.h>

#define PMP_SHIFT 2

static uint64_t encode_bad(uint64_t base, unsigned log2_size)
{
	uint64_t napot_mask = (1ULL << (log2_size - 2)) - 1;
	return (base >> PMP_SHIFT) | napot_mask;
}

static uint64_t encode_fixed(uint64_t base, unsigned log2_size)
{
	uint64_t napot_mask = (1ULL << (log2_size - 3)) - 1;
	return (base >> PMP_SHIFT) | napot_mask;
}

static unsigned decode_log2_size(uint64_t pmpaddr)
{
	unsigned ones = 0;

	while (pmpaddr & 1) {
		ones++;
		pmpaddr >>= 1;
	}

	return ones + 3;
}

int main(void)
{
	uint64_t base = 0x80000000ULL;
	unsigned log2_size = 18;
	uint64_t bad = encode_bad(base, log2_size);
	uint64_t fixed = encode_fixed(base, log2_size);

	printf("case=NAPOT\n");
	printf("base=0x%llx log2_size=%u\n",
	       (unsigned long long)base, log2_size);
	printf("bad_pmpaddr=0x%llx bad_decoded_log2=%u\n",
	       (unsigned long long)bad, decode_log2_size(bad));
	printf("fixed_pmpaddr=0x%llx fixed_decoded_log2=%u\n",
	       (unsigned long long)fixed, decode_log2_size(fixed));

	return decode_log2_size(fixed) == log2_size &&
	       decode_log2_size(bad) != log2_size ? 0 : 1;
}
