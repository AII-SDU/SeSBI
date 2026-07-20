#include <assert.h>
#include <limits.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

#include "asm/csr.h"

struct mock_pmp_state {
	unsigned long cfg0;
	unsigned long cfg2;
	unsigned long addr[MAX_CSR_PMP];
	unsigned int reads;
	unsigned int writes;
	int read_csr;
	int write_csr[2];
};

static struct mock_pmp_state mock;

static int addr_index(int csr_num)
{
	if (csr_num < CSR_PMPADDR0 || csr_num > CSR_PMPADDR15)
		return -1;
	return csr_num - CSR_PMPADDR0;
}

unsigned long read_csr_num(int csr_num)
{
	mock.reads++;
	mock.read_csr = csr_num;
	if (csr_num == CSR_PMPCFG0)
		return mock.cfg0;
	if (csr_num == CSR_PMPCFG2)
		return mock.cfg2;
	assert(!"unexpected CSR read");
	return 0;
}

void write_csr_num(int csr_num, unsigned long value)
{
	int index;

	assert(mock.writes < 2);
	mock.write_csr[mock.writes++] = csr_num;
	if (csr_num == CSR_PMPCFG0) {
		mock.cfg0 = value;
		return;
	}
	if (csr_num == CSR_PMPCFG2) {
		mock.cfg2 = value;
		return;
	}
	index = addr_index(csr_num);
	assert(index >= 0);
	mock.addr[index] = value;
}

unsigned long log2roundup(unsigned long value)
{
	unsigned long order = 0;

	while (order < RISCV_XLEN) {
		if (value <= (1UL << order))
			break;
		order++;
	}
	return order;
}

int printk(const char *format, ...)
{
	(void)format;
	return 0;
}

/* Compile the production implementation with only sbi_set_pmp enabled. */
#define SBI_PMP_UNIT_TEST 1
#include "../sbi/sbi_main.c"

static void reset_mock(void)
{
	int i;

	mock.cfg0 = 0x8877665544332211UL;
	mock.cfg2 = 0x1020304050607080UL;
	for (i = 0; i < MAX_CSR_PMP; i++)
		mock.addr[i] = 0xa5a5000000000000UL + (unsigned long)i;
	mock.reads = 0;
	mock.writes = 0;
	mock.read_csr = -1;
	mock.write_csr[0] = -1;
	mock.write_csr[1] = -1;
}

static unsigned long replace_byte(unsigned long old, int offset,
				  unsigned long value)
{
	unsigned int shift = (unsigned int)offset * 8;
	unsigned long mask = 0xffUL << shift;

	return (old & ~mask) | ((value << shift) & mask);
}

static unsigned long expected_napot(unsigned long start, unsigned long size)
{
	return (start >> PMP_SHIFT) | ((size >> 3) - 1);
}

static void expect_invalid(int index, unsigned long start, unsigned long size,
			   unsigned long prot)
{
	struct mock_pmp_state before;

	reset_mock();
	before = mock;
	assert(sbi_set_pmp(index, start, size, prot) == -1);
	assert(mock.reads == 0);
	assert(mock.writes == 0);
	assert(memcmp(&mock.cfg0, &before.cfg0,
		      offsetof(struct mock_pmp_state, reads)) == 0);
}

static void test_invalid_requests_have_no_csr_effect(void)
{
	const int invalid_indices[] = { INT_MIN, -16, -14, -1, 16, INT_MAX };
	size_t i;

	for (i = 0; i < sizeof(invalid_indices) / sizeof(invalid_indices[0]); i++)
		expect_invalid(invalid_indices[i], 0x80000000UL, 0x40000UL,
			       PMP_RWX);

	expect_invalid(0, 0x80000000UL, 0, PMP_RWX);
	expect_invalid(0, 0x80000000UL, 1, PMP_RWX);
	expect_invalid(0, 0x80000000UL, 2, PMP_RWX);
	expect_invalid(0, 0x80000000UL, 3, PMP_RWX);
	expect_invalid(0, 0x80000000UL, 6, PMP_RWX);
	expect_invalid(0, 0x80000004UL, 8, PMP_RWX);
	expect_invalid(0, 0x1000UL, ~0UL, PMP_RWX);

	/* Unsupported bits and the reserved W=1,R=0 encodings. */
	expect_invalid(0, 0x80000000UL, 0x40000UL, PMP_A_NAPOT);
	expect_invalid(0, 0x80000000UL, 0x40000UL, PMP_L);
	expect_invalid(0, 0x80000000UL, 0x40000UL, PMP_W);
	expect_invalid(0, 0x80000000UL, 0x40000UL, PMP_W | PMP_X);
}

static void test_all_sixteen_selectors_and_frames(void)
{
	int index;

	for (index = 0; index < MAX_CSR_PMP; index++) {
		const unsigned long start = 0x80000000UL +
					    (unsigned long)index * 0x1000UL;
		const unsigned long size = 0x1000UL;
		const int offset = index & 7;
		const int bank = index < 8 ? CSR_PMPCFG0 : CSR_PMPCFG2;
		const unsigned long old_cfg0 = 0x8877665544332211UL;
		const unsigned long old_cfg2 = 0x1020304050607080UL;
		const unsigned long cfg_byte = PMP_RWX | PMP_A_NAPOT;
		int other;

		reset_mock();
		assert(sbi_set_pmp(index, start, size, PMP_RWX) == 0);
		assert(mock.reads == 1);
		assert(mock.writes == 2);
		assert(mock.read_csr == bank);
		assert(mock.write_csr[0] == CSR_PMPADDR0 + index);
		assert(mock.write_csr[1] == bank);
		assert(mock.addr[index] == expected_napot(start, size));
		for (other = 0; other < MAX_CSR_PMP; other++) {
			if (other != index)
				assert(mock.addr[other] ==
				       0xa5a5000000000000UL + (unsigned long)other);
		}
		if (index < 8) {
			assert(mock.cfg0 == replace_byte(old_cfg0, offset, cfg_byte));
			assert(mock.cfg2 == old_cfg2);
		} else {
			assert(mock.cfg0 == old_cfg0);
			assert(mock.cfg2 == replace_byte(old_cfg2, offset, cfg_byte));
		}
	}
}

static void test_na4_and_boot_requests(void)
{
	reset_mock();
	assert(sbi_set_pmp(7, 0x80000004UL, 4, PMP_R | PMP_X) == 0);
	assert(mock.addr[7] == (0x80000004UL >> PMP_SHIFT));
	assert(mock.cfg0 == replace_byte(0x8877665544332211UL, 7,
					 PMP_R | PMP_X | PMP_A_NA4));

	/* The two region shapes used by both current and corrected boot layouts. */
	reset_mock();
	assert(sbi_set_pmp(0, 0, ~0UL, PMP_RWX) == 0);
	assert(mock.addr[0] == ~0UL);
	assert(mock.cfg0 == replace_byte(0x8877665544332211UL, 0,
					 PMP_RWX | PMP_A_NAPOT));

	reset_mock();
	assert(sbi_set_pmp(1, 0x80000000UL, 0x40000UL, PMP_RWX) == 0);
	assert(mock.addr[1] == expected_napot(0x80000000UL, 0x40000UL));
	assert(mock.cfg0 == replace_byte(0x8877665544332211UL, 1,
					 PMP_RWX | PMP_A_NAPOT));

	/* The corrected layout uses the same shapes in the opposite order. */
	reset_mock();
	assert(sbi_set_pmp(0, 0x80000000UL, 0x40000UL, 0) == 0);
	assert(mock.addr[0] == expected_napot(0x80000000UL, 0x40000UL));
	assert(mock.cfg0 == replace_byte(0x8877665544332211UL, 0,
					 PMP_A_NAPOT));

	reset_mock();
	assert(sbi_set_pmp(1, 0, ~0UL, PMP_RWX) == 0);
	assert(mock.addr[1] == ~0UL);
	assert(mock.cfg0 == replace_byte(0x8877665544332211UL, 1,
					 PMP_RWX | PMP_A_NAPOT));
}

int main(void)
{
	test_invalid_requests_have_no_csr_effect();
	test_all_sixteen_selectors_and_frames();
	test_na4_and_boot_requests();
	puts("PASS: sbi_set_pmp validates inputs before CSR access and preserves non-target PMP state");
	return 0;
}
