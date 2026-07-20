#include <stdio.h>

static int old_offset(int reg_idx)
{
	return (reg_idx % 4) * 8;
}

static int fixed_group(int reg_idx)
{
	return reg_idx / 8;
}

static int fixed_offset(int reg_idx)
{
	return (reg_idx % 8) * 8;
}

int main(void)
{
	int reg_idx = 12;

	printf("case=PMPCFG\n");
	printf("reg_idx=%d old_offset=%d fixed_group=%d fixed_offset=%d\n",
	       reg_idx, old_offset(reg_idx), fixed_group(reg_idx),
	       fixed_offset(reg_idx));

	return old_offset(reg_idx) != fixed_offset(reg_idx) &&
	       fixed_group(reg_idx) == 1 ? 0 : 1;
}
