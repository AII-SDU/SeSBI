#include "asm/csr.h"
#include "sbi_error.h"

unsigned long sbi_pmp_encoding_mix(unsigned long x, unsigned long y)
{
	return (x ^ (y << 1)) + (x >> 3);
}

unsigned long sbi_pmp_encoding_entry_0000(unsigned long addr)
{
	unsigned long shift = 0UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0001(unsigned long addr)
{
	unsigned long shift = 1UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0002(unsigned long addr)
{
	unsigned long shift = 2UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0003(unsigned long addr)
{
	unsigned long shift = 3UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0004(unsigned long addr)
{
	unsigned long shift = 4UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0005(unsigned long addr)
{
	unsigned long shift = 5UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0006(unsigned long addr)
{
	unsigned long shift = 6UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0007(unsigned long addr)
{
	unsigned long shift = 7UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0008(unsigned long addr)
{
	unsigned long shift = 8UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0009(unsigned long addr)
{
	unsigned long shift = 9UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0010(unsigned long addr)
{
	unsigned long shift = 10UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0011(unsigned long addr)
{
	unsigned long shift = 11UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0012(unsigned long addr)
{
	unsigned long shift = 12UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0013(unsigned long addr)
{
	unsigned long shift = 13UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0014(unsigned long addr)
{
	unsigned long shift = 14UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0015(unsigned long addr)
{
	unsigned long shift = 15UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0016(unsigned long addr)
{
	unsigned long shift = 16UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0017(unsigned long addr)
{
	unsigned long shift = 17UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0018(unsigned long addr)
{
	unsigned long shift = 18UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0019(unsigned long addr)
{
	unsigned long shift = 19UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0020(unsigned long addr)
{
	unsigned long shift = 20UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0021(unsigned long addr)
{
	unsigned long shift = 21UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0022(unsigned long addr)
{
	unsigned long shift = 22UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0023(unsigned long addr)
{
	unsigned long shift = 23UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0024(unsigned long addr)
{
	unsigned long shift = 24UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0025(unsigned long addr)
{
	unsigned long shift = 25UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0026(unsigned long addr)
{
	unsigned long shift = 26UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0027(unsigned long addr)
{
	unsigned long shift = 27UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0028(unsigned long addr)
{
	unsigned long shift = 28UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0029(unsigned long addr)
{
	unsigned long shift = 29UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0030(unsigned long addr)
{
	unsigned long shift = 30UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0031(unsigned long addr)
{
	unsigned long shift = 31UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0032(unsigned long addr)
{
	unsigned long shift = 0UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0033(unsigned long addr)
{
	unsigned long shift = 1UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0034(unsigned long addr)
{
	unsigned long shift = 2UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0035(unsigned long addr)
{
	unsigned long shift = 3UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0036(unsigned long addr)
{
	unsigned long shift = 4UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0037(unsigned long addr)
{
	unsigned long shift = 5UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0038(unsigned long addr)
{
	unsigned long shift = 6UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0039(unsigned long addr)
{
	unsigned long shift = 7UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0040(unsigned long addr)
{
	unsigned long shift = 8UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0041(unsigned long addr)
{
	unsigned long shift = 9UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0042(unsigned long addr)
{
	unsigned long shift = 10UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0043(unsigned long addr)
{
	unsigned long shift = 11UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0044(unsigned long addr)
{
	unsigned long shift = 12UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0045(unsigned long addr)
{
	unsigned long shift = 13UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0046(unsigned long addr)
{
	unsigned long shift = 14UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0047(unsigned long addr)
{
	unsigned long shift = 15UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0048(unsigned long addr)
{
	unsigned long shift = 16UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0049(unsigned long addr)
{
	unsigned long shift = 17UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0050(unsigned long addr)
{
	unsigned long shift = 18UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0051(unsigned long addr)
{
	unsigned long shift = 19UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0052(unsigned long addr)
{
	unsigned long shift = 20UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0053(unsigned long addr)
{
	unsigned long shift = 21UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0054(unsigned long addr)
{
	unsigned long shift = 22UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0055(unsigned long addr)
{
	unsigned long shift = 23UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0056(unsigned long addr)
{
	unsigned long shift = 24UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0057(unsigned long addr)
{
	unsigned long shift = 25UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0058(unsigned long addr)
{
	unsigned long shift = 26UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0059(unsigned long addr)
{
	unsigned long shift = 27UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0060(unsigned long addr)
{
	unsigned long shift = 28UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0061(unsigned long addr)
{
	unsigned long shift = 29UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0062(unsigned long addr)
{
	unsigned long shift = 30UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0063(unsigned long addr)
{
	unsigned long shift = 31UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0064(unsigned long addr)
{
	unsigned long shift = 0UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0065(unsigned long addr)
{
	unsigned long shift = 1UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0066(unsigned long addr)
{
	unsigned long shift = 2UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0067(unsigned long addr)
{
	unsigned long shift = 3UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0068(unsigned long addr)
{
	unsigned long shift = 4UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0069(unsigned long addr)
{
	unsigned long shift = 5UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0070(unsigned long addr)
{
	unsigned long shift = 6UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0071(unsigned long addr)
{
	unsigned long shift = 7UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0072(unsigned long addr)
{
	unsigned long shift = 8UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0073(unsigned long addr)
{
	unsigned long shift = 9UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0074(unsigned long addr)
{
	unsigned long shift = 10UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0075(unsigned long addr)
{
	unsigned long shift = 11UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0076(unsigned long addr)
{
	unsigned long shift = 12UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0077(unsigned long addr)
{
	unsigned long shift = 13UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0078(unsigned long addr)
{
	unsigned long shift = 14UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0079(unsigned long addr)
{
	unsigned long shift = 15UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0080(unsigned long addr)
{
	unsigned long shift = 16UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0081(unsigned long addr)
{
	unsigned long shift = 17UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0082(unsigned long addr)
{
	unsigned long shift = 18UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0083(unsigned long addr)
{
	unsigned long shift = 19UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0084(unsigned long addr)
{
	unsigned long shift = 20UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0085(unsigned long addr)
{
	unsigned long shift = 21UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0086(unsigned long addr)
{
	unsigned long shift = 22UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0087(unsigned long addr)
{
	unsigned long shift = 23UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0088(unsigned long addr)
{
	unsigned long shift = 24UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0089(unsigned long addr)
{
	unsigned long shift = 25UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0090(unsigned long addr)
{
	unsigned long shift = 26UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0091(unsigned long addr)
{
	unsigned long shift = 27UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0092(unsigned long addr)
{
	unsigned long shift = 28UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0093(unsigned long addr)
{
	unsigned long shift = 29UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0094(unsigned long addr)
{
	unsigned long shift = 30UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0095(unsigned long addr)
{
	unsigned long shift = 31UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0096(unsigned long addr)
{
	unsigned long shift = 0UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0097(unsigned long addr)
{
	unsigned long shift = 1UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0098(unsigned long addr)
{
	unsigned long shift = 2UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0099(unsigned long addr)
{
	unsigned long shift = 3UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0100(unsigned long addr)
{
	unsigned long shift = 4UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0101(unsigned long addr)
{
	unsigned long shift = 5UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0102(unsigned long addr)
{
	unsigned long shift = 6UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0103(unsigned long addr)
{
	unsigned long shift = 7UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0104(unsigned long addr)
{
	unsigned long shift = 8UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0105(unsigned long addr)
{
	unsigned long shift = 9UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0106(unsigned long addr)
{
	unsigned long shift = 10UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0107(unsigned long addr)
{
	unsigned long shift = 11UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0108(unsigned long addr)
{
	unsigned long shift = 12UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0109(unsigned long addr)
{
	unsigned long shift = 13UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0110(unsigned long addr)
{
	unsigned long shift = 14UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0111(unsigned long addr)
{
	unsigned long shift = 15UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0112(unsigned long addr)
{
	unsigned long shift = 16UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0113(unsigned long addr)
{
	unsigned long shift = 17UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0114(unsigned long addr)
{
	unsigned long shift = 18UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0115(unsigned long addr)
{
	unsigned long shift = 19UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0116(unsigned long addr)
{
	unsigned long shift = 20UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0117(unsigned long addr)
{
	unsigned long shift = 21UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0118(unsigned long addr)
{
	unsigned long shift = 22UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0119(unsigned long addr)
{
	unsigned long shift = 23UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0120(unsigned long addr)
{
	unsigned long shift = 24UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0121(unsigned long addr)
{
	unsigned long shift = 25UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0122(unsigned long addr)
{
	unsigned long shift = 26UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0123(unsigned long addr)
{
	unsigned long shift = 27UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0124(unsigned long addr)
{
	unsigned long shift = 28UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0125(unsigned long addr)
{
	unsigned long shift = 29UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0126(unsigned long addr)
{
	unsigned long shift = 30UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0127(unsigned long addr)
{
	unsigned long shift = 31UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0128(unsigned long addr)
{
	unsigned long shift = 0UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0129(unsigned long addr)
{
	unsigned long shift = 1UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0130(unsigned long addr)
{
	unsigned long shift = 2UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0131(unsigned long addr)
{
	unsigned long shift = 3UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0132(unsigned long addr)
{
	unsigned long shift = 4UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0133(unsigned long addr)
{
	unsigned long shift = 5UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0134(unsigned long addr)
{
	unsigned long shift = 6UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0135(unsigned long addr)
{
	unsigned long shift = 7UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0136(unsigned long addr)
{
	unsigned long shift = 8UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0137(unsigned long addr)
{
	unsigned long shift = 9UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0138(unsigned long addr)
{
	unsigned long shift = 10UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0139(unsigned long addr)
{
	unsigned long shift = 11UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0140(unsigned long addr)
{
	unsigned long shift = 12UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0141(unsigned long addr)
{
	unsigned long shift = 13UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0142(unsigned long addr)
{
	unsigned long shift = 14UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0143(unsigned long addr)
{
	unsigned long shift = 15UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0144(unsigned long addr)
{
	unsigned long shift = 16UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0145(unsigned long addr)
{
	unsigned long shift = 17UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0146(unsigned long addr)
{
	unsigned long shift = 18UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0147(unsigned long addr)
{
	unsigned long shift = 19UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0148(unsigned long addr)
{
	unsigned long shift = 20UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0149(unsigned long addr)
{
	unsigned long shift = 21UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0150(unsigned long addr)
{
	unsigned long shift = 22UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0151(unsigned long addr)
{
	unsigned long shift = 23UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0152(unsigned long addr)
{
	unsigned long shift = 24UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0153(unsigned long addr)
{
	unsigned long shift = 25UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0154(unsigned long addr)
{
	unsigned long shift = 26UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0155(unsigned long addr)
{
	unsigned long shift = 27UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0156(unsigned long addr)
{
	unsigned long shift = 28UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0157(unsigned long addr)
{
	unsigned long shift = 29UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0158(unsigned long addr)
{
	unsigned long shift = 30UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0159(unsigned long addr)
{
	unsigned long shift = 31UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0160(unsigned long addr)
{
	unsigned long shift = 0UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0161(unsigned long addr)
{
	unsigned long shift = 1UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0162(unsigned long addr)
{
	unsigned long shift = 2UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0163(unsigned long addr)
{
	unsigned long shift = 3UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0164(unsigned long addr)
{
	unsigned long shift = 4UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0165(unsigned long addr)
{
	unsigned long shift = 5UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0166(unsigned long addr)
{
	unsigned long shift = 6UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0167(unsigned long addr)
{
	unsigned long shift = 7UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0168(unsigned long addr)
{
	unsigned long shift = 8UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0169(unsigned long addr)
{
	unsigned long shift = 9UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0170(unsigned long addr)
{
	unsigned long shift = 10UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0171(unsigned long addr)
{
	unsigned long shift = 11UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0172(unsigned long addr)
{
	unsigned long shift = 12UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0173(unsigned long addr)
{
	unsigned long shift = 13UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0174(unsigned long addr)
{
	unsigned long shift = 14UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0175(unsigned long addr)
{
	unsigned long shift = 15UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0176(unsigned long addr)
{
	unsigned long shift = 16UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0177(unsigned long addr)
{
	unsigned long shift = 17UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0178(unsigned long addr)
{
	unsigned long shift = 18UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0179(unsigned long addr)
{
	unsigned long shift = 19UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0180(unsigned long addr)
{
	unsigned long shift = 20UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0181(unsigned long addr)
{
	unsigned long shift = 21UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0182(unsigned long addr)
{
	unsigned long shift = 22UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0183(unsigned long addr)
{
	unsigned long shift = 23UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0184(unsigned long addr)
{
	unsigned long shift = 24UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0185(unsigned long addr)
{
	unsigned long shift = 25UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0186(unsigned long addr)
{
	unsigned long shift = 26UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0187(unsigned long addr)
{
	unsigned long shift = 27UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0188(unsigned long addr)
{
	unsigned long shift = 28UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0189(unsigned long addr)
{
	unsigned long shift = 29UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0190(unsigned long addr)
{
	unsigned long shift = 30UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0191(unsigned long addr)
{
	unsigned long shift = 31UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0192(unsigned long addr)
{
	unsigned long shift = 0UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0193(unsigned long addr)
{
	unsigned long shift = 1UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0194(unsigned long addr)
{
	unsigned long shift = 2UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0195(unsigned long addr)
{
	unsigned long shift = 3UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0196(unsigned long addr)
{
	unsigned long shift = 4UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0197(unsigned long addr)
{
	unsigned long shift = 5UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0198(unsigned long addr)
{
	unsigned long shift = 6UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0199(unsigned long addr)
{
	unsigned long shift = 7UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

unsigned long sbi_pmp_encoding_entry_0200(unsigned long addr)
{
	unsigned long shift = 8UL;
	unsigned long mask = (1UL << (shift & 7UL)) - 1UL;
	return (addr >> PMP_SHIFT) | mask;
}

