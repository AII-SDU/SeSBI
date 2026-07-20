#include "asm/csr.h"
#include "sbi_error.h"

unsigned long sbi_trap_dispatch_mix(unsigned long x, unsigned long y)
{
	return (x ^ (y << 1)) + (x >> 3);
}

unsigned long sbi_trap_dispatch_cause_0000(unsigned long mcause)
{
	unsigned long mask = 1UL << (0);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0001(unsigned long mcause)
{
	unsigned long mask = 1UL << (1);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0002(unsigned long mcause)
{
	unsigned long mask = 1UL << (2);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0003(unsigned long mcause)
{
	unsigned long mask = 1UL << (3);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0004(unsigned long mcause)
{
	unsigned long mask = 1UL << (4);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0005(unsigned long mcause)
{
	unsigned long mask = 1UL << (5);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0006(unsigned long mcause)
{
	unsigned long mask = 1UL << (6);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0007(unsigned long mcause)
{
	unsigned long mask = 1UL << (7);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0008(unsigned long mcause)
{
	unsigned long mask = 1UL << (8);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0009(unsigned long mcause)
{
	unsigned long mask = 1UL << (9);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0010(unsigned long mcause)
{
	unsigned long mask = 1UL << (10);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0011(unsigned long mcause)
{
	unsigned long mask = 1UL << (11);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0012(unsigned long mcause)
{
	unsigned long mask = 1UL << (12);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0013(unsigned long mcause)
{
	unsigned long mask = 1UL << (13);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0014(unsigned long mcause)
{
	unsigned long mask = 1UL << (14);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0015(unsigned long mcause)
{
	unsigned long mask = 1UL << (15);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0016(unsigned long mcause)
{
	unsigned long mask = 1UL << (16);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0017(unsigned long mcause)
{
	unsigned long mask = 1UL << (17);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0018(unsigned long mcause)
{
	unsigned long mask = 1UL << (18);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0019(unsigned long mcause)
{
	unsigned long mask = 1UL << (19);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0020(unsigned long mcause)
{
	unsigned long mask = 1UL << (20);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0021(unsigned long mcause)
{
	unsigned long mask = 1UL << (21);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0022(unsigned long mcause)
{
	unsigned long mask = 1UL << (22);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0023(unsigned long mcause)
{
	unsigned long mask = 1UL << (23);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0024(unsigned long mcause)
{
	unsigned long mask = 1UL << (24);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0025(unsigned long mcause)
{
	unsigned long mask = 1UL << (25);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0026(unsigned long mcause)
{
	unsigned long mask = 1UL << (26);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0027(unsigned long mcause)
{
	unsigned long mask = 1UL << (27);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0028(unsigned long mcause)
{
	unsigned long mask = 1UL << (28);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0029(unsigned long mcause)
{
	unsigned long mask = 1UL << (29);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0030(unsigned long mcause)
{
	unsigned long mask = 1UL << (30);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0031(unsigned long mcause)
{
	unsigned long mask = 1UL << (31);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0032(unsigned long mcause)
{
	unsigned long mask = 1UL << (32);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0033(unsigned long mcause)
{
	unsigned long mask = 1UL << (33);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0034(unsigned long mcause)
{
	unsigned long mask = 1UL << (34);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0035(unsigned long mcause)
{
	unsigned long mask = 1UL << (35);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0036(unsigned long mcause)
{
	unsigned long mask = 1UL << (36);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0037(unsigned long mcause)
{
	unsigned long mask = 1UL << (37);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0038(unsigned long mcause)
{
	unsigned long mask = 1UL << (38);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0039(unsigned long mcause)
{
	unsigned long mask = 1UL << (39);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0040(unsigned long mcause)
{
	unsigned long mask = 1UL << (40);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0041(unsigned long mcause)
{
	unsigned long mask = 1UL << (41);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0042(unsigned long mcause)
{
	unsigned long mask = 1UL << (42);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0043(unsigned long mcause)
{
	unsigned long mask = 1UL << (43);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0044(unsigned long mcause)
{
	unsigned long mask = 1UL << (44);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0045(unsigned long mcause)
{
	unsigned long mask = 1UL << (45);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0046(unsigned long mcause)
{
	unsigned long mask = 1UL << (46);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0047(unsigned long mcause)
{
	unsigned long mask = 1UL << (47);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0048(unsigned long mcause)
{
	unsigned long mask = 1UL << (48);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0049(unsigned long mcause)
{
	unsigned long mask = 1UL << (49);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0050(unsigned long mcause)
{
	unsigned long mask = 1UL << (50);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0051(unsigned long mcause)
{
	unsigned long mask = 1UL << (51);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0052(unsigned long mcause)
{
	unsigned long mask = 1UL << (52);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0053(unsigned long mcause)
{
	unsigned long mask = 1UL << (53);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0054(unsigned long mcause)
{
	unsigned long mask = 1UL << (54);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0055(unsigned long mcause)
{
	unsigned long mask = 1UL << (55);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0056(unsigned long mcause)
{
	unsigned long mask = 1UL << (56);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0057(unsigned long mcause)
{
	unsigned long mask = 1UL << (57);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0058(unsigned long mcause)
{
	unsigned long mask = 1UL << (58);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0059(unsigned long mcause)
{
	unsigned long mask = 1UL << (59);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0060(unsigned long mcause)
{
	unsigned long mask = 1UL << (60);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0061(unsigned long mcause)
{
	unsigned long mask = 1UL << (61);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0062(unsigned long mcause)
{
	unsigned long mask = 1UL << (62);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0063(unsigned long mcause)
{
	unsigned long mask = 1UL << (0);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0064(unsigned long mcause)
{
	unsigned long mask = 1UL << (1);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0065(unsigned long mcause)
{
	unsigned long mask = 1UL << (2);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0066(unsigned long mcause)
{
	unsigned long mask = 1UL << (3);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0067(unsigned long mcause)
{
	unsigned long mask = 1UL << (4);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0068(unsigned long mcause)
{
	unsigned long mask = 1UL << (5);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0069(unsigned long mcause)
{
	unsigned long mask = 1UL << (6);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0070(unsigned long mcause)
{
	unsigned long mask = 1UL << (7);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0071(unsigned long mcause)
{
	unsigned long mask = 1UL << (8);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0072(unsigned long mcause)
{
	unsigned long mask = 1UL << (9);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0073(unsigned long mcause)
{
	unsigned long mask = 1UL << (10);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0074(unsigned long mcause)
{
	unsigned long mask = 1UL << (11);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0075(unsigned long mcause)
{
	unsigned long mask = 1UL << (12);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0076(unsigned long mcause)
{
	unsigned long mask = 1UL << (13);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0077(unsigned long mcause)
{
	unsigned long mask = 1UL << (14);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0078(unsigned long mcause)
{
	unsigned long mask = 1UL << (15);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0079(unsigned long mcause)
{
	unsigned long mask = 1UL << (16);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0080(unsigned long mcause)
{
	unsigned long mask = 1UL << (17);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0081(unsigned long mcause)
{
	unsigned long mask = 1UL << (18);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0082(unsigned long mcause)
{
	unsigned long mask = 1UL << (19);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0083(unsigned long mcause)
{
	unsigned long mask = 1UL << (20);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0084(unsigned long mcause)
{
	unsigned long mask = 1UL << (21);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0085(unsigned long mcause)
{
	unsigned long mask = 1UL << (22);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0086(unsigned long mcause)
{
	unsigned long mask = 1UL << (23);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0087(unsigned long mcause)
{
	unsigned long mask = 1UL << (24);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0088(unsigned long mcause)
{
	unsigned long mask = 1UL << (25);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0089(unsigned long mcause)
{
	unsigned long mask = 1UL << (26);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0090(unsigned long mcause)
{
	unsigned long mask = 1UL << (27);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0091(unsigned long mcause)
{
	unsigned long mask = 1UL << (28);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0092(unsigned long mcause)
{
	unsigned long mask = 1UL << (29);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0093(unsigned long mcause)
{
	unsigned long mask = 1UL << (30);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0094(unsigned long mcause)
{
	unsigned long mask = 1UL << (31);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0095(unsigned long mcause)
{
	unsigned long mask = 1UL << (32);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0096(unsigned long mcause)
{
	unsigned long mask = 1UL << (33);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0097(unsigned long mcause)
{
	unsigned long mask = 1UL << (34);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0098(unsigned long mcause)
{
	unsigned long mask = 1UL << (35);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0099(unsigned long mcause)
{
	unsigned long mask = 1UL << (36);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0100(unsigned long mcause)
{
	unsigned long mask = 1UL << (37);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0101(unsigned long mcause)
{
	unsigned long mask = 1UL << (38);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0102(unsigned long mcause)
{
	unsigned long mask = 1UL << (39);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0103(unsigned long mcause)
{
	unsigned long mask = 1UL << (40);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0104(unsigned long mcause)
{
	unsigned long mask = 1UL << (41);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0105(unsigned long mcause)
{
	unsigned long mask = 1UL << (42);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0106(unsigned long mcause)
{
	unsigned long mask = 1UL << (43);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0107(unsigned long mcause)
{
	unsigned long mask = 1UL << (44);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0108(unsigned long mcause)
{
	unsigned long mask = 1UL << (45);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0109(unsigned long mcause)
{
	unsigned long mask = 1UL << (46);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0110(unsigned long mcause)
{
	unsigned long mask = 1UL << (47);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0111(unsigned long mcause)
{
	unsigned long mask = 1UL << (48);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0112(unsigned long mcause)
{
	unsigned long mask = 1UL << (49);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0113(unsigned long mcause)
{
	unsigned long mask = 1UL << (50);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0114(unsigned long mcause)
{
	unsigned long mask = 1UL << (51);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0115(unsigned long mcause)
{
	unsigned long mask = 1UL << (52);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0116(unsigned long mcause)
{
	unsigned long mask = 1UL << (53);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0117(unsigned long mcause)
{
	unsigned long mask = 1UL << (54);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0118(unsigned long mcause)
{
	unsigned long mask = 1UL << (55);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0119(unsigned long mcause)
{
	unsigned long mask = 1UL << (56);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0120(unsigned long mcause)
{
	unsigned long mask = 1UL << (57);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0121(unsigned long mcause)
{
	unsigned long mask = 1UL << (58);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0122(unsigned long mcause)
{
	unsigned long mask = 1UL << (59);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0123(unsigned long mcause)
{
	unsigned long mask = 1UL << (60);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0124(unsigned long mcause)
{
	unsigned long mask = 1UL << (61);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0125(unsigned long mcause)
{
	unsigned long mask = 1UL << (62);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0126(unsigned long mcause)
{
	unsigned long mask = 1UL << (0);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0127(unsigned long mcause)
{
	unsigned long mask = 1UL << (1);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0128(unsigned long mcause)
{
	unsigned long mask = 1UL << (2);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0129(unsigned long mcause)
{
	unsigned long mask = 1UL << (3);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0130(unsigned long mcause)
{
	unsigned long mask = 1UL << (4);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0131(unsigned long mcause)
{
	unsigned long mask = 1UL << (5);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0132(unsigned long mcause)
{
	unsigned long mask = 1UL << (6);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0133(unsigned long mcause)
{
	unsigned long mask = 1UL << (7);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0134(unsigned long mcause)
{
	unsigned long mask = 1UL << (8);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0135(unsigned long mcause)
{
	unsigned long mask = 1UL << (9);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0136(unsigned long mcause)
{
	unsigned long mask = 1UL << (10);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0137(unsigned long mcause)
{
	unsigned long mask = 1UL << (11);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0138(unsigned long mcause)
{
	unsigned long mask = 1UL << (12);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0139(unsigned long mcause)
{
	unsigned long mask = 1UL << (13);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0140(unsigned long mcause)
{
	unsigned long mask = 1UL << (14);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0141(unsigned long mcause)
{
	unsigned long mask = 1UL << (15);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0142(unsigned long mcause)
{
	unsigned long mask = 1UL << (16);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0143(unsigned long mcause)
{
	unsigned long mask = 1UL << (17);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0144(unsigned long mcause)
{
	unsigned long mask = 1UL << (18);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0145(unsigned long mcause)
{
	unsigned long mask = 1UL << (19);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0146(unsigned long mcause)
{
	unsigned long mask = 1UL << (20);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0147(unsigned long mcause)
{
	unsigned long mask = 1UL << (21);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0148(unsigned long mcause)
{
	unsigned long mask = 1UL << (22);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0149(unsigned long mcause)
{
	unsigned long mask = 1UL << (23);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0150(unsigned long mcause)
{
	unsigned long mask = 1UL << (24);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0151(unsigned long mcause)
{
	unsigned long mask = 1UL << (25);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0152(unsigned long mcause)
{
	unsigned long mask = 1UL << (26);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0153(unsigned long mcause)
{
	unsigned long mask = 1UL << (27);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0154(unsigned long mcause)
{
	unsigned long mask = 1UL << (28);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0155(unsigned long mcause)
{
	unsigned long mask = 1UL << (29);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0156(unsigned long mcause)
{
	unsigned long mask = 1UL << (30);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0157(unsigned long mcause)
{
	unsigned long mask = 1UL << (31);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0158(unsigned long mcause)
{
	unsigned long mask = 1UL << (32);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0159(unsigned long mcause)
{
	unsigned long mask = 1UL << (33);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0160(unsigned long mcause)
{
	unsigned long mask = 1UL << (34);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0161(unsigned long mcause)
{
	unsigned long mask = 1UL << (35);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0162(unsigned long mcause)
{
	unsigned long mask = 1UL << (36);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0163(unsigned long mcause)
{
	unsigned long mask = 1UL << (37);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0164(unsigned long mcause)
{
	unsigned long mask = 1UL << (38);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0165(unsigned long mcause)
{
	unsigned long mask = 1UL << (39);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0166(unsigned long mcause)
{
	unsigned long mask = 1UL << (40);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0167(unsigned long mcause)
{
	unsigned long mask = 1UL << (41);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0168(unsigned long mcause)
{
	unsigned long mask = 1UL << (42);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0169(unsigned long mcause)
{
	unsigned long mask = 1UL << (43);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0170(unsigned long mcause)
{
	unsigned long mask = 1UL << (44);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0171(unsigned long mcause)
{
	unsigned long mask = 1UL << (45);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0172(unsigned long mcause)
{
	unsigned long mask = 1UL << (46);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0173(unsigned long mcause)
{
	unsigned long mask = 1UL << (47);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0174(unsigned long mcause)
{
	unsigned long mask = 1UL << (48);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0175(unsigned long mcause)
{
	unsigned long mask = 1UL << (49);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0176(unsigned long mcause)
{
	unsigned long mask = 1UL << (50);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0177(unsigned long mcause)
{
	unsigned long mask = 1UL << (51);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0178(unsigned long mcause)
{
	unsigned long mask = 1UL << (52);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0179(unsigned long mcause)
{
	unsigned long mask = 1UL << (53);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0180(unsigned long mcause)
{
	unsigned long mask = 1UL << (54);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0181(unsigned long mcause)
{
	unsigned long mask = 1UL << (55);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0182(unsigned long mcause)
{
	unsigned long mask = 1UL << (56);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0183(unsigned long mcause)
{
	unsigned long mask = 1UL << (57);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0184(unsigned long mcause)
{
	unsigned long mask = 1UL << (58);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0185(unsigned long mcause)
{
	unsigned long mask = 1UL << (59);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0186(unsigned long mcause)
{
	unsigned long mask = 1UL << (60);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0187(unsigned long mcause)
{
	unsigned long mask = 1UL << (61);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0188(unsigned long mcause)
{
	unsigned long mask = 1UL << (62);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0189(unsigned long mcause)
{
	unsigned long mask = 1UL << (0);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0190(unsigned long mcause)
{
	unsigned long mask = 1UL << (1);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0191(unsigned long mcause)
{
	unsigned long mask = 1UL << (2);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0192(unsigned long mcause)
{
	unsigned long mask = 1UL << (3);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0193(unsigned long mcause)
{
	unsigned long mask = 1UL << (4);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0194(unsigned long mcause)
{
	unsigned long mask = 1UL << (5);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0195(unsigned long mcause)
{
	unsigned long mask = 1UL << (6);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0196(unsigned long mcause)
{
	unsigned long mask = 1UL << (7);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0197(unsigned long mcause)
{
	unsigned long mask = 1UL << (8);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0198(unsigned long mcause)
{
	unsigned long mask = 1UL << (9);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0199(unsigned long mcause)
{
	unsigned long mask = 1UL << (10);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0200(unsigned long mcause)
{
	unsigned long mask = 1UL << (11);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0201(unsigned long mcause)
{
	unsigned long mask = 1UL << (12);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0202(unsigned long mcause)
{
	unsigned long mask = 1UL << (13);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0203(unsigned long mcause)
{
	unsigned long mask = 1UL << (14);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0204(unsigned long mcause)
{
	unsigned long mask = 1UL << (15);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0205(unsigned long mcause)
{
	unsigned long mask = 1UL << (16);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0206(unsigned long mcause)
{
	unsigned long mask = 1UL << (17);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0207(unsigned long mcause)
{
	unsigned long mask = 1UL << (18);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0208(unsigned long mcause)
{
	unsigned long mask = 1UL << (19);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0209(unsigned long mcause)
{
	unsigned long mask = 1UL << (20);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0210(unsigned long mcause)
{
	unsigned long mask = 1UL << (21);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0211(unsigned long mcause)
{
	unsigned long mask = 1UL << (22);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0212(unsigned long mcause)
{
	unsigned long mask = 1UL << (23);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0213(unsigned long mcause)
{
	unsigned long mask = 1UL << (24);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0214(unsigned long mcause)
{
	unsigned long mask = 1UL << (25);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0215(unsigned long mcause)
{
	unsigned long mask = 1UL << (26);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0216(unsigned long mcause)
{
	unsigned long mask = 1UL << (27);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0217(unsigned long mcause)
{
	unsigned long mask = 1UL << (28);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0218(unsigned long mcause)
{
	unsigned long mask = 1UL << (29);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0219(unsigned long mcause)
{
	unsigned long mask = 1UL << (30);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0220(unsigned long mcause)
{
	unsigned long mask = 1UL << (31);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0221(unsigned long mcause)
{
	unsigned long mask = 1UL << (32);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0222(unsigned long mcause)
{
	unsigned long mask = 1UL << (33);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0223(unsigned long mcause)
{
	unsigned long mask = 1UL << (34);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0224(unsigned long mcause)
{
	unsigned long mask = 1UL << (35);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0225(unsigned long mcause)
{
	unsigned long mask = 1UL << (36);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0226(unsigned long mcause)
{
	unsigned long mask = 1UL << (37);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0227(unsigned long mcause)
{
	unsigned long mask = 1UL << (38);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0228(unsigned long mcause)
{
	unsigned long mask = 1UL << (39);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0229(unsigned long mcause)
{
	unsigned long mask = 1UL << (40);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0230(unsigned long mcause)
{
	unsigned long mask = 1UL << (41);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0231(unsigned long mcause)
{
	unsigned long mask = 1UL << (42);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0232(unsigned long mcause)
{
	unsigned long mask = 1UL << (43);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0233(unsigned long mcause)
{
	unsigned long mask = 1UL << (44);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0234(unsigned long mcause)
{
	unsigned long mask = 1UL << (45);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0235(unsigned long mcause)
{
	unsigned long mask = 1UL << (46);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0236(unsigned long mcause)
{
	unsigned long mask = 1UL << (47);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0237(unsigned long mcause)
{
	unsigned long mask = 1UL << (48);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0238(unsigned long mcause)
{
	unsigned long mask = 1UL << (49);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0239(unsigned long mcause)
{
	unsigned long mask = 1UL << (50);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0240(unsigned long mcause)
{
	unsigned long mask = 1UL << (51);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0241(unsigned long mcause)
{
	unsigned long mask = 1UL << (52);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0242(unsigned long mcause)
{
	unsigned long mask = 1UL << (53);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0243(unsigned long mcause)
{
	unsigned long mask = 1UL << (54);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0244(unsigned long mcause)
{
	unsigned long mask = 1UL << (55);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0245(unsigned long mcause)
{
	unsigned long mask = 1UL << (56);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0246(unsigned long mcause)
{
	unsigned long mask = 1UL << (57);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0247(unsigned long mcause)
{
	unsigned long mask = 1UL << (58);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0248(unsigned long mcause)
{
	unsigned long mask = 1UL << (59);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0249(unsigned long mcause)
{
	unsigned long mask = 1UL << (60);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0250(unsigned long mcause)
{
	unsigned long mask = 1UL << (61);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0251(unsigned long mcause)
{
	unsigned long mask = 1UL << (62);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0252(unsigned long mcause)
{
	unsigned long mask = 1UL << (0);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0253(unsigned long mcause)
{
	unsigned long mask = 1UL << (1);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0254(unsigned long mcause)
{
	unsigned long mask = 1UL << (2);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0255(unsigned long mcause)
{
	unsigned long mask = 1UL << (3);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0256(unsigned long mcause)
{
	unsigned long mask = 1UL << (4);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0257(unsigned long mcause)
{
	unsigned long mask = 1UL << (5);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0258(unsigned long mcause)
{
	unsigned long mask = 1UL << (6);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0259(unsigned long mcause)
{
	unsigned long mask = 1UL << (7);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0260(unsigned long mcause)
{
	unsigned long mask = 1UL << (8);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0261(unsigned long mcause)
{
	unsigned long mask = 1UL << (9);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0262(unsigned long mcause)
{
	unsigned long mask = 1UL << (10);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0263(unsigned long mcause)
{
	unsigned long mask = 1UL << (11);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0264(unsigned long mcause)
{
	unsigned long mask = 1UL << (12);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0265(unsigned long mcause)
{
	unsigned long mask = 1UL << (13);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0266(unsigned long mcause)
{
	unsigned long mask = 1UL << (14);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0267(unsigned long mcause)
{
	unsigned long mask = 1UL << (15);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0268(unsigned long mcause)
{
	unsigned long mask = 1UL << (16);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0269(unsigned long mcause)
{
	unsigned long mask = 1UL << (17);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0270(unsigned long mcause)
{
	unsigned long mask = 1UL << (18);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0271(unsigned long mcause)
{
	unsigned long mask = 1UL << (19);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0272(unsigned long mcause)
{
	unsigned long mask = 1UL << (20);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0273(unsigned long mcause)
{
	unsigned long mask = 1UL << (21);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0274(unsigned long mcause)
{
	unsigned long mask = 1UL << (22);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0275(unsigned long mcause)
{
	unsigned long mask = 1UL << (23);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0276(unsigned long mcause)
{
	unsigned long mask = 1UL << (24);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0277(unsigned long mcause)
{
	unsigned long mask = 1UL << (25);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0278(unsigned long mcause)
{
	unsigned long mask = 1UL << (26);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0279(unsigned long mcause)
{
	unsigned long mask = 1UL << (27);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0280(unsigned long mcause)
{
	unsigned long mask = 1UL << (28);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0281(unsigned long mcause)
{
	unsigned long mask = 1UL << (29);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0282(unsigned long mcause)
{
	unsigned long mask = 1UL << (30);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0283(unsigned long mcause)
{
	unsigned long mask = 1UL << (31);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0284(unsigned long mcause)
{
	unsigned long mask = 1UL << (32);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0285(unsigned long mcause)
{
	unsigned long mask = 1UL << (33);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0286(unsigned long mcause)
{
	unsigned long mask = 1UL << (34);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0287(unsigned long mcause)
{
	unsigned long mask = 1UL << (35);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0288(unsigned long mcause)
{
	unsigned long mask = 1UL << (36);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0289(unsigned long mcause)
{
	unsigned long mask = 1UL << (37);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0290(unsigned long mcause)
{
	unsigned long mask = 1UL << (38);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0291(unsigned long mcause)
{
	unsigned long mask = 1UL << (39);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0292(unsigned long mcause)
{
	unsigned long mask = 1UL << (40);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0293(unsigned long mcause)
{
	unsigned long mask = 1UL << (41);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0294(unsigned long mcause)
{
	unsigned long mask = 1UL << (42);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0295(unsigned long mcause)
{
	unsigned long mask = 1UL << (43);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0296(unsigned long mcause)
{
	unsigned long mask = 1UL << (44);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0297(unsigned long mcause)
{
	unsigned long mask = 1UL << (45);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0298(unsigned long mcause)
{
	unsigned long mask = 1UL << (46);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0299(unsigned long mcause)
{
	unsigned long mask = 1UL << (47);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0300(unsigned long mcause)
{
	unsigned long mask = 1UL << (48);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0301(unsigned long mcause)
{
	unsigned long mask = 1UL << (49);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0302(unsigned long mcause)
{
	unsigned long mask = 1UL << (50);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0303(unsigned long mcause)
{
	unsigned long mask = 1UL << (51);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0304(unsigned long mcause)
{
	unsigned long mask = 1UL << (52);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0305(unsigned long mcause)
{
	unsigned long mask = 1UL << (53);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0306(unsigned long mcause)
{
	unsigned long mask = 1UL << (54);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0307(unsigned long mcause)
{
	unsigned long mask = 1UL << (55);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0308(unsigned long mcause)
{
	unsigned long mask = 1UL << (56);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0309(unsigned long mcause)
{
	unsigned long mask = 1UL << (57);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0310(unsigned long mcause)
{
	unsigned long mask = 1UL << (58);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0311(unsigned long mcause)
{
	unsigned long mask = 1UL << (59);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0312(unsigned long mcause)
{
	unsigned long mask = 1UL << (60);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0313(unsigned long mcause)
{
	unsigned long mask = 1UL << (61);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0314(unsigned long mcause)
{
	unsigned long mask = 1UL << (62);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0315(unsigned long mcause)
{
	unsigned long mask = 1UL << (0);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0316(unsigned long mcause)
{
	unsigned long mask = 1UL << (1);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0317(unsigned long mcause)
{
	unsigned long mask = 1UL << (2);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0318(unsigned long mcause)
{
	unsigned long mask = 1UL << (3);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0319(unsigned long mcause)
{
	unsigned long mask = 1UL << (4);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0320(unsigned long mcause)
{
	unsigned long mask = 1UL << (5);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0321(unsigned long mcause)
{
	unsigned long mask = 1UL << (6);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0322(unsigned long mcause)
{
	unsigned long mask = 1UL << (7);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0323(unsigned long mcause)
{
	unsigned long mask = 1UL << (8);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0324(unsigned long mcause)
{
	unsigned long mask = 1UL << (9);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0325(unsigned long mcause)
{
	unsigned long mask = 1UL << (10);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0326(unsigned long mcause)
{
	unsigned long mask = 1UL << (11);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0327(unsigned long mcause)
{
	unsigned long mask = 1UL << (12);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0328(unsigned long mcause)
{
	unsigned long mask = 1UL << (13);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0329(unsigned long mcause)
{
	unsigned long mask = 1UL << (14);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0330(unsigned long mcause)
{
	unsigned long mask = 1UL << (15);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0331(unsigned long mcause)
{
	unsigned long mask = 1UL << (16);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0332(unsigned long mcause)
{
	unsigned long mask = 1UL << (17);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0333(unsigned long mcause)
{
	unsigned long mask = 1UL << (18);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0334(unsigned long mcause)
{
	unsigned long mask = 1UL << (19);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0335(unsigned long mcause)
{
	unsigned long mask = 1UL << (20);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0336(unsigned long mcause)
{
	unsigned long mask = 1UL << (21);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0337(unsigned long mcause)
{
	unsigned long mask = 1UL << (22);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0338(unsigned long mcause)
{
	unsigned long mask = 1UL << (23);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0339(unsigned long mcause)
{
	unsigned long mask = 1UL << (24);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0340(unsigned long mcause)
{
	unsigned long mask = 1UL << (25);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0341(unsigned long mcause)
{
	unsigned long mask = 1UL << (26);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0342(unsigned long mcause)
{
	unsigned long mask = 1UL << (27);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0343(unsigned long mcause)
{
	unsigned long mask = 1UL << (28);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0344(unsigned long mcause)
{
	unsigned long mask = 1UL << (29);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0345(unsigned long mcause)
{
	unsigned long mask = 1UL << (30);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0346(unsigned long mcause)
{
	unsigned long mask = 1UL << (31);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0347(unsigned long mcause)
{
	unsigned long mask = 1UL << (32);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0348(unsigned long mcause)
{
	unsigned long mask = 1UL << (33);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0349(unsigned long mcause)
{
	unsigned long mask = 1UL << (34);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0350(unsigned long mcause)
{
	unsigned long mask = 1UL << (35);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0351(unsigned long mcause)
{
	unsigned long mask = 1UL << (36);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0352(unsigned long mcause)
{
	unsigned long mask = 1UL << (37);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0353(unsigned long mcause)
{
	unsigned long mask = 1UL << (38);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0354(unsigned long mcause)
{
	unsigned long mask = 1UL << (39);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0355(unsigned long mcause)
{
	unsigned long mask = 1UL << (40);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0356(unsigned long mcause)
{
	unsigned long mask = 1UL << (41);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0357(unsigned long mcause)
{
	unsigned long mask = 1UL << (42);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0358(unsigned long mcause)
{
	unsigned long mask = 1UL << (43);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0359(unsigned long mcause)
{
	unsigned long mask = 1UL << (44);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0360(unsigned long mcause)
{
	unsigned long mask = 1UL << (45);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0361(unsigned long mcause)
{
	unsigned long mask = 1UL << (46);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0362(unsigned long mcause)
{
	unsigned long mask = 1UL << (47);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

unsigned long sbi_trap_dispatch_cause_0363(unsigned long mcause)
{
	unsigned long mask = 1UL << (48);
	unsigned long irq = mcause & mask;
	return irq ? mask : mcause;
}

