#include "asm/csr.h"
//#include "asm/sbi.h"
#include "printk.h"
#include "sbi_lib.h"
#ifndef SBI_PMP_UNIT_TEST
#include "uart.h"
#include "sbi_trap.h"
#include "sbi_timer.h"
#endif

#define FW_JUMP_ADDR 0x80200000
#define FW_PROTECT_BASE 0x80000000UL
#define FW_PROTECT_SIZE 0x40000UL

#define BANNER \
"      ___                ___     ___    ___   ___\n"\
"    //   ) )           //   ) )//   ))    / /\n" \
"   ((         ___     ((      //___//    / /\n"\
"    \\      //___) )   \\    // __ (     / /\n"\
"       ) ) //           ) ) //    ))   / /\n" \
"((___/ /  ((____ ((___ / / //____// __/ /___\n"


int sbi_set_pmp(int reg_idx, unsigned long start, unsigned long size, unsigned long prot)
{
	int order;
	int pmpcfg_csr, pmpcfg_shift, pmpaddr_csr;
	unsigned long cfgmask, pmpcfg;
	unsigned long addrmask, pmpaddr;
	int allow_all;

	/*
	 * Validate the complete request before the first PMP CSR access.  In
	 * particular, reg_idx is signed: checking only the upper bound lets
	 * negative values alias supported CSR numbers after the selector
	 * arithmetic below.
	 */
	if (reg_idx < 0 || reg_idx >= MAX_CSR_PMP)
		return -1;

	/* The public prot argument contains only the R/W/X permission bits. */
	if ((prot & ~PMP_RWX) != 0)
		return -1;
	/* RISC-V reserves the permission encodings with W=1 and R=0. */
	if ((prot & PMP_W) != 0 && (prot & PMP_R) == 0)
		return -1;

	/*
	 * SeSBI uses (start=0, size=UINT64_MAX) as its explicit allow-all
	 * sentinel.  Every ordinary region is represented exactly: its size is
	 * a power of two of at least four bytes, its base is naturally aligned,
	 * and its last byte remains in the RV64 address space.
	 */
	allow_all = (start == 0 && size == ~0UL);
	if (allow_all) {
		order = RISCV_XLEN;
	} else {
		if (size < (1UL << PMP_SHIFT) || (size & (size - 1)) != 0)
			return -1;
		if ((start & (size - 1)) != 0)
			return -1;
		if (start > ~0UL - (size - 1))
			return -1;
		order = log2roundup(size);
	}

	if (order < PMP_SHIFT)
		return -1;

	printk("%s: start: 0x%lx order %d prot 0x%lx\n", __func__, start, order, prot);

	pmpaddr = start >> PMP_SHIFT;

	/* 对于RV64，对应的cfg寄存器是pmpcfg0，pmpcfg2，pmpcfg4... */
	pmpcfg_csr   = (CSR_PMPCFG0 + (reg_idx >> 2)) & ~1;
	pmpcfg_shift = (reg_idx & 7) << 3;

	pmpaddr_csr = CSR_PMPADDR0 + reg_idx;

	/* 配置cfg中的A字段，NA4表示只有4bytes的区域 */
	prot &= ~PMP_A;
	prot |= (order == PMP_SHIFT) ? PMP_A_NA4 : PMP_A_NAPOT;

	/* 配置cfg中的prot */
	cfgmask = ~(0xffUL << pmpcfg_shift);
	pmpcfg	= (read_csr_num(pmpcfg_csr) & cfgmask);
	pmpcfg |= ((prot << pmpcfg_shift) & ~cfgmask);

	/* 
	 * 配置PMP address
	 * 当oder == 2时，A使用PMP_A_NA4, pmpaddr直接使用start>>2
	 * 当oder > 2时，A使用PMP_A_NAPOT，需要重新配置pmpaddr
	 */
	if (order > PMP_SHIFT)
	{
		if (order == RISCV_XLEN) {
			pmpaddr = -1UL;
		} else {
			/*
			 * 若pmpaddr值为y...y01...1，设连续1的个数为n,
			 * 则该PMP entry所控制的地址空间为从y...y00...0开始的2^{n+3}个字节
			 * 参考RSIC-V手册
			 */ 
			addrmask = (1UL << (order - PMP_SHIFT)) - 1;
			pmpaddr	 &= ~addrmask;
			pmpaddr |= (addrmask >> 1);
		}
	}

	printk("%s: pmpaddr: 0x%lx  pmpcfg 0x%lx, cfs_csr 0x%x addr_csr 0x%x\n",
			__func__, pmpaddr, pmpcfg, pmpcfg_csr, pmpaddr_csr);

	/* 写CSR寄存器 */
	write_csr_num(pmpaddr_csr, pmpaddr);
	write_csr_num(pmpcfg_csr, pmpcfg);

	return 0;
}

#ifndef SBI_PMP_UNIT_TEST
static int check_h_extension(void)
{
	return read_csr(misa) & (1 << 7);
}

/*
 * 运行在M模式
 */
void sbi_main(void)
{
	unsigned long val;

	uart_init();

	init_printk_done(putchar);
	printk(BANNER);

	sbi_trap_init();

	/*
	 * Cold-start timer initialization: establish a deterministic, silent
	 * "no deadline" timer-service readiness state before the supervisor
	 * handoff.  This does not program the first periodic deadline; the
	 * post-handoff service path (S-mode timer_init -> sbi_set_timer -> ecall
	 * -> clint_timer_event_start) does that.  Placed after trap init and
	 * before PMP configuration / mstatus setup / mret.
	 */
	sbi_timer_init();

	/*
	 * 配置PMP
	 * 默认布局保留当前固件行为。corrected 布局先安装固件区间 deny
	 * entry，再安装低优先级 allow-all entry。
	 */
#ifdef CONFIG_PMP_LAYOUT_CORRECTED
	printk("PMP layout: corrected deny-first firmware region\n");
	sbi_set_pmp(0, FW_PROTECT_BASE, FW_PROTECT_SIZE, 0);
	sbi_set_pmp(1, 0, -1UL, PMP_RWX);
#else
	printk("PMP layout: current allow-all first\n");
	sbi_set_pmp(0, 0, -1UL, PMP_RWX);
	sbi_set_pmp(1, FW_PROTECT_BASE, FW_PROTECT_SIZE, PMP_RWX);
#endif
	printk("PMP CSR snapshot: pmpcfg0=0x%lx pmpaddr0=0x%lx pmpaddr1=0x%lx\n",
			read_csr_num(CSR_PMPCFG0),
			read_csr_num(CSR_PMPADDR0),
			read_csr_num(CSR_PMPADDR1));

	printk("H extension %s\n", check_h_extension() ? "implemented" : "not implemented");

	/* 设置跳转模式为S模式 */
	val = read_csr(mstatus);
	val = INSERT_FIELD(val, MSTATUS_MPP, PRV_S);
	val |= MSTATUS_MPIE;
	write_csr(mstatus, val);

	delegate_traps();

	/* 设置M模式的Exception Program Counter，用于mret跳转 */
	write_csr(mepc, FW_JUMP_ADDR);
	/* 设置S模式异常向量表入口*/
	write_csr(stvec, FW_JUMP_ADDR);
	/* 关闭S模式的中断*/
	write_csr(sie, 0);
	/* 关闭S模式的页表转换 */
	write_csr(satp, 0);

	/* 切换到S模式 */
	asm volatile("mret");
}
#endif
