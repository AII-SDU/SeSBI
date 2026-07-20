#ifndef _ASM_RISCV_SBI_H
#define _ASM_RISCV_SBI_H

/*
 * SBI提供timer服务
 */
#define SBI_SET_TIMER 0
#define SBI_CONSOLE_PUTCHAR 0x1
#define SBI_CONSOLE_GETCHAR 0x2
#define SBI_EXIT_VM_TEST 0x100

/* SBI v0.2+ / v3.0 extension IDs used by SeSBI's prototype subset. */
#define SBI_EXT_BASE	0x10
#define SBI_EXT_TIME	0x54494D45
#define SBI_EXT_IPI	0x735049
#define SBI_EXT_RFENCE	0x52464E43
#define SBI_EXT_HSM	0x48534D
#define SBI_EXT_SRST	0x53525354
#define SBI_EXT_DBCN	0x4442434E
#define SBI_EXT_PMU	0x504D55

#define SBI_SPEC_VERSION_MAJOR	3
#define SBI_SPEC_VERSION_MINOR	0
#define SBI_SPEC_VERSION	((SBI_SPEC_VERSION_MAJOR << 24) | SBI_SPEC_VERSION_MINOR)

#define SBI_IMPL_ID_SESBI	0x53455342UL
#define SBI_IMPL_VERSION	0x00010000UL

/* SBI v0.2+ function IDs for the prototype subset. */
#define SBI_BASE_GET_SPEC_VERSION	0
#define SBI_BASE_GET_IMPL_ID		1
#define SBI_BASE_GET_IMPL_VERSION	2
#define SBI_BASE_PROBE_EXTENSION	3
#define SBI_BASE_GET_MVENDORID		4
#define SBI_BASE_GET_MARCHID		5
#define SBI_BASE_GET_MIMPID		6

#define SBI_TIME_SET_TIMER		0

#define SBI_IPI_SEND_IPI		0

#define SBI_RFENCE_REMOTE_FENCE_I		0
#define SBI_RFENCE_REMOTE_SFENCE_VMA		1
#define SBI_RFENCE_REMOTE_SFENCE_VMA_ASID	2
#define SBI_RFENCE_REMOTE_HFENCE_GVMA_VMID	3
#define SBI_RFENCE_REMOTE_HFENCE_GVMA		4
#define SBI_RFENCE_REMOTE_HFENCE_VVMA_ASID	5
#define SBI_RFENCE_REMOTE_HFENCE_VVMA		6

#define SBI_HSM_HART_START		0
#define SBI_HSM_HART_STOP		1
#define SBI_HSM_HART_GET_STATUS		2
#define SBI_HSM_HART_SUSPEND		3

#define SBI_HSM_STATE_STARTED		0

#define SBI_SRST_SYSTEM_RESET		0
#define SBI_SRST_RESET_TYPE_SHUTDOWN	0
#define SBI_SRST_RESET_TYPE_COLD_REBOOT	1
#define SBI_SRST_RESET_TYPE_WARM_REBOOT	2
#define SBI_SRST_RESET_REASON_NONE	0
#define SBI_SRST_RESET_REASON_FAILURE	1

#define SBI_DBCN_CONSOLE_WRITE		0
#define SBI_DBCN_CONSOLE_READ		1
#define SBI_DBCN_CONSOLE_WRITE_BYTE	2

struct sbiret {
	long error;
	unsigned long value;
};

#define SBI_CALL(which, arg0, arg1, arg2) ({			\
	register unsigned long a0 asm ("a0") = (unsigned long)(arg0);	\
	register unsigned long a1 asm ("a1") = (unsigned long)(arg1);	\
	register unsigned long a2 asm ("a2") = (unsigned long)(arg2);	\
	register unsigned long a7 asm ("a7") = (unsigned long)(which);	\
	asm volatile ("ecall"					\
		      : "+r" (a0)				\
		      : "r" (a1), "r" (a2), "r" (a7)		\
		      : "memory");				\
	a0;							\
})

/* 
 * 陷入到M模式，调用M模式提供的服务。
 * SBI运行到M模式下
 */
#define SBI_CALL_0(which) SBI_CALL(which, 0, 0, 0)
#define SBI_CALL_1(which, arg0) SBI_CALL(which, arg0, 0, 0)
#define SBI_CALL_2(which, arg0, arg1) SBI_CALL(which, arg0, arg1, 0)

#define SBI_CALL_6(eid, fid, arg0, arg1, arg2, arg3, arg4, arg5) ({	\
	register unsigned long a0 asm ("a0") = (unsigned long)(arg0);	\
	register unsigned long a1 asm ("a1") = (unsigned long)(arg1);	\
	register unsigned long a2 asm ("a2") = (unsigned long)(arg2);	\
	register unsigned long a3 asm ("a3") = (unsigned long)(arg3);	\
	register unsigned long a4 asm ("a4") = (unsigned long)(arg4);	\
	register unsigned long a5 asm ("a5") = (unsigned long)(arg5);	\
	register unsigned long a6 asm ("a6") = (unsigned long)(fid);	\
	register unsigned long a7 asm ("a7") = (unsigned long)(eid);	\
	asm volatile ("ecall"						\
		      : "+r" (a0), "+r" (a1)				\
		      : "r" (a2), "r" (a3), "r" (a4), "r" (a5),	\
			"r" (a6), "r" (a7)				\
		      : "memory");					\
	(struct sbiret){ .error = (long)a0, .value = a1 };		\
})

#define SBI_CALL_0_V02(eid, fid) \
	SBI_CALL_6(eid, fid, 0, 0, 0, 0, 0, 0)
#define SBI_CALL_1_V02(eid, fid, arg0) \
	SBI_CALL_6(eid, fid, arg0, 0, 0, 0, 0, 0)
#define SBI_CALL_2_V02(eid, fid, arg0, arg1) \
	SBI_CALL_6(eid, fid, arg0, arg1, 0, 0, 0, 0)
#define SBI_CALL_3_V02(eid, fid, arg0, arg1, arg2) \
	SBI_CALL_6(eid, fid, arg0, arg1, arg2, 0, 0, 0)
#define SBI_CALL_4_V02(eid, fid, arg0, arg1, arg2, arg3) \
	SBI_CALL_6(eid, fid, arg0, arg1, arg2, arg3, 0, 0)

static inline void sbi_set_timer(unsigned long stime_value)
{
	SBI_CALL_1(SBI_SET_TIMER, stime_value);
}

static inline struct sbiret sbi_get_spec_version(void)
{
	return SBI_CALL_0_V02(SBI_EXT_BASE, SBI_BASE_GET_SPEC_VERSION);
}

static inline struct sbiret sbi_probe_extension(unsigned long eid)
{
	return SBI_CALL_1_V02(SBI_EXT_BASE, SBI_BASE_PROBE_EXTENSION, eid);
}

static inline struct sbiret sbi_set_timer_v02(unsigned long stime_value)
{
	return SBI_CALL_1_V02(SBI_EXT_TIME, SBI_TIME_SET_TIMER, stime_value);
}

static inline struct sbiret sbi_debug_console_write_byte(unsigned char byte)
{
	return SBI_CALL_1_V02(SBI_EXT_DBCN, SBI_DBCN_CONSOLE_WRITE_BYTE, byte);
}

static inline struct sbiret sbi_debug_console_write(unsigned long num_bytes,
						    unsigned long base_addr)
{
	return SBI_CALL_3_V02(SBI_EXT_DBCN, SBI_DBCN_CONSOLE_WRITE,
			      num_bytes, base_addr, 0);
}

static inline struct sbiret sbi_debug_console_read(unsigned long num_bytes,
						   unsigned long base_addr)
{
	return SBI_CALL_3_V02(SBI_EXT_DBCN, SBI_DBCN_CONSOLE_READ,
			      num_bytes, base_addr, 0);
}

static inline struct sbiret sbi_send_ipi(unsigned long hart_mask,
					 unsigned long hart_mask_base)
{
	return SBI_CALL_2_V02(SBI_EXT_IPI, SBI_IPI_SEND_IPI,
			      hart_mask, hart_mask_base);
}

static inline struct sbiret sbi_remote_fence_i(unsigned long hart_mask,
					       unsigned long hart_mask_base)
{
	return SBI_CALL_2_V02(SBI_EXT_RFENCE, SBI_RFENCE_REMOTE_FENCE_I,
			      hart_mask, hart_mask_base);
}

static inline struct sbiret sbi_remote_sfence_vma(unsigned long hart_mask,
						  unsigned long hart_mask_base,
						  unsigned long start_addr,
						  unsigned long size)
{
	return SBI_CALL_4_V02(SBI_EXT_RFENCE, SBI_RFENCE_REMOTE_SFENCE_VMA,
			      hart_mask, hart_mask_base, start_addr, size);
}

static inline struct sbiret sbi_hart_get_status(unsigned long hartid)
{
	return SBI_CALL_1_V02(SBI_EXT_HSM, SBI_HSM_HART_GET_STATUS, hartid);
}

static inline struct sbiret sbi_system_reset(unsigned long reset_type,
					     unsigned long reset_reason)
{
	return SBI_CALL_2_V02(SBI_EXT_SRST, SBI_SRST_SYSTEM_RESET,
			      reset_type, reset_reason);
}

static inline void sbi_putchar(char c)
{
	SBI_CALL_1(SBI_CONSOLE_PUTCHAR, c);
}

static inline void sbi_put_string(char *str)
{
	int i;

	for (i = 0; str[i] != '\0'; i++)
		sbi_putchar((char) str[i]);
}
#endif /*_ASM_RISCV_SBI_H*/
