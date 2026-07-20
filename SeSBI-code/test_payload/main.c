/*
 * Minimal S-mode probe for the SeSBI artifact.
 *
 * The payload confirms that the firmware reaches supervisor mode, that the
 * selected PMP baseline permits the distinguishing load used by the concrete
 * experiments, and, when requested, that the advertised SBI extensions are
 * discoverable.  It is a bounded test payload, not an operating system.
 */

typedef unsigned long payload_u64;
typedef signed long payload_s64;

#define SBI_LEGACY_PUTCHAR 0x1UL
#define SBI_EXT_BASE       0x10UL
#define SBI_EXT_TIME       0x54494d45UL
#define SBI_EXT_DBCN       0x4442434eUL
#define SBI_EXT_IPI        0x735049UL
#define SBI_EXT_RFENCE     0x52464e43UL
#define SBI_EXT_HSM        0x48534dUL
#define SBI_EXT_SRST       0x53525354UL
#define SBI_EXT_PMU        0x504d55UL

#define SBI_BASE_GET_SPEC_VERSION 0UL
#define SBI_BASE_PROBE_EXTENSION  3UL
#define SBI_DBCN_WRITE_BYTE       2UL
#define SBI_IPI_SEND              0UL
#define SBI_RFENCE_REMOTE_FENCE_I 0UL
#define SBI_HSM_GET_STATUS        2UL

struct payload_sbiret {
	payload_s64 error;
	payload_u64 value;
};

static struct payload_sbiret payload_sbi_call(payload_u64 eid,
		payload_u64 fid, payload_u64 arg0, payload_u64 arg1,
		payload_u64 arg2)
{
	register payload_u64 a0 __asm__("a0") = arg0;
	register payload_u64 a1 __asm__("a1") = arg1;
	register payload_u64 a2 __asm__("a2") = arg2;
	register payload_u64 a6 __asm__("a6") = fid;
	register payload_u64 a7 __asm__("a7") = eid;

	__asm__ volatile ("ecall"
			  : "+r"(a0), "+r"(a1)
			  : "r"(a2), "r"(a6), "r"(a7)
			  : "memory");
	return (struct payload_sbiret){
		.error = (payload_s64)a0,
		.value = a1
	};
}

static void payload_putchar(char ch)
{
	(void)payload_sbi_call(SBI_LEGACY_PUTCHAR, 0, (payload_u64)ch, 0, 0);
}

static void payload_puts(const char *text)
{
	while (*text)
		payload_putchar(*text++);
}

#ifdef SESBI_EXTENSION_SMOKE
static void payload_print_hex(payload_u64 value)
{
	static const char digits[] = "0123456789abcdef";
	char reversed[16];
	unsigned int count = 0;

	do {
		reversed[count++] = digits[value & 0xfUL];
		value >>= 4;
	} while (value != 0);
	while (count != 0)
		payload_putchar(reversed[--count]);
}

static void payload_print_unsigned(payload_u64 value)
{
	char reversed[20];
	unsigned int count = 0;

	do {
		reversed[count++] = (char)('0' + value % 10UL);
		value /= 10UL;
	} while (value != 0);
	while (count != 0)
		payload_putchar(reversed[--count]);
}

static void payload_print_signed(payload_s64 value)
{
	payload_u64 magnitude;

	if (value < 0) {
		payload_putchar('-');
		magnitude = 0UL - (payload_u64)value;
	} else {
		magnitude = (payload_u64)value;
	}
	payload_print_unsigned(magnitude);
}

static void payload_print_result(const char *name,
		struct payload_sbiret result)
{
	payload_puts(name);
	payload_puts(": error=");
	payload_print_signed(result.error);
	payload_puts(" value=0x");
	payload_print_hex(result.value);
	payload_putchar('\n');
}

static void payload_probe_extension(const char *label, payload_u64 eid)
{
	struct payload_sbiret result = payload_sbi_call(
		SBI_EXT_BASE, SBI_BASE_PROBE_EXTENSION, eid, 0, 0);

	payload_puts("probe ");
	payload_puts(label);
	payload_puts(" eid=0x");
	payload_print_hex(eid);
	payload_puts(" error=");
	payload_print_signed(result.error);
	payload_puts(" value=");
	payload_print_unsigned(result.value);
	payload_putchar('\n');
}

static void payload_extension_smoke(void)
{
	payload_puts("SBI3 smoke begin\n");
	payload_print_result("get_spec_version",
		payload_sbi_call(SBI_EXT_BASE, SBI_BASE_GET_SPEC_VERSION,
				 0, 0, 0));
	payload_probe_extension("BASE ", SBI_EXT_BASE);
	payload_probe_extension("TIME ", SBI_EXT_TIME);
	payload_probe_extension("DBCN ", SBI_EXT_DBCN);
	payload_probe_extension("IPI  ", SBI_EXT_IPI);
	payload_probe_extension("RFNC ", SBI_EXT_RFENCE);
	payload_probe_extension("HSM  ", SBI_EXT_HSM);
	payload_probe_extension("SRST ", SBI_EXT_SRST);
	payload_probe_extension("PMU  ", SBI_EXT_PMU);

	payload_print_result("dbcn_write_byte",
		payload_sbi_call(SBI_EXT_DBCN, SBI_DBCN_WRITE_BYTE,
				 (payload_u64)'>', 0, 0));
	payload_print_result("send_ipi_empty_mask",
		payload_sbi_call(SBI_EXT_IPI, SBI_IPI_SEND, 0, 0, 0));
	payload_print_result("remote_fence_i_empty_mask",
		payload_sbi_call(SBI_EXT_RFENCE, SBI_RFENCE_REMOTE_FENCE_I,
				 0, 0, 0));
	payload_print_result("hart_get_status_0",
		payload_sbi_call(SBI_EXT_HSM, SBI_HSM_GET_STATUS, 0, 0, 0));
	payload_puts("SBI3 smoke end\n");
}
#endif

void payload_main(void)
{
	volatile payload_u64 *probe = (volatile payload_u64 *)0x80000000UL;
	volatile payload_u64 observed;

	payload_puts("SeSBI S-mode test payload\n");
#ifdef SESBI_EXTENSION_SMOKE
	payload_extension_smoke();
#endif
	observed = *probe;
	(void)observed;
	payload_puts("SeSBI PMP probe: load succeeded\n");

	for (;;)
		__asm__ volatile ("wfi");
}
