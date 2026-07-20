#include "sbi_ecall.h"
#include "sbi_trap.h"
#include "sbi_error.h"
#include "uart.h"
#include "io.h"
#include "asm/uart.h"

#define SBI_DBCN_MAX_BYTES 4096UL

void sbi_console_putchar(char ch)
{
	putchar(ch);
}

long sbi_console_getchar(void)
{
	return (long)uart_get();
}

static struct sbiret sbi_dbcn_write(unsigned long num_bytes,
				    unsigned long base_addr_lo,
				    unsigned long base_addr_hi)
{
	const char *buf = (const char *)base_addr_lo;
	unsigned long i;

	if (base_addr_hi != 0)
		return (struct sbiret){ .error = SBI_ERR_INVALID_ADDRESS };

	if (num_bytes > SBI_DBCN_MAX_BYTES)
		num_bytes = SBI_DBCN_MAX_BYTES;

	for (i = 0; i < num_bytes; i++)
		sbi_console_putchar(buf[i]);

	return (struct sbiret){ .error = SBI_SUCCESS, .value = num_bytes };
}

static struct sbiret sbi_dbcn_read(unsigned long num_bytes,
				   unsigned long base_addr_lo,
				   unsigned long base_addr_hi)
{
	char *buf = (char *)base_addr_lo;
	unsigned long i = 0;

	if (base_addr_hi != 0)
		return (struct sbiret){ .error = SBI_ERR_INVALID_ADDRESS };

	if (num_bytes > SBI_DBCN_MAX_BYTES)
		num_bytes = SBI_DBCN_MAX_BYTES;

	while (i < num_bytes && (readb(UART_LSR) & UART_LSR_DR))
		buf[i++] = (char)sbi_console_getchar();

	return (struct sbiret){ .error = SBI_SUCCESS, .value = i };
}

struct sbiret sbi_ecall_dbcn(unsigned long fid, struct sbi_trap_regs *regs)
{
	switch (fid) {
	case SBI_DBCN_CONSOLE_WRITE:
		return sbi_dbcn_write(regs->a0, regs->a1, regs->a2);
	case SBI_DBCN_CONSOLE_READ:
		return sbi_dbcn_read(regs->a0, regs->a1, regs->a2);
	case SBI_DBCN_CONSOLE_WRITE_BYTE:
		sbi_console_putchar((char)(regs->a0 & 0xff));
		return (struct sbiret){ .error = SBI_SUCCESS };
	default:
		return (struct sbiret){ .error = SBI_ERR_NOT_SUPPORTED };
	}
}
