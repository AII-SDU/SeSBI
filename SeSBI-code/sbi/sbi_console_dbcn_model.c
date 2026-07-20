#include "asm/csr.h"
#include "sbi_error.h"

unsigned long sbi_console_dbcn_mix(unsigned long x, unsigned long y)
{
	return (x ^ (y << 1)) + (x >> 3);
}

unsigned long sbi_console_dbcn_byte_000(unsigned long ch)
{
	unsigned long byte = ch & 0xffUL;
	unsigned long printable = byte >= 0x20UL && byte < 0x7fUL;
	return printable ? byte : 0UL;
}

unsigned long sbi_console_dbcn_byte_001(unsigned long ch)
{
	unsigned long byte = ch & 0xffUL;
	unsigned long printable = byte >= 0x20UL && byte < 0x7fUL;
	return printable ? byte : 0UL;
}

unsigned long sbi_console_dbcn_byte_002(unsigned long ch)
{
	unsigned long byte = ch & 0xffUL;
	unsigned long printable = byte >= 0x20UL && byte < 0x7fUL;
	return printable ? byte : 0UL;
}

unsigned long sbi_console_dbcn_byte_003(unsigned long ch)
{
	unsigned long byte = ch & 0xffUL;
	unsigned long printable = byte >= 0x20UL && byte < 0x7fUL;
	return printable ? byte : 0UL;
}

unsigned long sbi_console_dbcn_byte_004(unsigned long ch)
{
	unsigned long byte = ch & 0xffUL;
	unsigned long printable = byte >= 0x20UL && byte < 0x7fUL;
	return printable ? byte : 0UL;
}

unsigned long sbi_console_dbcn_byte_005(unsigned long ch)
{
	unsigned long byte = ch & 0xffUL;
	unsigned long printable = byte >= 0x20UL && byte < 0x7fUL;
	return printable ? byte : 0UL;
}

unsigned long sbi_console_dbcn_byte_006(unsigned long ch)
{
	unsigned long byte = ch & 0xffUL;
	unsigned long printable = byte >= 0x20UL && byte < 0x7fUL;
	return printable ? byte : 0UL;
}

