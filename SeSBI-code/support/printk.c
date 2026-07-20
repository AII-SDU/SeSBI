/*
 * Minimal firmware formatter for the SeSBI artifact.
 *
 * This implementation is intentionally small and independent.  It supports
 * only the conversion forms used by the firmware: c, s, d, u, x, X, p, and
 * percent, with optional zero padding, field width, and l/ll length markers.
 */

#include <stdarg.h>

#include "printk.h"

static void (*console_put)(char);

void init_printk_done(void (*fn)(char))
{
	console_put = fn;
}

static void emit_char(char ch)
{
	if (console_put)
		console_put(ch);
}

static int emit_string(const char *text)
{
	int count = 0;

	if (!text)
		text = "(null)";
	while (*text) {
		emit_char(*text++);
		count++;
	}
	return count;
}

static int emit_unsigned(unsigned long value, unsigned int base,
			 int uppercase, unsigned int width, char padding)
{
	const char *digits = uppercase ? "0123456789ABCDEF" :
					 "0123456789abcdef";
	char reversed[2 * sizeof(unsigned long) + 1];
	unsigned int length = 0;
	int count = 0;

	do {
		reversed[length++] = digits[value % base];
		value /= base;
	} while (value != 0);

	while (width > length) {
		emit_char(padding);
		width--;
		count++;
	}
	while (length != 0) {
		emit_char(reversed[--length]);
		count++;
	}
	return count;
}

static int emit_signed(long value, unsigned int width, char padding)
{
	unsigned long magnitude;
	int count = 0;

	if (value < 0) {
		emit_char('-');
		count++;
		if (width != 0)
			width--;
		magnitude = 0UL - (unsigned long)value;
	} else {
		magnitude = (unsigned long)value;
	}
	return count + emit_unsigned(magnitude, 10, 0, width, padding);
}

int printk(const char *format, ...)
{
	va_list arguments;
	int count = 0;

	va_start(arguments, format);
	while (*format) {
		unsigned int width = 0;
		int long_count = 0;
		char padding = ' ';
		char conversion;

		if (*format != '%') {
			emit_char(*format++);
			count++;
			continue;
		}
		format++;
		if (*format == '%') {
			emit_char(*format++);
			count++;
			continue;
		}
		if (*format == '0') {
			padding = '0';
			format++;
		}
		while (*format >= '0' && *format <= '9') {
			width = width * 10U + (unsigned int)(*format - '0');
			format++;
		}
		while (*format == 'l') {
			long_count++;
			format++;
		}
		conversion = *format ? *format++ : '\0';
		switch (conversion) {
		case 'c':
			emit_char((char)va_arg(arguments, int));
			count++;
			break;
		case 's':
			count += emit_string(va_arg(arguments, const char *));
			break;
		case 'd':
		case 'i':
			if (long_count)
				count += emit_signed(va_arg(arguments, long), width,
						     padding);
			else
				count += emit_signed((long)va_arg(arguments, int),
						     width, padding);
			break;
		case 'u':
			if (long_count)
				count += emit_unsigned(va_arg(arguments, unsigned long),
						       10, 0, width, padding);
			else
				count += emit_unsigned(
					(unsigned long)va_arg(arguments, unsigned int),
					10, 0, width, padding);
			break;
		case 'x':
		case 'X':
			if (long_count)
				count += emit_unsigned(va_arg(arguments, unsigned long),
						       16, conversion == 'X', width,
						       padding);
			else
				count += emit_unsigned(
					(unsigned long)va_arg(arguments, unsigned int),
					16, conversion == 'X', width, padding);
			break;
		case 'p':
			count += emit_string("0x");
			count += emit_unsigned(
				(unsigned long)va_arg(arguments, void *), 16, 0,
				2U * (unsigned int)sizeof(void *), '0');
			break;
		case '\0':
			format--;
			break;
		default:
			emit_char('%');
			emit_char(conversion);
			count += 2;
			break;
		}
	}
	va_end(arguments);
	return count;
}
