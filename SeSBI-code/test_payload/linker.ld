OUTPUT_ARCH(riscv)
ENTRY(_start)

SECTIONS
{
    . = 0x80200000;

    .text : ALIGN(16)
    {
        KEEP(*(.text.entry))
        *(.text .text.*)
    }

    .rodata : ALIGN(16)
    {
        *(.srodata .srodata.*)
        *(.rodata .rodata.*)
    }

    .data : ALIGN(16)
    {
        *(.sdata .sdata.*)
        *(.data .data.*)
    }

    .bss (NOLOAD) : ALIGN(16)
    {
        *(.sbss .sbss.*)
        *(.bss .bss.*)
        *(COMMON)
    }

    /DISCARD/ :
    {
        *(.comment)
        *(.note*)
        *(.eh_frame*)
    }
}
