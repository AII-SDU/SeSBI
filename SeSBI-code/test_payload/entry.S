    .section .text.entry, "ax", @progbits
    .balign 4
    .globl _start
    .type _start, @function
_start:
    la sp, payload_stack_top
    call payload_main

.Lpayload_idle:
    wfi
    j .Lpayload_idle

    .size _start, . - _start

    .section .bss.stack, "aw", @nobits
    .balign 16
payload_stack:
    .skip 4096
payload_stack_top:
