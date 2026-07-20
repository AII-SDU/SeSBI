GNU ?= riscv64-linux-gnu
QEMU ?= qemu-system-riscv64
V ?= 0
PMP_LAYOUT ?= current
SBI3_SMOKE ?= 0

ARCH_FLAGS := -march=rv64imafd -mabi=lp64 -mcmodel=medany \
	-mstrict-align -mno-relax -msmall-data-limit=0
COMMON_CPPFLAGS := -Iinclude -Isbi
COMMON_CFLAGS := $(ARCH_FLAGS) -std=gnu11 -g -O0 -Wall -Wextra \
	-ffreestanding -fno-builtin -fno-common -fno-pic -fno-pie \
	-fno-stack-protector -fno-unwind-tables -fno-asynchronous-unwind-tables \
	-fdebug-prefix-map=$(CURDIR)=. -ffile-prefix-map=$(CURDIR)=.
COMMON_ASFLAGS := $(ARCH_FLAGS) -D__ASSEMBLY__

ifeq ($(PMP_LAYOUT),corrected)
COMMON_CPPFLAGS += -DCONFIG_PMP_LAYOUT_CORRECTED=1
else ifneq ($(PMP_LAYOUT),current)
$(error PMP_LAYOUT must be current or corrected)
endif

ifeq ($(V),1)
Q :=
else
Q := @
endif

BUILD_ROOT := build
FW_BUILD_DIR := $(BUILD_ROOT)/firmware
PAYLOAD_BUILD_DIR := $(BUILD_ROOT)/test-payload
SUPPORT_BUILD_DIR := $(BUILD_ROOT)/support

FW_C_SRCS := $(wildcard sbi/*.c)
FW_ASM_SRCS := $(filter-out sbi/sbi_boot.S sbi/sbi_payload.S,$(wildcard sbi/*.S))
FW_C_OBJS := $(patsubst sbi/%.c,$(FW_BUILD_DIR)/%_c.o,$(FW_C_SRCS))
FW_ASM_OBJS := $(patsubst sbi/%.S,$(FW_BUILD_DIR)/%_s.o,$(FW_ASM_SRCS))
FW_SUPPORT_OBJS := $(SUPPORT_BUILD_DIR)/printk_c.o
FW_OBJS := $(FW_C_OBJS) $(FW_ASM_OBJS) $(FW_SUPPORT_OBJS)
FW_ELF := $(FW_BUILD_DIR)/sesbi-fw.elf
FW_MAP := $(FW_BUILD_DIR)/sesbi-fw.map

PAYLOAD_C_SRCS := test_payload/main.c
PAYLOAD_ASM_SRCS := test_payload/entry.S
PAYLOAD_C_OBJS := $(patsubst test_payload/%.c,$(PAYLOAD_BUILD_DIR)/%_c.o,$(PAYLOAD_C_SRCS))
PAYLOAD_ASM_OBJS := $(patsubst test_payload/%.S,$(PAYLOAD_BUILD_DIR)/%_s.o,$(PAYLOAD_ASM_SRCS))
PAYLOAD_OBJS := $(PAYLOAD_C_OBJS) $(PAYLOAD_ASM_OBJS)
PAYLOAD_ELF := $(PAYLOAD_BUILD_DIR)/sesbi-test-payload.elf
PAYLOAD_MAP := $(PAYLOAD_BUILD_DIR)/sesbi-test-payload.map

ifeq ($(SBI3_SMOKE),1)
PAYLOAD_CPPFLAGS := -DSESBI_EXTENSION_SMOKE=1
else
PAYLOAD_CPPFLAGS :=
endif

.DEFAULT_GOAL := all
.PHONY: all clean firmware test-payload run debug

all:
	$(Q)$(MAKE) --no-print-directory clean
	$(Q)$(MAKE) --no-print-directory firmware test-payload

firmware: sesbi-fw.elf sesbi-fw.bin sesbi-fw.map

test-payload: sesbi-test-payload.elf sesbi-test-payload.bin sesbi-test-payload.map

$(FW_BUILD_DIR)/%_c.o: sbi/%.c
	$(Q)mkdir -p $(@D)
	$(Q)echo " CC  $@"
	$(Q)$(GNU)-gcc $(COMMON_CPPFLAGS) $(COMMON_CFLAGS) -c $< -o $@

$(FW_BUILD_DIR)/%_s.o: sbi/%.S
	$(Q)mkdir -p $(@D)
	$(Q)echo " AS  $@"
	$(Q)$(GNU)-gcc $(COMMON_CPPFLAGS) $(COMMON_ASFLAGS) -c $< -o $@

$(SUPPORT_BUILD_DIR)/printk_c.o: support/printk.c include/printk.h
	$(Q)mkdir -p $(@D)
	$(Q)echo " CC  $@"
	$(Q)$(GNU)-gcc $(COMMON_CPPFLAGS) $(COMMON_CFLAGS) -c $< -o $@

$(FW_ELF): sbi/sbi_linker.ld sbi/sbi_base.ld $(FW_OBJS)
	$(Q)echo " LD  $@"
	$(Q)$(GNU)-ld --fatal-warnings --build-id=none \
		-T sbi/sbi_linker.ld -Map=$(FW_MAP) -o $@ $(FW_OBJS)

sesbi-fw.elf: $(FW_ELF)
	$(Q)cp $< $@

sesbi-fw.bin: $(FW_ELF)
	$(Q)$(GNU)-objcopy $< -O binary $@
	$(Q)echo " OBJCOPY $@"

sesbi-fw.map: $(FW_ELF)
	$(Q)cp $(FW_MAP) $@

$(PAYLOAD_BUILD_DIR)/%_c.o: test_payload/%.c
	$(Q)mkdir -p $(@D)
	$(Q)echo " CC  $@"
	$(Q)$(GNU)-gcc $(PAYLOAD_CPPFLAGS) $(COMMON_CFLAGS) -c $< -o $@

$(PAYLOAD_BUILD_DIR)/%_s.o: test_payload/%.S
	$(Q)mkdir -p $(@D)
	$(Q)echo " AS  $@"
	$(Q)$(GNU)-gcc $(COMMON_ASFLAGS) -c $< -o $@

$(PAYLOAD_ELF): test_payload/linker.ld $(PAYLOAD_OBJS)
	$(Q)echo " LD  $@"
	$(Q)$(GNU)-ld --fatal-warnings --build-id=none \
		-T test_payload/linker.ld -Map=$(PAYLOAD_MAP) -o $@ $(PAYLOAD_OBJS)

sesbi-test-payload.elf: $(PAYLOAD_ELF)
	$(Q)cp $< $@

sesbi-test-payload.bin: $(PAYLOAD_ELF)
	$(Q)$(GNU)-objcopy $< -O binary $@
	$(Q)echo " OBJCOPY $@"

sesbi-test-payload.map: $(PAYLOAD_ELF)
	$(Q)cp $(PAYLOAD_MAP) $@

run: all
	$(Q)$(QEMU) -nographic -machine virt -m 128M \
		-bios sesbi-fw.bin \
		-device loader,file=sesbi-test-payload.bin,addr=0x80200000

debug: all
	$(Q)$(QEMU) -nographic -machine virt -m 128M \
		-bios sesbi-fw.bin \
		-device loader,file=sesbi-test-payload.bin,addr=0x80200000 -S -s

clean:
	$(Q)rm -rf $(BUILD_ROOT) .tmp_* *.bin *.elf *.map
