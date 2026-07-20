#!/usr/bin/env bash
# Method B (integration): does an end-to-end Linux boot on OpenSBI notice a
# silently-misconfigured PMP region (NAPOT off-by-one)?  We instrument
# sbi_pmp_encode to print the requested log2len and the resulting pmp->addr,
# then boot real Linux both clean and with the NAPOT bug injected.
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
SRC="${OPENSBI_DIR:-${ROOT}/opensbi_upstream}"
LOG="${LOG_DIR:-${ROOT}/logs}"
IMG="${LINUX_IMAGE:-}"
QEMU_BIN="${QEMU_BIN:-qemu-system-riscv64}"
MAKE_BIN="${MAKE_BIN:-make}"
GIT_BIN="${GIT_BIN:-git}"
TIMEOUT_BIN="${TIMEOUT_BIN:-timeout}"
export CROSS_COMPILE="${CROSS_COMPILE:-riscv64-linux-gnu-}"

[ -d "${SRC}" ] || { echo "[FATAL] OpenSBI directory not found: ${SRC}" >&2; exit 2; }
[ -n "${IMG}" ] || { echo "[FATAL] set LINUX_IMAGE to a bootable RISC-V Linux Image" >&2; exit 2; }
[ -f "${IMG}" ] || { echo "[FATAL] Linux image not found: ${IMG}" >&2; exit 2; }
for tool in "${QEMU_BIN}" "${MAKE_BIN}" "${GIT_BIN}" "${TIMEOUT_BIN}" "${CROSS_COMPILE}gcc"; do
  command -v "${tool}" >/dev/null 2>&1 || { echo "[FATAL] required command not found: ${tool}" >&2; exit 2; }
done
mkdir -p "${LOG}"
cd "$SRC"
BIN=build/platform/generic/firmware/fw_dynamic.bin
PMP=lib/sbi/sbi_pmp.c

instrument () {
  # insert a print right after the NAPOT encode line (pmp->addr |= (addrmask >> 1);)
  perl -0pi -e 's{(pmp->addr \|= \(addrmask >> 1\);)}{$1\n\t\t\tsbi_printf("PMPENC log2len=%lu addr=0x%lx pmpaddr=0x%lx\\n", log2len, addr, pmp->addr);}' "$PMP"
}
inject_napot () {
  perl -0pi -e 's{pmp->addr \|= \(addrmask >> 1\);}{pmp->addr |= addrmask; /*MUT-NAPOT*/}' "$PMP"
}

boot () {  # $1 = tag
  "${MAKE_BIN}" -j"${JOBS:-8}" PLATFORM=generic >"$LOG/int_$1.build.log" 2>&1
  if [ $? -ne 0 ]; then echo "$1: BUILD FAILED"; return; fi
  "${TIMEOUT_BIN}" "${BOOT_TIMEOUT_SECONDS:-50}" "${QEMU_BIN}" -M virt -m 512M -smp 1 -nographic \
    -bios "$BIN" -kernel "$IMG" -append "console=ttyS0" \
    > "$LOG/int_$1.boot.log" 2>&1
  local panic booted pmpenc
  panic=$(grep -ic "kernel panic\|Oops\|unable to handle\|trap" "$LOG/int_$1.boot.log")
  booted=$(grep -ic "Linux version\|Freeing unused\|Run /init\|Mounting\|VFS:" "$LOG/int_$1.boot.log")
  pmpenc=$(grep -c "PMPENC" "$LOG/int_$1.boot.log")
  echo "$1: pmpenc_prints=$pmpenc linux_progress=$booted panic_markers=$panic"
}

echo "===== CLEAN (instrumented, no bug) ====="
"${GIT_BIN}" checkout -- "$PMP" 2>/dev/null
instrument
boot clean
echo "--- clean PMPENC lines ---"; grep "PMPENC" "$LOG/int_clean.boot.log" | head -20

echo "===== NAPOT BUG (instrumented + injected) ====="
"${GIT_BIN}" checkout -- "$PMP" 2>/dev/null
instrument
inject_napot
grep -q "MUT-NAPOT" "$PMP" && echo "injected OK" || echo "inject FAILED"
boot napot
echo "--- napot PMPENC lines ---"; grep "PMPENC" "$LOG/int_napot.boot.log" | head -20

"${GIT_BIN}" checkout -- "$PMP" 2>/dev/null
echo "restored; done"
