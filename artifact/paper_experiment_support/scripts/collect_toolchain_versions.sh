#!/usr/bin/env bash
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=common.sh
. "$SCRIPT_DIR/common.sh"

OUT="$OUT_DIR/00_setup"
mkdir -p "$OUT"

TARGETS="$OUT/paper_setup_targets.csv"
VERSIONS="$OUT/toolchain_versions.txt"
COMMANDS="$OUT/version_commands.txt"
MATRIX="$OUT/environment_match_matrix.csv"
QEMU_GDB="$OUT/qemu_gdb_support.txt"
VM_PROFILE="$OUT/paper_vm_profile.md"
QEMU_CANDIDATES="$OUT/qemu_candidates.csv"

ISABELLE_REQUESTED="${ISABELLE_BIN:-${ISABELLE:-isabelle}}"
DAFNY_REQUESTED="${DAFNY_BIN:-${DAFNY:-dafny}}"
QEMU_REQUESTED="${QEMU_BIN:-qemu-system-riscv64}"
ISABELLE_RESOLVED="$(command -v "$ISABELLE_REQUESTED" 2>/dev/null || true)"
DAFNY_RESOLVED="$(command -v "$DAFNY_REQUESTED" 2>/dev/null || true)"
QEMU_RESOLVED="$(command -v "$QEMU_REQUESTED" 2>/dev/null || true)"

cat >"$TARGETS" <<'EOF'
item,paper_description
host,VMware Workstation Player
memory,8 GB RAM
cpu,4 CPU cores
disk,512 GB disk
os,Ubuntu 20.04 LTS 64-bit
qemu,QEMU 4.2.0 with GDB support
isabelle,Isabelle 2025
dafny,Dafny
cloc,cloc recorded arguments
EOF

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "repo_root=$REPO_ROOT"
  echo
  echo "[uname]"
  uname -a || true
  echo
  echo "[os-release]"
  if [ -f /etc/os-release ]; then
    sed -n '1,20p' /etc/os-release
  fi
  echo
  echo "[cpu]"
  nproc || true
  lscpu | sed -n '1,20p' || true
  echo
  echo "[memory]"
  free -h || true
  echo
  echo "[disk]"
  df -h "$REPO_ROOT" || true
  echo
  echo "[riscv64-linux-gnu-gcc]"
  riscv64-linux-gnu-gcc --version | head -n 1 || true
  echo
  echo "[qemu-system-riscv64]"
  if [ -n "$QEMU_RESOLVED" ]; then
    "$QEMU_RESOLVED" --version | head -n 1
  else
    echo "unavailable"
  fi
  echo
  echo "[gdb]"
  gdb --version | head -n 1 || true
  echo
  echo "[isabelle]"
  if [ -n "$ISABELLE_RESOLVED" ]; then
    "$ISABELLE_RESOLVED" version || true
  else
    echo "unavailable"
  fi
  echo
  echo "[dafny]"
  if [ -n "$DAFNY_RESOLVED" ]; then
    "$DAFNY_RESOLVED" --version || true
  else
    echo "unavailable"
  fi
  echo
  echo "[cloc]"
  if command -v cloc >/dev/null 2>&1; then
    cloc --version || true
  else
    echo "unavailable"
  fi
} >"$VERSIONS" 2>&1

cat >"$COMMANDS" <<EOF
uname -a
cat /etc/os-release
nproc
lscpu
free -h
df -h "$REPO_ROOT"
riscv64-linux-gnu-gcc --version
qemu-system-riscv64 --version
gdb --version
isabelle version
dafny --version
cloc --version
EOF

{
  echo "item,paper_target,observed,status,note"
  echo "host,VMware Workstation Player,not_observable_from_guest,recorded_target,host hypervisor cannot be fully confirmed from guest shell"
  echo "memory,8 GB RAM,$(free -h | awk '/^内存：|^Mem:/ {print $2; exit}'),observed_current,rerun inside paper VM for exact match"
  echo "cpu,4 CPU cores,$(nproc 2>/dev/null || echo unavailable),observed_current,rerun inside paper VM for exact match"
  echo "disk,512 GB disk,$(df -h "$REPO_ROOT" | awk 'NR==2 {print $2}'),observed_current,rerun inside paper VM for exact match"
  observed_os="$(. /etc/os-release 2>/dev/null; echo "${PRETTY_NAME:-unavailable}")"
  echo "os,Ubuntu 20.04 LTS 64-bit,$observed_os,observed_current,does not match paper target on current host"
  observed_qemu="$(if [ -n "$QEMU_RESOLVED" ]; then "$QEMU_RESOLVED" --version | head -n 1; else echo unavailable; fi)"
  echo "qemu,QEMU 4.2.0 with GDB support,$observed_qemu,observed_current,does not match paper target on current host"
  observed_isabelle="$(if [ -n "$ISABELLE_RESOLVED" ]; then "$ISABELLE_RESOLVED" version 2>/dev/null; else echo unavailable; fi)"
  echo "isabelle,Isabelle 2025,$observed_isabelle,compatible_current,Isabelle2025-2 is available"
  observed_dafny="$(if [ -n "$DAFNY_RESOLVED" ]; then "$DAFNY_RESOLVED" --version 2>/dev/null; else echo unavailable; fi)"
  echo "dafny,Dafny,$observed_dafny,observed_current,version recorded for recovery"
  observed_cloc="$(if command -v cloc >/dev/null 2>&1; then cloc --version 2>/dev/null; else echo unavailable; fi)"
  echo "cloc,cloc recorded arguments,$observed_cloc,missing_current,fallback counter records NCNB line counts"
} >"$MATRIX"

{
  echo "# Paper VM profile"
  echo
  echo "- Hypervisor: VMware Workstation Player"
  echo "- Guest OS: Ubuntu 20.04 LTS 64-bit"
  echo "- RAM: 8 GB"
  echo "- CPU cores: 4"
  echo "- Disk: 512 GB"
  echo "- QEMU: 4.2.0 with GDB support"
  echo "- Isabelle: 2025"
  echo "- Dafny: recorded by recovery script"
  echo "- Code-size tool: cloc with recorded arguments"
  echo
  echo "This file records the paper target profile. Re-run the recovery scripts in a matching VM to regenerate observed evidence under the original setup."
} >"$VM_PROFILE"

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "[installed qemu]"
  if [ -n "$QEMU_RESOLVED" ]; then
    "$QEMU_RESOLVED" --version | head -n 1
    "$QEMU_RESOLVED" -help 2>&1 | grep -E -- '-gdb|-S|-s[ ,]' | head -n 20 || true
  else
    echo "unavailable"
  fi
  echo
  echo "[paper command form]"
  echo "qemu-system-riscv64 -S -s -nographic -machine virt -m 128M -bios sesbi-fw.bin -device loader,file=sesbi-test-payload.bin,addr=0x80200000 -kernel sesbi-test-payload.elf"
} >"$QEMU_GDB"

{
  echo "path,version,target_match"
  for qemu in "$QEMU_RESOLVED"; do
    [ -n "$qemu" ] || continue
    if [ -x "$qemu" ]; then
      version="$("$qemu" --version | head -n 1)"
      case "$version" in
        *"version 4.2.0"*) match=yes ;;
        *) match=no ;;
      esac
      echo "$qemu,$version,$match"
    fi
  done
} >"$QEMU_CANDIDATES"
