#!/bin/bash
# verify.sh - 验证所有 Dafny 文件

set -e

echo "=========================================="
echo "Ras-Sse-Verify: RISC-V SBI RAS/SSE 形式化验证"
echo "=========================================="

# 检查 Dafny 是否安装
if ! command -v dafny &> /dev/null; then
    echo "错误: Dafny 未安装"
    echo "请安装 Dafny: https://github.com/dafny-lang/dafny/releases"
    echo "或使用: dotnet tool install --global dafny"
    exit 1
fi

echo ""
echo "Dafny 版本:"
dafny --version
echo ""

# 验证规格文件
echo "=========================================="
echo "[1/3] 验证规格文件: RasSseSpecRefined.dfy"
echo "=========================================="
dafny verify --cores:4 RasSseSpecRefined.dfy
echo ""

# 验证证明文件
echo "=========================================="
echo "[2/3] 验证证明文件: RasSseProofs.dfy"
echo "=========================================="
dafny verify --cores:4 RasSseProofs.dfy
echo ""

# 验证测试文件
echo "=========================================="
echo "[3/3] 验证测试文件: RasSseTests.dfy"
echo "=========================================="
dafny verify --cores:4 RasSseTests.dfy
echo ""

echo "=========================================="
echo "所有验证完成!"
echo "=========================================="
