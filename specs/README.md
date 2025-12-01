# Ras-Sse-Verify: RISC-V SBI RAS/SSE 形式化验证框架

## 概述

本项目为论文 "Formal Verification for Secure and Dependable RAS Error Handling in RISC-V SBI Firmware" 提供 Dafny 形式化规格和证明。

## 文件结构

```
ras_sse_verify/
├── RasSseSpecRefined.dfy   # 规格定义（数据结构、不变量、操作规格）
├── RasSseProofs.dfy        # 安全属性证明（P1-P4）
├── RasSseTests.dfy         # 测试用例
└── README.md               # 本文档
```

## 安全属性

本框架验证以下四个核心安全属性：

### P1: 前缀保持传输（无丢失、无重复）
- **定义**: `sbi_ras_sync_hart_errs` 的输出和残余队列的多重集并等于原队列
- **证明**: `P1_PrefixPreservingTransfer`, `P1_NoLoss`, `P1_NoDuplication`

### P2: 单次投递
- **定义**: Running 状态的事件 pending 必为 false，防止重复触发
- **证明**: `P2_RunningImpliesNotPending`, `P2_RunningCannotBeInjected`

### P3: 优先级调度
- **定义**: `ProcessPending` 总是选择优先级最高的 pending 事件
- **证明**: `P3_SelectedHasHighestPriority`, `P3_PriorityOrdering`

### P4: Hart 隔离
- **定义**: 被屏蔽的 hart 不处理任何事件；对一个 hart 的操作不影响其他 hart
- **证明**: `P4_MaskingPreventsProcessing`, `P4_OtherHartsUnchanged`

## 核心数据结构

### SSE 事件状态机
```
Unused -> Registered -> Enabled -> Running
                          ^           |
                          |___________|
                         (complete)
```

### 不变量
- `SseEventInv`: Running 状态时 pending 必为 false
- `HartStateInv`: enabled 列表按 (priority, event_id) 排序
- `RasAgentInv`: 注册/探测状态一致性

## 验证方法

### 安装 Dafny
```bash
# 方法 1: 通过 dotnet
dotnet tool install --global dafny

# 方法 2: 下载预编译版本
# https://github.com/dafny-lang/dafny/releases
```

### 运行验证
```bash
# 验证规格
dafny verify RasSseSpecRefined.dfy

# 验证证明
dafny verify RasSseProofs.dfy

# 运行测试
dafny verify RasSseTests.dfy

# 验证所有文件
dafny verify *.dfy
```

### 预期输出
```
Dafny program verifier finished with X verified, 0 errors
```

## 与论文的对应关系

| 论文章节 | Dafny 文件/模块 |
|---------|----------------|
| Section IV-B (状态模型) | `RasSseSpecRefined.dfy` |
| Section IV-C (形式化状态空间) | `SystemState`, `SseEvent`, `HartState`, `RasAgent` |
| Section IV-D (安全属性) | `RasSseProofs.dfy` 中的 `P1_*`, `P2_*`, `P3_*`, `P4_*` |
| Table IV (RAS 函数规格) | `SbiRas*Spec` predicates |
| Table V (SSE 函数规格) | `Sse*Spec` predicates |

## 规格与实现的对应

| Dafny 规格 | OpenSBI/SeSBI-RAS 函数 |
|-----------|----------------------|
| `SbiRasSyncHartErrsSpec` | `sbi_ras_sync_hart_errs()` |
| `SseRegisterSpec` | `sbi_sse_register()` |
| `SseEnableSpec` | `sbi_sse_enable()` |
| `SseInjectSpec` | `sbi_sse_inject_event()` |
| `SseProcessPendingEventsSpec` | `sbi_sse_process_pending_events()` |
| `SseCompleteSpec` | `sbi_sse_complete()` |
| `SseHartMaskSpec` | `sbi_sse_hart_mask()` |

## 已知限制

1. **并发模型**: 当前模型是顺序的，未建模多 hart 并发执行
2. **硬件交互**: RERI 硬件寄存器访问被抽象为队列操作
3. **CPER 生成**: 未建模 CPER 记录的构造细节

## 扩展方向

- 添加并发模型（使用 `{:concurrent}` 注解）
- 细化 CPER 缓冲区管理规格
- 添加 liveness 属性（最终交付保证）

## 参考资料

- [RISC-V RERI Specification](https://github.com/riscv-non-isa/riscv-ras-eri)
- [RISC-V SBI Specification](https://github.com/riscv-non-isa/riscv-sbi-doc)
- [Dafny Documentation](https://dafny.org/latest/DafnyRef/DafnyRef)
