# IR/x86 局部 Lemma 与全局组合验证方案

## 1. 当前实现快照

本仓库当前已经落地的是“程序级符号执行 + observable refinement + 可选 x86 summary 折叠”的验证路径，而不是完整的离线 lemma registry。

当前目标仍然是证明：

```text
对所有输入，x86 AOT 程序的可观察输出精化 EVM IR 程序的可观察输出
```

这里的“可观察输出”由统一的 result / path observation schema 表达：

```text
condition
offset
length
memory
base_addr
has_return_data
storage
transient_storage
```

当前代码中有两条程序级验证路径：

1. `merged-result` 路径：默认路径，把 EVM/x86 所有终止状态分别合并为一个 result dict 后比较。
2. `terminal path observation` 路径：显式设置 `path_observations=True` 时使用，保留 EVM/x86 终止路径，逐个 path pair 比较 observable，避免先合并完整 memory/storage Array。

当前已有的 summary 机制是 x86 侧执行加速框架。内置 summary 目前只有 `CALLDATALOAD`，并且默认关闭，只有调用方显式传入 `TRUSTED_SUMMARY_CONFIG` 才会启用。

当前没有实现：

```text
MUL shape_id
MUL parse_witness
MUL algorithmic lemma cache
通用 proof artifact registry
summary proof status 强制校验
```

因此，旧版文档中关于 `MUL` 的 L1/L2/L3 分层 lemma 仍是后续路线，不是当前能力。

## 2. 程序级验证入口

程序级入口是 `verification/program_verifier.py` 中的 `ProgramEquivalenceChecker.verify_program_pair()`。

调用方提供：

```text
evm_program: EVMProgram
x86_program: X86Program
initial_state: SMTState
stack_check: Optional[int]
path_observations: bool
path_pair_workers: int
enable_merge: bool
skip_feasibility: bool
summary_config: Optional[X86SummaryConfig]
```

### 2.1 默认 merged-result 路径

默认 `path_observations=False`。

流程：

```text
EVMProgram.to_z3(initial_state)
  -> EVM CFG 符号执行
  -> 合并所有 terminal GlobalState
  -> result dict

X86Program.to_z3(initial_state, call_site_mapping, enable_merge, summary_config)
  -> 反汇编并识别 basic blocks
  -> x86 CFG 符号执行
  -> 可选 summary_runtime
  -> 合并所有 terminal X86GlobalState
  -> result dict

RefinementChecker.check_refinement(evm_result, x86_result, assumptions)
```

EVM/x86 执行过程中写入 `SMTState.assumptions` 的前提会被收集、去重，并以顶层 precondition 注入 refinement solver。当前最重要的例子是 `CALLDATALOAD` 的 offset 高 192 位为 0 这一类无损假设。

默认路径适合较小程序或路径合并后公式仍可控的程序。它保留了原来的 Alive2 风格：先构建两个完整终态，再证明输出一致。

### 2.2 terminal path observation 路径

显式 `path_observations=True` 时，程序不会先把完整可观察 Array 合并为一个大终态，而是构造 terminal path observation：

```text
EVMProgram.to_z3_paths(...)
X86Program.to_z3_paths(...)
RefinementChecker.check_refinement_paths(...)
```

`PathObservation` 定义在 `common/path_observation.py`。它是 frozen dataclass，同时提供 `get()`、`__getitem__()` 和 `as_dict()`，因此能被现有 refinement checker 以 dict-like 方式消费。

这条路径当前用于较大的真实样本，例如：

```text
tests/data/perf_erc20_lite.json + .hex
tests/data/muti_block.json + .hex
```

这些测试组合使用：

```text
path_observations=True
path_pair_workers=4
enable_merge=True
summary_config=TRUSTED_SUMMARY_CONFIG
```

`perf_erc20_lite` 还使用 `skip_feasibility=True`，避免符号 calldata 场景下大量 path pair feasibility 预检查消耗预算。

## 3. observable refinement 检查

`verification/refinement_checker.py` 只是薄门面，实际检查拆在三个对象里：

```text
OutputRefinementChecks    -> return data / memory / stack debug
StorageEquivalenceChecks  -> storage / transient storage
PathRefinementChecks      -> terminal path coverage + path pair orchestration
```

三者共享 `_RefinementContext`，使用同一个 timeout/tuning/logging 基础设施和 `QF_AUFBV` solver。

### 3.1 输出比较项

`OutputRefinementChecks._check_refinement_direct_memory_with_solver()` 当前按以下顺序证明没有反例：

1. `has_return_data` 条件一致。
2. 当两侧都有非空 return data 时，`length` 一致。
3. 当两侧都有非空 return data 且长度相等时，对符号 byte index `i` 证明 return data 内容一致。
4. 如果 result 中包含 `storage`，证明 storage Array 等价。
5. 如果 result 中包含 `transient_storage`，证明 transient storage Array 等价。

return memory 的地址关系是：

```text
EVM byte = evm_memory[evm_offset + i]
x86 byte = x86_memory[x86_base_addr + x86_offset + i]
```

EVM 的 `base_addr` 当前为 `None`，x86 的 `base_addr` 来自 `R15`。

如果两侧都没有非空 return data，内容比较会在 `has_return_data` 前提下自然 vacuous，不会强行比较未返回的 memory 区域。

### 3.2 storage / transient storage

`StorageEquivalenceChecks` 首先尝试结构化快速证明：

```text
直接 AST 等价
Store / If 链递归结构等价
path_condition 下的 ITE 选支消解
小预算 unsat oracle 辅助判断 path 是否蕴含某个分支条件
```

如果结构化路径失败，再退回通用 SMT 查询：

```text
exists key. evm_storage[key] != x86_storage[key]
```

当表达式涉及符号 `CallDataSize` 时，当前实现会先做一个小预算 quick check；若 Z3 返回 unknown，则按 calldata size 分区：

```text
size = 0..67
size >= 68
```

每个分区使用独立 capped timeout。这是为了让 ERC20 类样本中由 calldata size 触发的 storage 分支更可解。

### 3.3 debug 栈检查

`stack_check` 不是核心 refinement 条件，而是调试辅助。

当 `stack_check` 非空时，程序级验证会额外比较固定槽位坐标系中的若干 EVM/x86 stack slot。它使用独立 `stack_check_timeout_ms`，避免污染主 refinement timeout。

在 `path_observations=True` 下，如果需要 stack debug，`to_z3_paths(..., merge_state=True)` 会额外产出 merged state；否则不构造 merged state。

## 4. terminal path pair refinement

`verification/refinement_paths.py` 是当前全局 path observation 组合的核心。

### 4.1 path coverage

在比较 path pair 前，checker 先分别检查 EVM 和 x86 的 terminal paths 是否覆盖所有输入：

```text
Not(Or(path_conditions)) is UNSAT
```

如果某一侧没有 terminal path，直接失败：

```text
NO TERMINAL PATHS
```

如果 coverage 查询 SAT，则说明存在输入没有被任何 terminal path 覆盖，验证失败。

### 4.2 path pair 比较

对每个 pair：

```text
path_condition = And(evm_path.condition, x86_path.condition)
```

然后在这个 path condition 下调用与 merged-result 相同的 direct observable check。

默认会先做 feasibility 预检查：

```text
path_condition is SAT?
```

该检查使用 `_RefinementCheckTuning.path_pair_feasibility_timeout_ms`，当前最多 250ms。

结果处理：

```text
UNSAT    -> pair 不可达，跳过
SAT      -> 继续 refinement
UNKNOWN  -> 保守处理为可能可达，继续 refinement
```

`skip_feasibility=True` 时跳过这一步。soundness 不受影响：不可达 pair 的后续 refinement 查询会因为 `path_condition` UNSAT 而 vacuously 通过。代价只是统计里的 “feasible pair(s)” 会被计为所有 pair，并且每个 pair 都会进入后续 subcheck。

### 4.3 并行 path pair 检查

`path_pair_workers > 1` 时，`PathRefinementChecks` 使用 `ThreadPoolExecutor` 把 pair 切成 worker chunks。

每个 worker：

```text
创建独立 Z3 Context
创建独立 SolverFor("QF_AUFBV")
把 PathObservation 中的 Z3 AST translate 到 worker context
缓存已 translate 的 EVM/x86 path result
复用 worker-local solver 做 feasibility/refinement subchecks
```

Z3 AST translation 由全局 lock 保护，避免跨线程 context translation 的不稳定行为。

一旦某个 worker 发现失败，会设置 cancel event；其他 worker 在 chunk 边界看到 cancel 后退出。

## 5. x86 summary 框架

summary 框架位于 `x86_64/summaries`。

当前 summary 是 x86 执行器的“指令 slice 折叠”机制：

```text
matcher/discover 找到可 summary 的 x86 slice
X86SummaryRuntime 注册 summary
X86SymbolicExecutor 在精确 (block_addr, instruction_index) 命中 summary
summary.apply 直接更新 SMTState
执行器跳过原始 slice
```

这不是默认启用的优化。`build_x86_summary_runtime()` 在 `summary_config=None` 时返回空 runtime。

### 5.1 通用数据结构

核心结构：

```text
X86SummarySpec
  discover(ctx, strict=False)
  apply(summary, state, fresh_prefix)

X86Summary
  kind
  entry_addr
  start_block_addr
  start_instruction_index
  continuation
  covered_block_addrs
  clobber_registers
  clobber_flags
  payload

X86SummaryRuntime
  plugins
  manager
  hit stats
```

`X86SummaryManager` 会做基础结构校验：

```text
summary kind 必须已注册
start block / continuation block 必须属于当前 CFG
start instruction index 必须指向真实指令
summary coverage 不得重叠
same-block summary 不能吞掉块尾 ret/jmp/jcc
cross-block summary 必须声明 covered blocks 和 continuation
```

### 5.2 执行器如何应用 summary

`X86SymbolicExecutor._execute_block()` 逐条指令执行。每个 instruction index 先查询 summary runtime：

```text
summary = summary_runtime.get(block.start_addr, instruction_index)
```

命中后：

```text
new_mstate = summary_runtime.apply(summary, new_mstate)
```

如果是 same-block summary，执行器把 instruction index 移到 `summary.continuation.instruction_index`，继续执行同块后缀。

如果是 cross-block summary，执行器直接跳到 continuation block，添加一条压缩 CFG 边，并设置 `summary_control_flow_managed=True`，避免 entry 块原始控制流再产生幽灵终止态。

### 5.3 当前内置 summary：CALLDATALOAD

当前唯一内置 summary 是：

```text
kind = "calldataload"
spec = CallDataLoadSummarySpec
config = TRUSTED_SUMMARY_CONFIG = X86SummaryConfig.enabled(calldataload="fallback")
```

`CALLDATALOAD` matcher 识别 go-hpc-evm amd64 输出中的 `compileEVMCALLDATALOAD` 形状。它提取：

```text
entry_addr
exit_addr
zero_addr
partial_addr
entry_instruction_index
result_stack_offset
offset_limb_locs[4]
clobber_registers
internal_block_addrs
```

结构检查覆盖：

```text
entry block 的 overflow high-limb 检查
[r13+0x98] calldata size 读取
offset 与 size 的比较和 zero path
[r13+0x90] calldata pointer 读取
fast path 的 4 组 qword load + bswap + stack store
zero path 的 4 个 qword zero stores
partial path 的 32 个 byte load/store 覆盖
fast/zero/partial 三条路径收敛到同一个 exit
result stack offsets 连续
clobber registers 排除 R13/R14/R15 等保留寄存器
```

当前 `CALLDATALOAD` summary 还要求 low offset 是安全常量，避免 x64 `offset + 32` wrap 与共享 Go/EVM `getData(input, offset, 32)` 语义之间出现未证明差异。动态 low offset 会 fail closed；`muti_block_08` 的相关测试目前记录了这一限制。

`apply_calldataload_summary()` 使用共享语义：

```text
common.calldata.calldataload_word(
  calldata,
  callengine_input_size_bytes,
  offset_bv,
  omit_overflow_guard=False,
)
```

然后把 256-bit 结果写入 x86 stack 域：

```text
x86_memory.store_256bit(R14 + result_stack_offset, result, domain=STACK)
```

并用 fresh symbolic values 覆盖声明的 clobber registers 和 flags。

### 5.4 summary 信任边界

当前代码中的 `TRUSTED_SUMMARY_CONFIG` 表示调用方显式信任该 summary。它不等价于“proof artifact 已被 verifier 自动核验”。

因此，当前 soundness 依赖：

```text
CALLDATALOAD matcher 的 fail-closed 结构检查
共享 calldataload_word 语义与 EVM IR 侧一致
调用方只在接受 trusted summary 边界时传 TRUSTED_SUMMARY_CONFIG
```

文档和代码中应继续把这一点说清楚：summary matcher 只能说明 slice 结构可被折叠，不能替代局部语义证明。后续引入 proof artifact 后，应把 `TRUSTED_SUMMARY_CONFIG` 从“显式信任”迁移到“显式启用已验证 summary”。

## 6. 当前真实样本的组合方式

### 6.1 perf_erc20_lite

`tests/integration/test_refinement_checker.py` 中的 `test_verify_perf_erc20_lite_program_pair()` 使用：

```text
timeout_ms=1200000
path_observations=True
path_pair_workers=4
enable_merge=True
skip_feasibility=True
summary_config=TRUSTED_SUMMARY_CONFIG
```

测试期望：

```text
calldataload discovered == 5
calldataload hits == 5
```

该样本覆盖 dispatcher、selector 分支、SHA3 mapping key、SLOAD/SSTORE、RETURN/REVERT 等真实合约常见路径。

### 6.2 muti_block

`test_verify_muti_block_program_pair_full()` 使用：

```text
timeout_ms=1200000
path_observations=True
path_pair_workers=4
enable_merge=True
summary_config=TRUSTED_SUMMARY_CONFIG
```

同样期望：

```text
calldataload discovered == 5
calldataload hits == 5
```

### 6.3 muti_block_08

`test_verify_muti_block_08_program_pair_full()` 当前仍标记 skip。

相关 unit test 表明 `CALLDATALOAD` matcher 对动态 low offset 会 fail closed；fallback 模式只发现安全常量 offset 的 summary，strict 模式会报告 dynamic low offset 错误。这是当前 summary 健全性（soundness）边界的一部分。

## 7. 与“局部 Lemma + 全局组合”的关系

当前实现已经具备全局组合的运行骨架：

```text
程序级 CFG 符号执行
terminal path observations
path pair refinement
x86 summary runtime
summary hit stats
```

但“局部 Lemma”目前还没有进入自动信任链。现在的 summary 更接近手工 trusted summary：

```text
已实现：发现 slice、结构检查、状态折叠、命中统计
未实现：proof artifact、proof status、lemma registry、verified-only gate
```

因此后续路线应以当前 summary runtime 为落点，而不是另起一套执行框架。

## 8. 后续路线：把 trusted summary 升级为 verified summary

### 8.1 proof artifact schema

每个可启用 summary hit 至少需要记录：

```text
summary_kind
entry_addr
start_key
continuation
covered_block_addrs
x86_bytes_hash 或 instruction hash
layout / operand mapping
clobber_registers
clobber_flags
frame_touches
semantic_model_version
solver / proof strategy version
proof_status
```

只有 `proof_status == verified` 的 artifact 才能进入默认 verifier 信任链。

### 8.2 fail-closed gate

未来的 `X86SummaryRuntime` 应在注册 summary 时区分：

```text
discovered but unverified
verified and enabled
trusted override
```

建议策略：

```text
production verifier:
  只允许 verified summary
  未验证命中 fail closed

development verifier:
  允许 trusted override
  输出明确告警和 hit 列表

offline prover:
  对 discovered summary 生成 proof obligation
```

### 8.3 CALLDATALOAD 的补齐项

当前 `CALLDATALOAD` summary 的下一步不是扩大 matcher，而是给现有 matcher 产物补 proof：

```text
证明 fast path load/bswap/store 等价于 calldataload_word 的完整 32-byte 读取
证明 zero path 等价于越界或 overflow 返回 0
证明 partial path 的 32 byte copy/zero padding 等价于 calldataload_word
证明 clobber/frame 声明覆盖所有被写位置
证明 low offset 动态情形的 x64 offset+32 wrap 处理，或继续 fail closed
```

### 8.4 MUL 的位置

`MUL` 仍是未来引入 algorithmic lemma 的主要候选，因为直接展开真实 x86 multiplication carry-chain 容易让全局 solver 变慢或 unknown。

建议仍沿用旧方案的三层分解，但需要标记为未实现：

```text
L1: actual x86 MUL slice == abstract limb-chain shape
L2: abstract limb-chain shape == common/uint256.py 的 mul_semantics
L3: mul_semantics == (x * y) mod 2^256
```

目标不是把完整 `MUL` carry-chain 放进每次全局 query，而是让全局组合只消费已验证 summary term。

## 9. 当前实现应保持的不变量

1. summary 默认关闭，必须由调用方显式配置。
2. matcher 失败必须 fail closed，不应静默回退到错误 summary。
3. path coverage 必须在 path pair refinement 前检查。
4. `skip_feasibility=True` 只能跳过剪枝，不能跳过 refinement subchecks。
5. path pair 并行时必须使用 worker-local Z3 Context/Solver，跨 context AST 必须 translate。
6. return data 比较必须带 `has_return_data` 和 `length` 前提。
7. storage/transient storage 的结构化 fast path 只能证明等价，不能把 unknown 当成功。
8. `TRUSTED_SUMMARY_CONFIG` 的使用必须在测试和报告中显式可见。

## 10. 结论

当前代码已经从“单个 monolithic Z3 query”推进到更可扩展的组合形态：

```text
EVM/x86 CFG 符号执行
terminal path observation
path pair refinement
可选 x86 summary folding
```

这条路径已经支撑 `perf_erc20_lite` 和 `muti_block` 的全符号程序级验证。

下一阶段的重点不是重写全局 checker，而是把现有 x86 summary runtime 的信任边界补齐：为 `CALLDATALOAD` 生成可核验 proof artifact，再把相同机制扩展到 `MUL` 等高成本 slice。届时本文档中的“局部 Lemma”才会从路线图变成默认验证链的一部分。
