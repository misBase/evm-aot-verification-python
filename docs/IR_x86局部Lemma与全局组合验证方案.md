# IR/x86 局部 Lemma 与全局组合验证方案

## 1. 背景与当前状态

当前目标是证明：

```text
IR 执行结果 == x86 AOT 执行结果
```

直接把完整 IR 和完整 x86 bytes 一次性展开给 Z3，会遇到两个问题：

1. x86 指令级语义过细，尤其是 `MUL` 这类 256-bit 算术会产生大量 bit-vector、carry、flag、内存表达式。
2. Go AOT 后端生成的 x86 不是单一固定模板，同一个 IR opcode 可能因为寄存器分配、栈位置、常量传播、RAX/RDX 保存恢复等因素生成不同 bytes。

因此，全局验证不应依赖 monolithic symbolic execution，而应采用组合式验证：

```text
局部慢证明 x86 slice 等价于 IR op summary
+
全局快速组合已证明 summary
```

`MUL` 当前只是一个局部试点。如果 `MUL` 局部都需要复杂证明，全局直接展开一定更难；这说明系统需要 lemma / summary / cache 机制，而不是继续扩大单个 Z3 query。

当前代码状态：

```text
Uint256.mul_semantics: holiman 4x64 BV 建模
MUL micro-refinement: 真实 BV 路径，当前 1s timeout 下 xfail
```

历史上曾经有一条 `lifted_mul` / fresh-product 路径。它只证明共享乘积占位符下的 carry-chain 结构一致，不证明真实乘法语义。该路径已经删除，不再作为验证方案的一部分。

## 2. 核心概念

### 2.1 x86 slice

x86 slice 是一个 IR op 编译后对应的机器码片段，例如一个 `MUL` IR operator 可能对应几十条 x86 指令。

slice 必须来自 Go AOT 编译器输出的真实 byte range，而不是手写猜测的模板。

### 2.2 layout

layout 描述 IR 值在 x86 状态中的位置。

一个 256-bit 值由 4 个 64-bit limb 组成，每个 limb 可能位于：

```text
register: 例如 R8
stack memory: 例如 [R14 - 0x40]
constant: 例如 0
```

state relation 连接 IR state 与 x86 state：

```text
R(ir_state, x86_state, layout)
```

含义是：在当前 layout 下，IR state 中的 stack / memory / storage / gas 等抽象状态，被 x86 的寄存器、stack memory、callEngine 字段等正确表示。

例如：

```text
layout(x.z0) = R8
=> ir_stack_x.z0 == x86.regs[R8]

layout(x.z0) = [R14 - 0x40]
=> ir_stack_x.z0 == x86.stack_mem[R14 - 0x40]

layout(x.z0) = const(0)
=> ir_stack_x.z0 == 0
```

### 2.3 summary / lemma

summary 是某段已证明 x86 slice 的抽象语义。

例如 `MUL` summary：

```text
输入: x, y
输出: (x * y) mod 2^256
副作用: 更新 EVM stack 顶部，允许 clobber 指定临时寄存器和 flags
```

对应 lemma 形式：

```text
forall ir_state, x86_state.
  R_before(ir_state, x86_state, layout_before)
  =>
  R_after(IR_MUL(ir_state), ExecuteX86Slice(x86_state), layout_after)
  and frame_conditions
```

推荐让 lemma 对 layout 参数化，而不是把某个具体 layout 偷偷 bake 到 proof artifact 里：

```text
forall x, y, layout_before, layout_after, x86_state.
  LayoutPre(layout_before, x, y, x86_state)
  =>
  LayoutPost(layout_after, IR_MUL(x, y), ExecuteX86Slice(bytes, x86_state))
```

这样同一段 bytes 可以在不同 IR 上下文中按不同 layout 实例化。若某个 proof artifact 固定了具体 layout，则 layout hash 必须进入 cache key。

## 3. 分阶段路线

### 阶段 1：固定 bytes strong lemma

先对当前已知的固定 `X86_MUL_CORE_HEX_SEQUENCE` 建立强语义 lemma。

第一条 proof 选择最常见形态：

```text
stack-only layout
q2/q3/q4 都不是 compile-time constant zero
固定当前 X86_MUL_CORE_HEX_SEQUENCE bytes
```

证明目标：

```text
forall x, y.
  ExecuteActualX86(X86_MUL_CORE_HEX_SEQUENCE, stack_layout_input)
  ==
  Uint256.mul_semantics(x, y)
```

或者更强：

```text
ExecuteActualX86(...) == (x * y) mod 2^256
```

这里 `ExecuteActualX86` 必须使用项目中的真实 x86 语义路径，例如：

```text
instruction.to_z3(state)
```

允许该阶段使用长 timeout：

```text
600s 或更长
```

因为该 proof 只需要离线证明一次，并可缓存。

产出：

1. `tests/slow` 或 `tests/proofs` 下的 `MUL` strong lemma test。
2. proof 结果记录：bytes hash、solver result、reason_unknown、timeout、solver version、proof date。
3. 如果结果是 `unknown`，保留公式规模和诊断信息，用于后续拆分。

验收：

1. 对固定 stack-only、non-const-zero `MUL` bytes，strong proof 返回 `unsat`，或产出明确 `unknown` 诊断。
2. proof 使用真实 x86 BV 语义路径。
3. proof 结果可进入后续 cache / registry。

### 阶段 2：Python 侧 slice 恢复与 exact bytes 匹配

短期目标是不改 Go AOT 编译器。Python verifier 的输入只包括：

```text
machine code bytes
IR JSON
```

Python 侧根据 IR op 顺序和已知 AOT codegen 形态恢复：

```text
IR op -> x86 byte range
operand/result layout
known x86 slice hash
```

恢复策略必须 fail closed：

```text
匹配到已知、已证明的 exact bytes:
  应用对应 summary

匹配不到:
  报错 unverified slice
  或在离线模式触发 strong prover
```

不能因为“看起来像某个模板”就信任该 slice。v0 优先使用 exact bytes hash / 已证明 summary hash，而不是宽松模式匹配。

验收：

1. Python verifier 能从 machine code + IR JSON 中恢复至少固定 stack-only `MUL` 的 byte range。
2. 恢复出的 bytes hash 必须命中已验证 summary，或者 fail closed。
3. 不需要修改 Go AOT 编译器。

### 阶段 3：IR/x86 state relation

定义统一的状态关系：

```text
R(ir_state, x86_state, layout)
```

需要覆盖：

```text
EVM stack 中的 256-bit 值
x86 stack memory，即 R14 域
x86 general-purpose registers
callEngine side-channel 字段
EVM memory / storage / transient storage
gas / pc / status code
readonly sources: calldata / code / returndata
```

每个 256-bit 值拆成：

```text
z0, z1, z2, z3
```

其中 `z0` 是最低 limb。

frame condition 应描述逻辑值保持，而不是物理位置保持。

对每个 IR live value `v`，在 op 前后都必须存在某个 x86 位置 `L`，使得：

```text
R(v, L)
```

成立。但 `L_before` 不必等于 `L_after`。合法的 register allocation、spill、reload 都可能移动值的位置。

summary 必须声明：

```text
哪些逻辑值被消费
哪些逻辑值被产生
哪些 live value 在 op 后仍需被 layout relation 追踪
哪些物理寄存器、flags、memory slot 可被 clobber
```

验收：

1. 能表达 stack / register / constant 三种 limb 位置。
2. 能表达 `MUL` 前后 layout 改变。
3. 未声明 clobber 的状态变化会导致 proof 失败。

### 阶段 4：MUL 证明分层

如果固定 bytes strong lemma 无法在可接受时间内证明，应将 `MUL` 强证明拆成可复用的小 lemma。

推荐拆分：

```text
actual x86 MUL slice == holiman_limb_mul_shape(x, y, const_zero_decisions)
holiman_limb_mul_shape(x, y, const_zero_decisions) == (x * y) mod 2^256
layout_before 正确读取 IR operands
layout_after 正确写回 IR result
```

`actual x86 MUL slice == holiman_limb_mul` 不是单条 lemma，而是一族按真实 emitted slice 生成的 lemma。影响 shape 的因素包括：

```text
q2/q3/q4 的 const-zero 分支组合
operand limb 的 register / stack / constant layout
result limb layout
RAX/RDX save/restore 模式
临时寄存器分配
实际 emitted bytes
```

其中 `q2/q3/q4` 是三个独立 compile-time constant-zero 判断点，因此最多形成 8 种算法 shape。不要预先枚举并证明所有 shape；应当按真实程序中出现的 emitted slice 生成和缓存 lemma。

验收：

1. 算法语义 lemma 可被多个 x86 layout 复用。
2. register / memory / constant 变体只需要重新证明 x86 slice 和 layout，不需要重复证明 holiman 数学性质。
3. 任何真实程序中出现的新 emitted slice 都必须 fail closed 或触发离线证明。

### 阶段 5：lemma registry 与 proof cache

把已证明的局部 lemma 注册起来，全局验证时可直接复用。

如果 lemma statement 已经对 layout 参数化，则推荐最小 cache key：

```text
x86_bytes_hash
compiler_profile_hash
lemma_strategy
```

这里 `x86_bytes_hash` 已经覆盖：

```text
const-zero 分支组合
寄存器选择
RAX/RDX save/restore 实际指令
临时寄存器分配导致的编码差异
```

但 layout 不能从语义前提中消失。它必须作为 lemma precondition / parameter 被检查和实例化。

如果某个 proof artifact 固定了具体 layout、clobber set 或 operand mapping，那么对应的 `layout_hash`、`clobber_set_hash`、`operand_mapping_hash` 必须进入 cache key。

`lemma_strategy` 应是封闭枚举，而不是任意字符串：

```text
z3_qf_bv_long
z3_qf_nia_with_mul
isabelle_certified
```

cache value 至少包含：

```text
summary_id
precondition
postcondition
frame_condition
proof_status
proof_artifact_path
solver_version
created_at
```

cache miss 策略：

```text
开发/离线模式: 触发局部 slow proof
严格验证/CI 模式: 报错 unverified slice
```

不允许在 cache miss 后标记为 unsafe trust 并继续通过。

验收：

1. 相同 x86 slice 不重复证明。
2. 若后续接入 compiler profile，compiler profile 变化会使旧 cache 失效。
3. layout 变化不会误用旧 lemma。
4. cache miss fail closed，或显式进入离线证明流程。

### 阶段 6：全局组合验证

在完整程序验证中，以 IR op 边界作为 cutpoint，组合局部 summary。

验证流程：

```text
初始化 IR state 与 x86 state
建立 R_0(ir_state_0, x86_state_0, layout_0)

for each IR op:
  Python 从 machine code + IR JSON 恢复 x86 slice 与 layout
  查询 lemma registry
  如果命中 verified summary:
    应用 IR op semantics
    应用 x86 summary
  否则:
    fail closed 或触发离线证明
  建立 R_{i+1}

最终检查 IR final state == x86 final state
```

全局 solver 主要证明：

```text
summary 之间的 state relation 连续
stack height / stack layout 正确演化
control flow 与 block boundary 对齐
memory / storage / gas 等跨 op 状态一致
host call summary 与 callEngine 状态一致
```

全局 solver 不应重复证明：

```text
MUL 内部 carry-chain
SHA3 内部 hash
DIV/MOD 内部算法
CALL host 细节
```

这些应由局部 summary 或 host summary 承担。

## 4. 对 `MUL` 的具体下一步

第一步：新增 slow proof：

```text
fixed stack-only, non-const-zero X86_MUL_CORE_HEX_SEQUENCE
==
Uint256.mul_semantics
```

该 proof 应使用项目真实 BV x86 语义路径：

```text
instruction.to_z3(state)
```

推荐先给 600s timeout，并记录：

```text
solver result
reason_unknown
公式规模
bytes hash
solver version
```

第二步：在 Python 侧恢复 `MUL` slice：

```text
operand limb locations
result limb locations
fixed stack-only byte range
exact bytes hash
```

第三步：按真实 emitted slice 生成 lemma，而不是预枚举所有组合。

优先级建议：

```text
1. stack-only + non-const-zero
2. q4 = 0 的简化 slice
3. q3 = 0, q4 = 0 的简化 slice
4. register-based operand layout
5. 其他真实程序中出现的 slice
```

第四步：全局验证中只对已证明的 `MUL` summary 做替换。

## 5. 风险与原则

### 5.1 不能静默信任 summary

任何 summary 必须有明确 proof status：

```text
unverified
z3_verified
certified
```

全局验证只允许使用：

```text
z3_verified
certified
```

任何没有真实语义 proof 的结构检查结果都不能进入全局 verifier 的信任链。

### 5.2 bytes 匹配是安全但不完备的

精确 bytes 匹配：

```text
sound: 不会误用 lemma
not complete: 覆盖不了 register/constant 变体
```

模式匹配：

```text
complete 潜力更高
soundness 风险更高
```

初期建议使用 exact bytes hash。后续如果引入模式匹配，必须先证明 pattern matcher 的 soundness。

短期不改 Go AOT 编译器，因此 exact bytes 匹配是默认路线。代价是 coverage 不完备：Python 侧不认识的新 codegen 形态会验证失败，而不是被自动信任。

### 5.3 layout 必须进入 lemma 前提

如果一个 lemma 是在：

```text
x0 = [R14 - 0x40]
```

的前提下证明的，不能用于：

```text
x0 = R8
```

除非 lemma 本身已经参数化覆盖这两种 layout。

### 5.4 frame condition 与语义等价同等重要

只证明输出值相同不够。还要证明未声明改变的状态不变。

这里的“不变”指逻辑 live value 被正确保留，而不是必须留在同一个物理寄存器或 stack slot。合法 spill / reload 可以改变位置，但不能丢失值。

### 5.5 Go AOT metadata 是最后的可选增强

如果后续 exact bytes / Python 恢复路线覆盖率不足，才考虑让 Go AOT 输出结构化 metadata。

metadata 顶层建议包含：

```text
compiler_profile:
  go_hpc_evm_commit_hash
  amd64_compiler_version
  register_allocator_version
  assembler_or_encoding_profile
```

每个 op metadata 可包含：

```text
ir_op_id
ir_pc
ir_opcode
x86_byte_range
operand_locations
result_locations
const_zero_decisions
rax_rdx_spill_info
```

`rax_rdx_spill_info` 建议保留精确模式：

```text
rax_rdx_spill_info:
  rax:
    mode: none | release_location_to_stack | save_to_temp_register
    stack_offset: int | null
    temp_register: string | null
  rdx:
    mode: none | release_location_to_stack | save_to_temp_register
    stack_offset: int | null
    temp_register: string | null
```

这不是 soundness 的必要条件，只是提高覆盖率、诊断质量和维护性的后续选项。

## 6. 最小可执行里程碑

### Milestone 1：MUL 固定 bytes strong lemma

目标：

```text
stack-only non-const-zero X86_MUL_CORE_HEX_SEQUENCE == Uint256.mul_semantics
```

验收：

```text
600s 内 slow proof 返回 unsat，或产出明确 unknown 诊断
proof 结果可缓存
```

### Milestone 2：Python slice recovery

目标：

```text
输入 machine code + IR JSON
Python 能恢复 fixed stack-only MUL 的 x86 byte range
```

验收：

```text
不修改 Go AOT 编译器
恢复出的 bytes hash 命中 verified summary，或 fail closed
```

### Milestone 3：summary registry

目标：

```text
已证明 summary 可被全局验证器查询和应用
```

验收：

```text
未证明 summary 不可被静默使用
v0 layout-parametric summary 的 key 包含 bytes/lemma strategy
若后续接入 Go AOT metadata，再把 compiler profile 纳入 key
非 layout-parametric summary 必须额外包含 layout/clobber/operand mapping hash
```

### Milestone 4：小程序组合验证

目标：

```text
验证包含 ADD + MUL + STOP 的小程序
其中 MUL 使用 verified summary，不展开 x86 carry-chain
```

验收：

```text
全局验证通过
报告显示 MUL summary 命中
```

### Milestone 5：扩展到真实 block

目标：

```text
对真实 EVM block 做 summary-based IR/x86 等价验证
```

验收：

```text
大部分普通算术和栈操作由 summary 覆盖
重型 opcode 不导致全局 solver 超时
```

### Milestone 6：可选 Go AOT metadata

目标：

```text
当 Python slice recovery 覆盖率不足时，再让 Go AOT 输出 metadata
```

验收：

```text
metadata 只作为覆盖率和诊断增强
不改变 verifier 的 fail-closed 原则
```

## 7. 结论

最终系统应避免把完整 x86 程序全部展开给一个 Z3 query。更可扩展的路线是：

```text
局部证明 hard x86 slice
生成 verified summary
缓存 lemma
全局按 IR op 边界组合 summary
```

`MUL` 的困难不是偶然问题，而是提示我们必须引入 summary / lemma / cache 体系。最终证明链必须包含真实乘法语义的 strong lemma。v0 summary 的复用必须绑定具体 bytes 和 lemma strategy，并在 lemma 前提中显式检查 layout、clobber 和 operand mapping；如果这些前提被 bake 进 proof artifact，就必须进入 cache key。compiler profile 是后续接入 Go AOT metadata 后的可选 cache 维度。
