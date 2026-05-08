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

当前 `MUL micro-refinement` 在 1s timeout 下 xfail 是预期状态。Milestone 1 的 L1/L2/L3 分层证明完成后，应由 `shape_id` 对应的 algorithmic lemma 替代该直接展开路径，并把对应验证目标从 xfail 转为 `unsat`。

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

推荐让 lemma 对 layout 和结构化 slice 参数化，而不是把某个具体 layout 偷偷 bake 到 proof artifact 里：

```text
forall x, y, actual_bytes, parse_witness, parsed_slice, layout_before, layout_after, x86_state.
  CheckedParseWitness(actual_bytes, parse_witness, parsed_slice)
  and ParsedMULSlice(parsed_slice, shape_id, operand_locs, result_sp, temp_reg_roles, rax_rdx_freeup)
  and
  LayoutPre(layout_before, x, y, x86_state)
  =>
  LayoutPost(layout_after, IR_MUL(x, y), ExecuteParsedMULSlice(parsed_slice, x86_state))
```

`CheckedParseWitness` 是 actual bytes 与 parsed slice 之间的桥。verifier replay 必须保证：

```text
ExecuteParsedMULSlice(parsed_slice, x86_state)
==
ExecuteX86Slice(actual_bytes, x86_state)
```

这样同一个 algorithmic shape 可以在不同 IR 上下文中按不同 layout 实例化。若某个 proof artifact 固定了具体 layout，则 layout hash 必须进入 cache key。

### 2.4 L1 解析证书 schema 与 replay 协议

L1 parser 不应进入信任链。它只产生可复核的 `parse_witness`；trusted verifier replay/checker 负责独立检查 witness 是否确实来自 actual bytes。

`parse_witness` 至少包含：

```text
parse_witness = [
  {
    byte_offset: int
    length: int
    decoded_instruction: string
    grammar_node_id: string
    binds: {
      register_role: string | null
      operand_source: string | null
      result_target: string | null
      reads: set[location]
      writes: set[location]
      clobbers: set[location]
    }
  },
  ...
]
```

verifier replay 必须独立检查：

```text
1. byte_offset / length 对应的 actual bytes 反汇编结果等于 decoded_instruction
2. witness 条目按 byte_offset 连续覆盖整个 MUL slice，无遗漏、无重叠
3. grammar_node_id 序列拓扑等于 shape_id 对应的 abstract holiman chain
4. binds 中的 register_role / operand_source / result_target 前后一致且无冲突
5. reads / writes / clobbers 均包含在 frame_touches 声明允许的集合内
6. result store 覆盖 result_sp 对应的 4 个 EVM stack limb slot
```

replay 还需要维护 abstract value tracking table。该表逐节点记录 abstract value id 的 def-use 流转，而不是信任 parser 自报某个寄存器“语义上就是 tmp1”。

```text
node_id
abstract_value_id
defined_at
current_locations
required_inputs
produced_outputs
flags_in
flags_out
```

检查示例：

```text
MULQ paramReg:
  required_inputs: RAX = q_i, paramReg = p_j
  produced_outputs: RAX = lo(q_i * p_j), RDX = hi(q_i * p_j)

ADDQ tmpReg, RAX:
  required_inputs: RAX = lo(...), tmpReg = carry/tmp value
  produced_outputs: RAX = sum low limb, flags = add flags

ADCQ 0, RDX:
  required_inputs: RDX = high limb, flags = previous add flags
  produced_outputs: RDX = high limb plus carry, flags = adc flags
```

只有 replay 成功后，`parsed_slice` 才能用于实例化 algorithmic lemma；parser 解析失败、witness 不连续、角色绑定冲突或 tracking table 校验失败，都必须 fail closed。

## 3. 分阶段路线

### 阶段 1：MUL 分层 lemma

不再把第一阶段定义为“一次性证明某个固定 bytes slice 等价于 `Uint256.mul_semantics`”。真实 `compileEVMMul` 的完整 non-const-zero 形态包含 10 条 `MULQ`、12 条 `ADDQ`、12 条 `ADCQ`，还包含大量 `MOVQ` 与 layout 相关的 load/store。直接把完整真实 x86 slice 展开成一个 monolithic QF_BV 目标，容易把 solver 压到 `unknown` 或超时。

第一阶段应拆成三层：

```text
L1: actual x86 MUL slice == abstract holiman op chain
L2: abstract holiman op chain == Uint256.mul_semantics
L3: Uint256.mul_semantics == (x * y) mod 2^256
```

其中：

```text
L1 是 x86 ↔ IR 桥：
  从真实 machine code 结构化解析出 shape_id、operand_locs、temp_reg_roles、
  result_sp、rax_rdx_freeup 和 frame_touches。

L2 是算法层：
  证明抽象 holiman limb chain 与 common/uint256.py 中的 mul_semantics 一致。

L3 是整数语义层：
  证明 mul_semantics 的 4 个 limb 拼接后等价于截断乘法 (x * y) mod 2^256。
```

`L2` 和 `L3` 与 x86 bytes、寄存器分配、stack offset 无关，应作为可复用的算法 lemma 缓存。`L1` 只负责证明当前真实 slice 符合某个已知 algorithmic shape，并正确读取/写回当前 layout。

产出：

1. 8 种 `shape_id` 的 abstract holiman op chain 定义。
2. `shape_id -> algorithmic lemma` 的 proof/cache 记录。
3. `L1` 结构化解析器输出格式与 fail-closed 检查规则。

验收：

1. `q2/q3/q4` 的 compile-time const-zero 组合能映射到 8 种 `shape_id`。
2. `L2/L3` proof 不依赖具体 x86 bytes。
3. `L1` 解析失败、frame 检查失败或 layout 前提不满足时必须 fail closed。

### 阶段 2：Python 侧结构化 slice 恢复

短期目标是不改 Go AOT 编译器。Python verifier 的输入只包括：

```text
machine code bytes
IR JSON
```

Python 侧根据 IR op 顺序和 `compileEVMMul` 的结构化 codegen 形态恢复：

```text
IR op -> x86 byte range
parse_witness
shape_id
operand_locs[8]
result_sp
temp_reg_roles
rax_rdx_freeup
frame_touches
x86_bytes_hash
```

恢复策略必须 fail closed：

```text
解析出合法 MUL slice:
  使用 shape_id 命中 algorithmic lemma
  用 operand_locs / result_sp / temp_reg_roles / rax_rdx_freeup 实例化 summary

解析失败或 frame 检查失败:
  报错 unverified slice
  或在离线模式触发结构化诊断 / 局部证明
```

不能因为“看起来像某个模板”就信任该 slice。结构化 parser 的输出必须可复核：每条关键指令应能对应到 abstract holiman chain 的一个节点，且寄存器角色、operand location、result stack slot、RAX/RDX free-up 和 frame touch set 都必须被显式检查。

`x86_bytes_hash` 只作为完整性校验、诊断和 proof artifact 记录使用，不作为主 lemma cache key。

验收：

1. Python verifier 能从 machine code + IR JSON 中恢复 `MUL` 的 byte range 和结构化参数。
2. 恢复出的 `shape_id` 必须命中 verified algorithmic lemma，或者 fail closed。
3. `x86_bytes_hash` 可记录和校验，但不能决定 lemma 是否可用。
4. 不需要修改 Go AOT 编译器。

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

对 `MUL` v1，frame condition 可以非常具体：

```text
允许改变:
  RAX / RDX
  parser 识别出的 temp_reg_roles 对应的通用寄存器
  flags
  result_sp 对应的 4 个 EVM stack limb slot
  rax_rdx_freeup 中声明的 spill slot 或 temp register

只读:
  R14 作为 EVM stack base pointer

必须不变:
  R13 / R15
  CallEngine gas / status / pc 等字段
  EVM memory / storage / transient storage
  calldata / code / returndata 等 readonly sources
  对每个 v ∈ live_before \ consumed_by_MUL，
    必须存在 loc ∈ layout_after，使 R(v, loc) 成立
```

这意味着 `MUL` summary 不需要在局部 proof 中展开完整 EVM state；memory、storage、gas、status 等只需要作为 untouched frame 批量声明，并由 slice 静态结构检查确认未被访问。

验收：

1. 能表达 stack / register / constant 三种 limb 位置。
2. 能表达 `MUL` 前后 layout 改变。
3. 未声明 clobber 的状态变化会导致 proof 失败。

### 阶段 4：MUL algorithmic shape

`compileEVMMul` 是结构化、参数化的模板代码。真正改变乘法算法骨架的因素只有 `q2/q3/q4.isConstantZero()` 三个 compile-time 判断点，因此应预枚举 8 种 `shape_id`，而不是按每个 emitted bytes 生成一条独立算法 lemma。

推荐证明分层：

```text
actual x86 MUL slice == holiman_limb_mul_shape(shape_id, x, y)
holiman_limb_mul_shape(shape_id, x, y) == Uint256.mul_semantics(x, y)
Uint256.mul_semantics(x, y) == (x * y) mod 2^256
layout_before 正确读取 IR operands
layout_after 正确写回 IR result
```

`shape_id` 只由下面三位决定：

```text
bit0: q2.isConstantZero()
bit1: q3.isConstantZero()
bit2: q4.isConstantZero()
```

以下内容不是 algorithmic shape 维度，只是 lemma 实例化参数或结构检查项：

```text
operand limb 的 register / stack / constant layout
result_sp 和 result limb 写回 offset
temp_reg_roles，即 param/tmp/res 寄存器角色
RAX/RDX free-up prologue/epilogue
实际 emitted bytes 与 x86_bytes_hash
```

`rax_rdx_freeup` 需要区分：

```text
none
spill_location_to_stack
save_to_temp_register
```

其中 `spill_location_to_stack` 对应 `makeRAXAndRDXFree -> stealTargetRegister -> compileReleaseRegisterToStack` 的间接路径，可能在 slice 前部写入 R14 stack slot；`save_to_temp_register` 可能在前后出现 reg-reg save/restore。这些都是 frame/prologue 检查项，不改变 holiman 乘法骨架。

验收：

1. 8 种 `shape_id` 都有明确的 abstract holiman op chain。
2. 算法语义 lemma 可被多个 x86 layout 复用。
3. register / memory / constant 变体只需要重新实例化 layout 和 frame 前提，不需要重复证明 holiman 数学性质。
4. 任何真实程序中出现的新结构如果无法解析为已知 `shape_id`，必须 fail closed 或触发离线诊断。

### 阶段 5：lemma registry 与 proof cache

把已证明的局部 lemma 注册起来，全局验证时可直接复用。

如果 lemma statement 已经对 layout 参数化，则 algorithmic lemma 的推荐主 cache key：

```text
shape_id
lemma_strategy
solver_version
```

这里 `shape_id` 覆盖：

```text
q2/q3/q4 的 compile-time const-zero 分支组合
abstract holiman op chain 的算法骨架
```

但 layout、寄存器角色和 frame 条件不能从语义前提中消失。它们必须作为 lemma precondition / parameter 被检查和实例化。

如果某个 proof artifact 固定了具体 layout、clobber set 或 operand mapping，那么对应的 `layout_hash`、`clobber_set_hash`、`operand_mapping_hash` 必须进入 cache key。

`x86_bytes_hash` 不作为主 lemma cache key。它应记录在具体 slice artifact 中，用于：

```text
完整性校验
诊断与回归定位
确认 parser 输入与 proof artifact 对应
```

`lemma_strategy` 应是封闭枚举，而不是任意字符串：

```text
z3_qf_bv_long
z3_qf_nia_with_mul
isabelle_certified
```

当前 v1 只要求实现 `z3_*` 策略；`isabelle_certified` 仅作为未来 certified proof 后端预留。

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
solver_version 不一致: 视为 cache miss
```

不允许在 cache miss 后标记为 unsafe trust 并继续通过。`solver_version` 不一致时，旧 artifact 可以保留作历史记录，但不能进入当前信任链。

验收：

1. 相同 `shape_id` 的算法性质不重复证明。
2. 具体 x86 slice 必须重新通过结构化解析和 frame 检查。
3. layout 变化不会误用旧 lemma，因为 layout 是实例化前提而不是主 cache key。
4. cache miss fail closed，或显式进入离线证明流程。

### 阶段 6：全局组合验证

在完整程序验证中，以 IR op 边界作为 cutpoint，组合局部 summary。

对 `MUL`，组合 query 中 IR 侧不要把 `Uint256.mul_semantics` 展开为 limb/carry 公式。IR 侧 `MUL` 和 x86 summary 侧 `MUL` 应共同抽象为同一个 UF / summary term：

```text
mul_uf(x, y)
```

`mul_uf` 与 `Uint256.mul_semantics`、截断乘法 `(x * y) mod 2^256` 的一致性由 L2/L3 离线 proof artifact 保证，不在全局 query 中重复展开。

验证流程：

```text
初始化 IR state 与 x86 state
建立 R_0(ir_state_0, x86_state_0, layout_0)

for each IR op:
  Python 从 machine code + IR JSON 恢复 x86 slice、layout 与结构化参数
  查询 shape_id 对应的 lemma registry
  如果命中 verified algorithmic summary 且结构化参数检查通过:
    对 MUL: IR 侧与 x86 summary 侧产生同一个 mul_uf(x, y)
    对其他 op: 应用对应 IR summary 与 x86 summary
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
结构化 slice 参数与 summary 前提一致
```

全局 solver 对 `mul_uf` 只允许使用以下白名单：

```text
允许:
  UF congruence
  同一 cutpoint 内 IR summary 与 x86 summary 产生相同 mul_uf(x, y) 的等式
  L2/L3 proof artifact 的 proof_status / cache key 检查

禁止:
  展开 Uint256.mul_semantics
  注入 (x * y) mod 2^256 的 BV / NIA 定义
  注入交换律、结合律、分配律等代数公理
  在全局 query 中重新证明 MUL carry-chain
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

第一步：定义 8 种 algorithmic shape：

```text
shape_id = (q2_zero ? 1 : 0)
         | (q3_zero ? 2 : 0)
         | (q4_zero ? 4 : 0)
```

每个 `shape_id` 对应一条 abstract holiman op chain。完整 non-const-zero shape 对应 10 个 64-bit multiplication 节点；const-zero shape 通过删除对应高 limb 乘法链得到。

第二步：证明可复用算法 lemma：

```text
abstract_holiman_chain(shape_id, x, y) == Uint256.mul_semantics(x, y)
Uint256.mul_semantics(x, y) == (x * y) mod 2^256
```

这两类 proof 与 x86 bytes 无关，可按 `shape_id` 缓存。

第三步：在 Python 侧实现 `MUL` 结构化 slice recovery：

```text
输入: machine code + IR JSON + x86 CFG
输出:
  shape_id
  operand_locs[8]
  result_sp
  temp_reg_roles
  rax_rdx_freeup
  frame_touches
  x86_bytes_hash
```

parser 必须识别：

```text
setAndLoad(resultRegister, q_i)
setAndLoad(paramReg, p_j)
MULQ / ADDQ / ADCQ / MOVQ chain
q2/q3/q4 const-zero 简化分支
4 条 result store 到 R14 stack slot
RAX/RDX free-up prologue/epilogue
```

第四步：用解析结果实例化 summary：

```text
shape_id 命中 verified algorithmic lemma
operand_locs 满足 LayoutPre
result_sp 满足 LayoutPost
temp_reg_roles / rax_rdx_freeup / frame_touches 满足 frame condition
```

解析或实例化失败时 fail closed。`x86_bytes_hash` 只记录到 artifact，用于诊断和完整性校验。

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

### 5.2 结构化解析优先于 exact bytes 匹配

精确 bytes 匹配可以避免误用某条具体 lemma，但现实覆盖率很差：

```text
不同 sp -> R14 memory offset bytes 不同
不同 operand register -> instruction encoding 不同
不同 const operand value -> immediate bytes 不同
不同 RAX/RDX free-up -> prologue/epilogue bytes 不同
```

因此 v1 默认路线不应是 exact bytes hash，而应是结构化 slice 解析：

```text
解析成功:
  输出 parse_witness、shape_id、layout 参数、temp_reg_roles、rax_rdx_freeup、frame_touches
  用这些参数实例化 verified algorithmic lemma

解析失败:
  fail closed
```

这里的结构化解析不是“看起来像某个模板就直接放行”。parser 只提取 lemma 实例化参数；soundness 仍由 lemma precondition、frame condition 和 verifier 对 parser 输出的 replay/check 保证。

必须区分两种用法：

```text
禁止:
  仅凭 matcher 命中就把 slice 视为 verified

允许:
  结构化解析成功 -> 生成可复核参数 -> 实例化 verified lemma -> 检查失败则 fail closed
```

`x86_bytes_hash` 仍应记录在 artifact 中，但只用于完整性校验、诊断和回归定位，不作为主 proof cache key。

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

如果后续 Python 结构化恢复路线覆盖率不足，才考虑让 Go AOT 输出结构化 metadata。

metadata 不能进入 soundness 信任链。它最多用于：

```text
缩小候选 byte range
提升诊断信息
帮助定位 codegen 变化
提高 parser 覆盖率
```

verifier 即使拿到 metadata，也仍必须从真实 machine code 中解析 / replay / 检查：

```text
shape_id
operand_locs
result_sp
temp_reg_roles
rax_rdx_freeup
frame_touches
```

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
diagnostic_hints
```

其中 `diagnostic_hints` 可以包含 parser 辅助信息，例如：

```text
const_zero_decisions
source IR op index
expected opcode family
```

RAX/RDX free-up 信息不需要 Go AOT 输出语义化字段；Python parser 应直接从 slice 前后指令中识别 `none | spill_location_to_stack | save_to_temp_register`。metadata 只是提高覆盖率、诊断质量和维护性的后续选项。

## 6. 最小可执行里程碑

### Milestone 1：MUL algorithmic shape lemma

目标：

```text
定义 8 种 shape_id
完成 abstract holiman op chain
证明 abstract holiman op chain == Uint256.mul_semantics
证明 Uint256.mul_semantics == (x * y) mod 2^256
```

验收：

```text
L2/L3 proof 结果可缓存
proof 不依赖具体 x86 bytes / stack offset / register allocation
shape_id 与 q2/q3/q4 const-zero 组合一一对应
```

### Milestone 2：Python 结构化 MUL slice recovery

目标：

```text
输入 machine code + IR JSON
Python 能恢复 MUL 的 x86 byte range 和结构化参数
```

验收：

```text
不修改 Go AOT 编译器
恢复出 parse_witness / shape_id / operand_locs[8] / result_sp / temp_reg_roles / rax_rdx_freeup / frame_touches
verifier replay 能独立检查 parse_witness
shape_id 命中 verified algorithmic summary，或 fail closed
x86_bytes_hash 只用于 artifact 完整性校验和诊断
```

### Milestone 3：summary registry

目标：

```text
已证明 summary 可被全局验证器查询和应用
```

验收：

```text
未证明 summary 不可被静默使用
layout-parametric summary 的主 key 包含 shape_id / lemma_strategy / solver_version
具体 slice artifact 记录 x86_bytes_hash、layout、clobber、operand mapping
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
对 tests/data/muti_block_08.* 做 summary-based IR/x86 等价验证
```

验收：

```text
>= 80% IR ops 命中 verified summary
全局验证 wall-clock < 60s
SHA3 memory model 完成前，该 fixture 只作为条件验收，不作为阻塞硬门槛
```

### Milestone 6：可选 Go AOT metadata

目标：

```text
当 Python 结构化 slice recovery 覆盖率不足时，再让 Go AOT 输出 metadata
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

`MUL` 的困难不是偶然问题，而是提示我们必须引入 summary / lemma / cache 体系。真实 Go AOT `compileEVMMul` 是结构化、参数化的模板代码，不应当按随机 bytes 流处理。核心 cache 单位应是 8 种 `shape_id` 对应的 algorithmic lemma；具体 x86 slice 通过 Python 结构化解析抽取 layout、寄存器角色、RAX/RDX free-up 和 frame touch set，再实例化已证明的 summary。`x86_bytes_hash` 只用于完整性校验、诊断和 artifact 记录。compiler profile 和 Go AOT metadata 都只是后续覆盖率 / 诊断增强，不能替代 verifier 对真实 machine code 的解析和 fail-closed 检查。
