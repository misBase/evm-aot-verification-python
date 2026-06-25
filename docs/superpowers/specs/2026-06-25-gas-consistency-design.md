# Gas 消耗一致性验证 — 设计 spec

## Context

本项目用 Z3 证明 EVM IR 语义与编译后 x86-64 机器码语义等价。目标:新增 **gas 消耗
一致性**验证维度 —— 静态 gas、动态 gas、OOG/状态码,分阶段交付,边实现边 review。

验证锚点是 **x86 codegen 实际计算的 gas**(不是黄皮书)。详见记忆
`gas_codegen_split_host_vs_native`:x86 codegen 真实算 gas 的只有 ① 每 block 入口
`makeStaticUseGas(Block.StaticGas)`;② 内存扩展动态 gas(`makeUseGas` +
`memoryGasCost`)。SSTORE refund / CALL 63-64 转发 / SLOAD cost 全在 Go runtime host
function,当 UF 信任边界。

比较语义 = **终值逐路径等式**(同一符号 G,证 `evm_gas.Gas == callengine_gas_remaining`,
反例 `!=` 求 UNSAT)。A 强度:只验 gas 充足路径的终值等价,不验 OOG 路径正确性
(OOG/状态码留到最后阶段)。

## 阶段总览

- **阶段 0 — 静态 gas:✅ 已完成(651 passed)**。
- **阶段 1 — 内存扩展动态 gas**:第一版只 MSTORE+RETURN(mstore_return fixture),
  转正后逐指令扩 MLOAD/MSTORE8/SHA3/COPY 全系列/REVERT/MCOPY。
- **阶段 2 — CALL/CREATE returnGas 常量链**:host 调用前 ADDQ、后 SUBQ 镜像。
- **阶段 3 — OOG + 状态码一致性**:符号 gas 不剪 OOG 分支,验 out-of-gas 在哪个
  block/PC 触发、status code 两侧一致。host gas/refund UF 边界文档化。

## 阶段 0(已完成,只做回归保护)

- `SMTState.create_initial_state(symbolic_gas=False)` 默认具体常量 1000000000
  (OOG 分支不可达,保护功能等价验证);`symbolic_gas=True` 才用符号 G。
- `RefinementChecker/ProgramEquivalenceChecker(check_gas=False)` 默认关 gas 检查。
- gas 检查需显式 `check_gas=True` + `symbolic_gas=True` 双开关。
- 静态 gas 恒足用 `program_verifier` 层全局 `UGE(G, bound)`,bound = ∑static_gas ×
  max_iteration(500),fail-closed。**不改成逐扣减路径假设。**
- `_check_gas_equivalence`(`verification/refinement_gas.py`)接入 outputs/paths/
  instruction_refinement 三处 + 5 处 merged-result dict 加 gas 键。
- 详见记忆 `gas_stage0_dual_switch_design`。

## 阶段 1 — 内存扩展动态 gas(第一版:MSTORE + RETURN)

### 数据流(镜像 Go memoryGasCost 的 expansion branch)

```text
# requested size 按指令:MSTORE = offset+32;RETURN = If(length==0, 0, offset+length)
mem_words    = (requested + 31) >> 5                         # scope 下 ≤ 0xFFFFFFFF
rounded_size = mem_words << 5
square       = mem_words * mem_words                         # scope 下 < 2^64,高位=0
# 128-bit UDiv 对齐 div_bridge(否则 size=64 配不上 x86 size=128 → bit-blast):
quad         = Extract(63, 0, UDiv(ZeroExt(64, square), BitVecVal(512, 128)))
new_total    = mem_words * 3 + quad                          # MemoryGas=3, QuadCoeffDiv=512
expands      = UGT(rounded_size, callengine_memory_size_bytes)   # [R13+0x18] = mem.Len()
fee          = If(expands, new_total - callengine_memory_gas_used, 0)
callengine_memory_gas_used'   = If(expands, new_total, 旧值)      # [R13+0x20] = lastGasCost
callengine_memory_size_bytes' = If(expands, rounded_size, 旧值)   # [R13+0x18]
evm_gas'     = consume_dynamic(fee)
```

`mstore_return` 路线:MSTORE 先扩到 32B(扣 gas),RETURN 同范围**不再扩容**
(expands=False → cost=0)—— 验证 lastGasCost 增量机制正确。

### Key Changes

- **前置修复 `x86_64/go_function_semantics.py:855`**:`_handle_builtin_memory_grow`
  当前 `new_size_bytes = callengine_builtin_arg0 << 5` **错误**。Go
  `dealWithMemoryGrow` 直接 `targetMemSize := growNumber`(growNumber 是 native code
  写入 [R13+0x108] 的 rounded byte size)。改为 `new_size_bytes =
  callengine_builtin_arg0`(去掉 `<< 5`),同步更新 [R13+0x18]。否则首次扩容 32B 被
  记成 1024B,后续 expansion 判断全错 → 假 SAT。
- **新增 EVM memory gas helper**(`state/evm_gas_state.py` 或 evm_ir gas helper):
  实现上述数据流。128-bit UDiv 形态固定。
- **`evm_ir/semantics.py:761` MSTORE**:pop offset 后调 helper(requested=offset+32,
  在 store_256bit 前,镜像 x86 先算 gas 再 grow)。
- **`evm_ir/semantics.py:1273` RETURN**:requested = If(length==0,0,offset+length),
  调 helper(在设 return_offset 前)。
- offset 256→64-bit:scope assumption 保证高 192 位为 0(success-path,验证域缩小)。

### scope assumption(success-path,非无损先验,显式标注)

- `requested ≤ 0x1FFFFFFFE0` ⟹ `mem_words ≤ 0xFFFFFFFF` ⟹ `square < 2^64`;
- offset/length/`offset+length` 在 uint64 内无溢出。
- 这是被验证域的缩小,不是无损先验(memory overflow 区两侧同行为未验)。

### div_bridge 对齐

- EVM 侧 quad 用 `UDiv(ZeroExt(64,square), BitVecVal(512,128))` → `(udiv, 128)`。
- x86 侧 `div r64` 建模为 `UDiv(Concat(RDX,RAX), ZeroExt(64,divisor))` → `(udiv, 128)`。
- 两侧 key 交集 → `verified_div_bridges` 配对成功 → Z3 跳过 bit-blast。
- gas 检查 solver 前已有 `add_div_bridges`(阶段 0 已接),只需确认 gas 表达式里的
  `(udiv,128)` 被收集。

## 阶段 2 — CALL/CREATE returnGas 常量链

- `compileEVMDELEGATECALL/CALL/CREATE/CREATE2`:`returnGas = block.static_gas -
  op.immediate`(确定常量),host 调用前 `ADDQ returnGas` 加回、后 `SUBQ returnGas`。
- x86 侧 `add/sub [R13+0x70]` 已自动同步;EVM 侧用同一常量作用 evm_gas。
- host function 本身 gas/refund = UF 信任,不验。
- 防空证明:host 前后 gas-delta 用同名 UF `host_delta(pre_host_gas, ...)` 且约束
  `≤ pre_host_gas`(详见原计划修订点 9/17),使 returnGas 常量不前后抵消。

## 阶段 3 — OOG + 状态码一致性

- 符号 gas 下**不注入恒足假设**(或注入可变 bound),让 OOG 分支可达。
- 验证:out-of-gas 在哪个 block/PC 触发两侧一致 + `callengine_status_code` ==
  EVM 派生 status(STOP/RETURN/REVERT/OOG/underflow 映射到 aot_profile.status_codes)。
- EVM 侧需新增「派生 status」概念(终止类型 → status code)。
- 这是最严阶段,路径爆炸,用 terminal-paths 逐路径比;status 用等式语义。

## Test Plan

- 基线:`poetry run pytest -q` 全绿(阶段 0 保护)。
- 阶段 1 unit:memory grow builtin(输入 32 → [R13+0x18]==32 非 1024);memory gas
  helper(首次 32B cost=3,二次同范围 cost=0);div AST(EVM 二次项收集到 128-bit UDiv)。
- 阶段 1 integration:`mstore_return` 在 check_gas=True + symbolic_gas=True 通过;
  篡改 memory gas / grow size 被 mismatch 抓到(防假绿)。
- 每阶段:正向(UNSAT)+ 反向篡改(SAT)。
- 回归:`poetry run pytest tests/unit/test_gas_stage0_semantics.py
  tests/integration/test_gas_consistency_stage0.py` +
  `test_verify_mstore_return_program_pair`。

## Assumptions

- 阶段 0 已完成,只回归保护,不重构。
- 阶段 1 第一版只 MSTORE+RETURN / mstore_return。
- A 强度:OOG 路径正确性留到阶段 3。
- SSTORE/CALL host gas/refund 作 UF 信任边界,文档+注释标注。
