# Gas 消耗一致性验证设计

> 描述**当前代码的实际形态**。上一版按 2026-06-25 的实施 spec 写成，其模型（钳零扣减
> + 恒足假设 + 三个 state 开关）已被整体废弃；文末「模型演进」记录了废弃的原因，避免
> 有人照旧文档维护而把已修的问题装回去。

## 1. 目标与验证锚点

用 Z3 证明 EVM IR 语义与编译后 x86-64 机器码语义等价。gas 是在
storage/memory/returndata/status 之外的一个 observable 维度：证明同一初始 gas 下，
EVM 侧 `evm_gas.Gas` 与 x86 侧 `callengine_gas_remaining`（`[R13+0x70]`）在每条终止
路径上相等。

验证锚点是 **x86 codegen 实际计算的 gas**，不是黄皮书。go-hpc-evm 的 gas 分布在两处：

- **机器码可见**：① 每 block 入口 `makeStaticUseGas(Block.StaticGas)`；② 动态 gas
  （`checkMemoryAndCalcDynamicGas*` → `memoryGasCost` + word/copy/LOG data gas）；
  ③ CALL/CREATE 系列 host 调用前后的 `ADDQ/SUBQ returnGas`。
- **Go runtime 不可见**：SLOAD/SSTORE cost、SSTORE refund、CALL 63/64 转发、EXP 的
  `50*byteLen(exponent)` 等，全在 host/builtin function 内部。

可见部分做**真证明**，不可见部分用**同名 UF 相消**（§6）。

## 2. gas 状态语义无条件建模

**没有"关掉 gas 建模"这回事。** 静态/动态 gas 扣减、`lastGasCost` 与 memory size 的
bookkeeping、OOG 分叉，在所有模式下都执行。理由：gas 是决定控制流的内部状态（OOG
阈值），不是只在比较时才需要的 observable。曾经的 `gas_modeling_enabled` /
`oog_modeling_enabled` 能关掉本该无条件成立的东西，已删除。

功能等价验证之所以不受影响，靠的是**具体 gas 预算**：`ULT(budget, static_gas)` 一类
条件在 `simplify` 阶段直接折成 `False`，路径根本不建，连一次可达性查询都不用。

## 3. 模式与用法

`verification.GasCheck` 三值枚举，每个取值绑定一种初始 gas 配置：

| 模式 | 初始 gas | 比较 gas | 语义 |
| --- | --- | --- | --- |
| `OFF`（默认） | **必须具体** | 否 | 功能等价验证 |
| `FIXED_BUDGET` | **必须具体** | 是 | 「从这一个预算出发」的**单点**结论 |
| `FULL` | **必须符号** | 是 | 对所有初始 gas 量化，OOG 路径参与比较 |

```python
ProgramEquivalenceChecker(gas_check=GasCheck.FIXED_BUDGET).verify_program_pair(
    evm, x86, SMTState.create_initial_state(gas_budget=1_000_000), ...
)
```

CLI：`main.py --gas-check {off,fixed-budget,full} [--gas-budget N]`。

`FIXED_BUDGET` 与 `FULL` 的差别是「固定一个 gas 点」vs「量化所有 gas」，**不是**
「无 OOG 路径」vs「有 OOG 路径」：具体预算下依赖符号 offset 的动态 fee 仍可能超预算，
那类 OOG 分支照样保留；小预算下 OOG 条件甚至静态为真。

### `OFF` 的已知 under-approximation（**刻意保留**，条件性结论）

`OFF` 下 `host_gas_uf_enabled` 是关的，两侧都不扣 host cost `H`。模型里的 gas 因此比真实值
高一个 `H`，凡是依赖 gas 的行为——OOG 阈值（判的是 `S > G` 而非 `S > G-H`，漏掉
`S ≤ G < H+S` 这片真实可达区域）、`GAS` opcode 的取值、以及由二者派生的分支——探索到的都
是错误的路径集。方向上会假绿。

`OFF` 要求具体预算只是关掉了其中最明显的一类反例（符号 `G`），**没有消除缺口**：`H` 是
UF，`G=1e9, H=999999998, S=3` 就是具体预算下的反例——host 调用成功（`H ≤ G`），扣完剩 2，
下一步真实 OOG，而模型仍拿 `1e9` 去判。所以 `OFF` 的结论是**条件性**的，该前提由
`_annotate_gas_scope` 写进**每一条** `OFF` 的 VERIFIED 消息，不靠本文档口头声明。

**为什么不干脆所有模式都开 host UF**：`OFF` 的定位是最便宜的功能等价筛查，它根本不比较
gas，开 UF 对它零收益，却让每条路径都背上 UF 项、OOG 分支重新存活（合成 12 block + 1 个
SLOAD 实测：EVM 终止路径 1 → 12，候选 pair 1 → 144）。§7.2 那笔上界的钱花在真正比较 gas
的 `FIXED_BUDGET` / `FULL` 两档上。**需要关上这个缺口的调用方改用那两档即可**——这是取舍，
不是待办。

历史候选修法里，「给 host UF 加结构性上界」已按 §7.2 实施（但**只在比较 gas 的两档生效**）；
「`OFF` 遇 host op 一律拒绝」评估后否决——几乎所有真实合约都含 CALL/CREATE，会把功能等价
这条主线整个作废。

### 入口 fail-closed 守卫（`verify_program_pair`）

| 检查 | 拒绝条件 | 防的是 |
| --- | --- | --- |
| IR 不变量 | block 有 `static_gas` 但无 TAG | 无 TAG 则 OOG 守卫不存在而扣减照做 → gas 回绕静默继续 |
| 可验证范围 | 程序含未建模的动态 gas 指令（allowlist 差集，与模式无关，§8） | 两侧都漏扣 → 假绿 |
| 两侧同源（**所有模式**） | `simplify(evm_gas) != simplify(callengine_gas_remaining)` | 起点不同就不是在比同一个输入程序 |
| 模式匹配 | `OFF`+符号 / `FULL`+具体 / `FIXED_BUDGET`+符号 | 依次是：host gas 缺口张开；验的分支被折死；规模承诺失效 |

其中"具体"必须 **`simplify` 之后**判定：`is_bv_value` 只看语法形式，
`BitVecVal(1,64)+BitVecVal(2,64)` 语义上是 3 却返回 `False`，不化简会让 `FULL` 把
"语义具体"的 gas 当符号量接受，实际只验单点却声称量化全部。

`gas_check != OFF` 时 verifier **自己**置位 `host_gas_uf_enabled`（唯一写入方），并强制
`path_observations=True`——动态 gas 的 path-local assumption 在 merged-result 模式下会被
无条件 And 成全局条件，越界约束 sibling 路径（`failure_path_assumption_global_leak`）。

### 结论范围写进成功消息

库调用方只有 `verify_program_pair` 的返回 message，所以范围由 `_annotate_gas_scope`
写进去，不能只躺在文档里：

```
✓ VERIFIED: ... [gas equivalent for the fixed initial budget 777000;
host gas amounts are shared uninterpreted functions constrained by externally
audited upper bounds — the host gas formulas themselves are NOT proven here,
and host-exhaustion termination is out of scope]
```

OFF 的消息是**另一套**：它刻意不建模 host gas，所以要直说缺口并给出出路——

```
✓ VERIFIED: ... [functional equivalence at the fixed initial gas budget 555000;
host gas is NOT modeled in this mode, so the modelled gas runs high by the host cost
and any gas-dependent behaviour (out-of-gas thresholds, the GAS opcode's value, and
branches derived from either) is explored over the wrong path set — use
GasCheck.FIXED_BUDGET or FULL to close that gap]
```

比较 gas 的两档措辞不能写成"host 按协议扣数"——上界是对 go-hpc-evm 的人工审计所得，
是 assume 不是定理（§7.2）。

## 4. 比较语义

`verification/refinement_gas.py::GasEquivalenceChecks`（与 storage/transient 检查平级，
组合注入 `RefinementChecker` / `PathRefinementChecks` / `RefinementOutputChecks`）：

- 反例查询 `evm_gas != x86_gas`，`UNSAT` → 等价；`SAT` → 反例；`UNKNOWN` → **fail-closed**。
- **任一侧或两侧缺 gas 观测都 fail-closed**。走到这个 checker 就意味着 gas 检查已启用
  （`check_gas=False` 时 `_gas is None`，`RefinementOutputChecks` 直接跳过），所以"两侧
  都没有"不是"本次没建模 gas"，而是观测本该有却丢了——`_PATH_RESULT_KEYS` 漏键、并行
  worker 跨 Context 翻译丢失、aggregate fallback 掉字段，全是假绿路径。曾经这里是
  "两侧都无就 skip 成通过"。`PathObservation.gas` 另有必填约束，杜绝生产者静默省略。
- solver **无条件 reset**（不是 push/pop）。并行 worker 的私有 solver 在同一次
  `check_observables` 里已被前序子检查累积成 UNSAT 基底，只 push/pop 会让 gas 查询恒
  UNSAT → 假绿（曾真实发生，见 `gas_parallel_pathobs_false_green`）。
- 注入 `add_div_bridges`：两侧内存扩展二次项都含 128-bit UDiv，AST 形状不同，直接比较
  会 bit-blast 到 unknown。

status code 一致性**不在本模块**：由 `refinement_outputs._check_status_code_with_solver`
比较 EVM `error_code` 与 x86 `callengine_status_code`。

## 5. 静态 gas

- block 入口一次性扣 `Block.StaticGas`，镜像 `makeStaticUseGas` 的
  `SUBQ staticGas; MOVQ → [R13+0x70]`。编译期已把块内各指令静态 gas 求和成常量，故
  必须**按块扣、不能逐 opcode 扣**。
- `GAS` opcode 返回 `Blk.StaticGas - Immediate`（镜像 `compileEVMGAS`）。
- **`consume_static` 是纯减法，不钳零。** x86 在 `gas < staticGas` 时 JCS 跳 OOG
  handler、**根本不执行 SUBQ**——"gas 不足"是控制流分叉，不是把余额压成 0 继续跑。
  分叉由 `cfg_executor` 的 TAG 守卫负责，到得了减法这一步就意味着 gas 已足够。
- **OOG 分叉在 TAG 序言守卫内，是第一个错误分支**，条件 `ULT(gas, block.static_gas)`
  → `error_code = OUT_OF_GAS`。次序严格镜像 `compileEVMTag`（`impl_amd64.go:4230`）：
  `makeStaticUseGas` → MinDepth → MaxDepth，后一个条件都带上前面所有条件的否定。
  `test_oog_precedes_stack_underflow_in_tag_guard` 锁死这个次序。
- 因此有 IR 不变量：**有 `static_gas` 的 block 必须带 TAG**，否则守卫不存在而扣减照做。
  在 verifier 入口 fail-closed，**不放执行器**——合成 `EVMBlock` 驱动 `SymbolicExecutor`
  测裸 CFG 是合法用法，不该被打断。

`consume_dynamic` **仍然钳零**，但只剩 host UF 一个生产调用方（§6）与三个 test-only
封装在用。可见动态 gas 走 §6.1 的纯减法路径。

## 6. 动态 gas（可见部分，真证明）

### 6.1 统一入口 `semantics._charge_dynamic_gas`

对齐 `interpreter.go:187-209` 整段流程，一次调用产出**有序错误分支 + 正常路径演化**：

```text
memSize, ovf := operation.memorySize(stack)   // → E1..E3 / cap 分支
memorySize, ovf = SafeMul(toWordSize(memSize), 32)
dynamicCost = memFee + extra_fees             // 累加成总额
if err != nil || !contract.UseGas(dynamicCost) { return ErrOutOfGas }   // → E4
if memorySize > 0 { mem.Resize(memorySize) }  // 正常路径才扩容
```

三个要点：

1. **总额一次判断**。解释器 `UseGas(dynamicCost)` 与 x86 单个 `makeUseGas` 都只判一次；
   分成 memFee/wordFee 各判一次在 gas 不足时结论不同。
2. **gas 状态无条件演化**。连续两条动态 gas 指令、`G-f1 < f2 ≤ G` 时不扣 f1 就漏掉 AOT
   在第二条处的 OOG；`lastGasCost` 不更新则第二次按 `newTotal-0` 计费，阈值本身就错。
3. **正常路径是纯减法**。E4 已把不足分叉出去，此路径上钳零分支恒假。

E4 用 `UGT(total, gas)`（`total == gas` **不**触发），对齐 `UseGas` 的 `if gas < cost`。
E4 无条件建模——`makeUseGas` 的 CMPQ/JCS 是可见机器码，不能有开关；要让它不产生路径，
靠足够大的具体预算把条件 `simplify` 成 `False`。

### 6.2 错误分支与快照类

`_calc_mem_size_64`（镜像 Go `calcMemSize64`）按解释器的短路顺序产出分支，互斥化由
`cfg_executor._execute_op_with_outcome` 负责：

| 分支 | 条件 | 状态码 |
| --- | --- | --- |
| ① length 非 uint64 | `length_hi != 0` | 13 |
| ② length == 0 | 短路返回，**不检查 offset** | — |
| ③ offset 非 uint64 | `¬② ∧ offset_hi != 0` | 13 |
| ④ 进位 | `¬② ∧ end < offset` | 13 |
| SafeMul 溢出 | `requested > MaxUint64-31` | 13 |
| memoryGasCost cap | `requested > 0x1FFFFFFFE0` | **12**（经 `interpreter.go:205` 塌缩） |
| E4 dynamic OOG | `UGT(total_fee, gas)` | 12 |

② 是语义要点：`RETURN(offset=2^200, length=0)` 在解释器和 AOT 里都是正常路径、fee=0。
旧实现无条件 assume offset 高 192 位为 0，把这条合法路径排除在验证域外。

快照类决定错误瞬间哪些 side-channel 已写入，必须与 x86 的 exit 时刻一致：
`PRE_FEE`（三项都未写）用于所有 mem-size 分支；`POST_FEE`（只有 `lastGasCost` 已写）
用于 E4——`makeUseGas` 在 `memoryGasCost` 之后才跑，其 SUBQ 在 JCS 之后故 gas 不扣，
`memoryGrow` 更在 UseGas 之后故 mem_size 不变。

### 6.3 费用公式

纯计算函数（`state/evm_gas_state.py`）：`memory_expansion_fee` / `word_fee` / `log_fee`。
它们**不改 state、不注入 assumption**——写回哪几项由调用方决定，gas 错误分支的快照要求
各不相同。

```text
mem_words  = (requested + 31) >> 5
square     = mem_words * mem_words                       # 128-bit 表达
quad       = Extract(63, 0, UDiv(ZeroExt(64, square), 512_128))
new_total  = mem_words * 3 + quad                        # MemoryGas=3, QuadCoeffDiv=512
expands    = UGT(mem_words << 5, [R13+0x18])
fee        = If(expands, new_total - [R13+0x20], 0)
```

- **quad 必须用 128-bit UDiv**，才能让 div_bridge 以 `(udiv, 128)` 配上 x86 的
  `div r64`（dividend `Concat(RDX,RAX)` 是 128 位）。64-bit UDiv 配不上 → bit-blast → unknown。
- 扣减与字段更新**只在 `expands` 时发生**，避免连续内存操作过扣（`mstore_return` fixture
  正是验这个）。
- word gas：`words = (len+31)>>5; fee = words*const`。SHA3=6、COPY 系=3、
  CREATE=`InitCodeWordGas` 2、CREATE2=2+6。LOG data gas 按**字节**计费
  （`375 + n*375 + size*8`），不能复用 word 公式。
- 溢出健全性**依赖调用顺序**：调用点先经 cap 分支（`requested ≤ 0x1FFFFFFFE0`）加上
  `len ≤ requested`，才保证乘法不溢出、x86 `makeSafeMul` 的 overflow 分支恒假被剪。

`charge_memory_expansion_gas` / `charge_word_gas` / `charge_log_gas` 三个就地封装现在
**只剩单测在用**。`charge_memory_expansion_gas` 里那条 `ULE(requested, 0x1FFFFFFFE0)`
会静默缩小验证域，是脚手架残留——生产路径已改用 §6.2 的 cap 分支（真建 OOG 终态），
**别在新代码里调用它们**。

### 6.4 覆盖的指令与调用点次序

MLOAD / MSTORE / MSTORE8（`calcMemSize64WithUint`）、RETURN / REVERT、SHA3（+6）、
CALLDATACOPY / CODECOPY / RETURNDATACOPY / MCOPY / EXTCODECOPY（+3）、LOG0..LOG4、
CREATE（+2）/ CREATE2（+8）。

扣费点相对副作用与弹栈的位置必须对齐 codegen，否则错误终态的 observable 与 x86 的
exit 时刻错位：

- MSTORE / LOG / RETURN：gas 前言早于 `popUint256`，故快照里参数**仍在栈上**。
- RETURNDATACOPY：gas 前言（`impl_amd64.go:3124`）在 pop 之前，errPoint（`:3143+`）在
  pop 之后 —— 两组分支的快照点不同，不能共用。
- MCOPY 的 `mStart = max(dest, source)` 必须在 **256 位**上比：x86
  `compileSubValuesForCompare` 是全 256 位借位链，先截 64 位会让 `dst=2^200/src=0` 误选。
- CREATE/CREATE2 严格四段：`dealWithAddGas → 可见 fee → host UF → dealWithSubGas`。
  可见 fee 落在 add/sub 窗口**之内**，顺序错了 gas 终值虽相同（加减相消）但 OOG 阈值会
  少算一个 returnGas。

### 6.5 前置修复：builtin memory grow

`go_function_semantics._handle_builtin_memory_grow` 原本 `arg0 << 5` 是错的：Go
`dealWithMemoryGrow` 直接 `targetMemSize := growNumber`，native code 写入 `[R13+0x108]`
的已是 rounded byte size。不修则首次扩容 32B 被记成 1024B，后续 expansion 判断全错。
修复**无条件生效**（曾有个 gas-off 分支保留旧的 `<<5`，那会让 x86 的 `[R13+0x18]` 与
EVM 侧 bookkeeping 分叉）。同时按 `if targetMemSize > memLen` 只增不减。

## 7. host/builtin gas UF（`state/host_gas.py`）

x86 机器码里没有这段 gas 指令，就没有对照对象。做法：建成同名 UF
`host_gas_<opcode>(*stack_args)`，两侧在各自调用点各扣同一个 UF，Z3 中同名同参求值到同
一符号，比较时相消，只留下两侧可见的 gas 做真实比较。带 access-list 依赖的指令还会多吃
一个**调用序号**参数（§7.1）。

- 覆盖 `HOST_GAS_HOST_KINDS`（SLOAD/SSTORE/BALANCE/EXTCODESIZE/EXTCODEHASH/EXTCODECOPY/
  SELFDESTRUCT/CALL 四件套/CREATE 两件套）+ `HOST_GAS_BUILTIN_KINDS`（EXP）。
- 参数必须承载**完整 256 位**（`_normalize_uf_arg`）。截到低 64 位会让仅高 192 位不同的
  栈值产出恒等 UF；对 EXP（gas 真依赖完整 exponent）这类指令，高位传错的 codegen bug 会
  同时逃过 gas 检查与功能检查。非 64/256 位宽度 fail-closed 抛错。
- **CALL 系的 returnGas 链**（`charge_host_gas_uf_with_return_gas`）：x86 在 host 调用
  前后对 `[R13+0x70]` 做 plain `ADD/SUB returnGas`，host gas 夹在中间。EVM 侧三段必须
  严格对齐，否则两侧 gas 差一个 returnGas ⟹ clamp 实参不同 ⟹ UF 不相消 ⟹ 假 SAT。
  CREATE 系不能用这个打包函数（窗口内还有可见 fee，见 §6.4）。
- x86 侧 `deduct_host_gas_uf_x86` 的 `_consume_clamp_64` 必须与
  `EVMGasState.consume_dynamic` **逐字一致**，两侧表达式同构才能相消。

**强度边界**：证的是「两侧扣了同一个 gas、传给 host 的栈参数一致」——能抓参数传错、
次序错位、漏扣的 codegen bug；**不是** host gas 公式本身正确。后者是 assume。

### 7.1 调用序号：把 access-list 依赖搬进 UF 签名

Z3 的 `Function` 是纯函数，同参必然同值。而 AOT 的 SLOAD host 函数
（`evm/host.go:71` `SLoad`）**不是**——它读 `SlotInAccessList` 并且**自己修改**它：

```go
if _, slotPresent := ...SlotInAccessList(addr, slot); !slotPresent {
    ...AddSlotToAccessList(addr, slot)          // 副作用
    return params.ColdSloadCostEIP2929, nil     // 2100
}
return params.WarmStorageReadCostEIP2929, nil   // 100
```

同一个 slot 读两次真实是 `(2100, 100)`，而不带序号的模型只能表示 `(c, c)` ——真实执行
走过的中间状态 `G−2100` 在**任何** UF 赋值下都不存在，验证域少了一片真实可达的 gas 轨迹
（gas 参与控制流，OOG 分叉的阈值判断就落在这些中间状态上）。

做法：给 `HOST_GAS_SEQ_KINDS` 里的指令在 UF 末尾追加一个**调用序号**参数，
`host_gas_sload(key)` → `host_gas_sload(key, seq)`。序号取自
`SMTState.host_gas_seq`，递增规则集中在 `host_gas.next_host_gas_seq`（两侧共用，分开写
迟早漂移）。

几个要点：

- **序号是 Z3 的 256-bit BitVec，不是 Python int**。x86 合流点合并后它可以是
  `If(cond, 1, 0)`；此时相消靠 EUF congruence（参数相等 ⟹ 函数值相等）而非语法同一。
  合并在 `_merge_at_confluence` 里按与 `evm_storage` 相同的 If-chain 范式处理，**必须
  带 `simplify`**——Z3 不会自动把 `If(c,1,1)` 折成 `1`，不折就会在每个合流点堆一层。
- **按 opcode 计数，不按 (opcode, key)**：key 是符号量，建模期无法判断 `k1 == k2`。
  粗划分只增加自由度，两种真实情况都能表示（同 key `(2100,100)` 与不同 key
  `(2100,2100)`）。
- **漏传序号 fail-closed**：`host_gas_uf` 对 `HOST_GAS_SEQ_KINDS` 里的指令强制要求
  `seq`。漏传会生成**一元** UF——Z3 里 arity 不同就是另一个函数符号，两侧都误用旧接口时
  照样相消、序号机制静默失效而测试全绿，那是真实的假绿路径。
- SSTORE 除序号外还吃 slot 的**写入前**值（`host.go:255` 的档位取决于 current 值）。
  两侧都必须在 `sstore` 之前取，写完再取只会拿回 `val` 本身。

**收录判据**是「**该 opcode 的 AOT host 函数**是否读写 access list」，逐条核对过
`evm/host.go`（不是 `gas_table.go`，理由见 §7.2 的警告）。明确**不收**的三个：

| opcode | 为什么不加 |
| --- | --- |
| SELFDESTRUCT | `host.go:328` `Suicide` 整个函数不扣 gas、不碰 access list |
| EXP | `engine_evm.go:785` `aotGasExpEIP158` 是 exponent 的纯函数，加序号只会丢掉「同参必同价」这条正确信息 |
| CREATE / CREATE2 | `host.go:361/398` 只做 `GetRemainingGas → gas−gas/64 → UseGas`，全函数不碰 access list |

**仍未覆盖的隐藏依赖**：CALL 系的 63/64 转发与 CREATE/CREATE2 的
`GetRemainingGas`（`evm/host.go:369/406` 的 `gas -= gas/64`）取决于 gas 的**具体数值**
而非调用次序，序号代理不了。要表达它们得把 `gas_before` 加进 UF 签名——那是独立的一件
事，且**与「给 UF 加协议上界」不是同一件事**：加参数修的是 UF identity 缺 gas 状态，
加上界（注入 `ULE(...)` 之类）才是剪枝，后者需要前者但不会由前者自动产生。

**强度边界的变化**：约束从「同参必同价」松成「同参 + 同次序必同价」。这是**放松**，
方向安全（自由度只增不减），代价是不再断言"两次同参调用等价"。

⚠️ 序号是**动态调用事件的区分符**，不是 access list 的状态模型：它只保证不同次调用
*可以*取不同值，不表达"第一次必 cold、之后必 warm"（真实冷热还取决于同一 key 在别处
是否已被访问、跨分支的访问历史，都没建模）。别把它写成"建模了 EIP-2929"。

**顺带收益（有限）**：两侧 host 调用序列若在数量或次序上偏移，序号就对不上 → UF 不相消
→ SAT。所以 `call_site_mapping` 的顺序假设从完全静默变成**部分**可检测——但它抓不住
「opcode、参数、动态序号三者都相同的两个站点互换」，那种情况 UF 照样相消。

### 7.2 协议上界：把 host UF 从"无约束"收到"不超过审计所得的上限"

host UF 原本是完全自由的函数，于是一旦扣 H，后继 block 的 `ULT(gas, static_gas)` 就再也
折不掉，OOG 分支全部存活、路径爆炸——这正是 `muti_block` 开 gas 后 x86 终止路径 30→102+
的来源。

做法：给写得出健全上界的 opcode 加 `ULE(H, bound)`，两侧在各自扣费点同时加。

**只在 FIXED_BUDGET / FULL 生效。** `GasCheck.OFF` 不开 host UF，因此也不产生上界：它的
定位是最便宜的功能等价筛查、根本不比较 gas，开 UF 对它零收益却让每条路径都背上 UF 项。
OFF 因此保留一个**已披露**的缺口（判 `S > G` 而非 `S > G-H`），由成功消息如实声明并指向
另两档——这是刻意取舍，不是待办。

上界表在 `state/host_gas.HOST_GAS_UPPER_BOUNDS`：

| opcode | 实测静态 gas | host 动态上界 |
| --- | --- | --- |
| SELFDESTRUCT | 0 | `host.go:328` `Suicide` 不扣 gas；上界 0 在无符号下就等价于 `cost == 0` |
| SLOAD | 0 | 2100（`ColdSloadCostEIP2929`） |
| SSTORE | 0 | 22100（cold 2100 + `SstoreSetGasEIP2200` 20000） |
| BALANCE / EXTCODESIZE / EXTCODEHASH / EXTCODECOPY | 100 | 2500（`ColdAccountAccessCost − WarmStorageReadCost`；warm 那 100 已在 static gas） |
| EXP | 0 | 1610（`ExpGas 10 + ExpByteEIP158 50 × byteLen`，`byteLen ≤ 32`） |
| CALL 四件套 / CREATE / CREATE2 | — | **写不出可剪枝的小常量上界** |

"实测静态 gas"来自 fixture IR 的 `static_gas` 减去 PUSH 份额——锚点是 AOT 实际发射了
什么，不是 geth 的 jump table。

CALL 系无界的原因（按 AOT 实际执行的 `evm/host.go` 记）：`host.go:809` 先收
cold−warm(2500)，再转 `host.go:741` 的 `gasCostWithHostCall`，那里累加三项——
`CallNewAccountGas`(25000, `protocol_params.go:43`)、内存扩展(`memoryGasCostCopy`,
`host.go:847`)、63/64 转发额度。头一项是常数，后两项无界：AOT **没有**
`checkMemoryAndCalcDynamicGasCall`（`impl_amd64.go` 只为 Sha3/CallDataCopy/CodeCopy/
ExtCodeCopy/ReturnDataCopy/MLoad/MStore/MStore8/MCopy/Log/Create/Create2 发射可见 fee），
所以内存扩展的二次项整个在 host 内、我们侧没有对应项可减。CREATE/CREATE2 则是
`host.go:361/398` 的 `GetRemainingGas → gas − gas/64 → UseGas`。
这些 opcode **照扣不误**——扣一个无约束 UF 仍然健全，只是它们的 OOG 分支不被剪。

`HOST_GAS_UNBOUNDED_KINDS` 由上界表**派生**（`HOST_GAS_UF_KINDS - 上界表的键`），新增
host opcode 却忘了写上界时会自动落进该集合而不是被静默当成有界。

**注入通道**：上界在执行期才产生（term 到执行 host op 时才存在），走不了
`initial_state.assumptions` 那条只在入口生效的路。改由 semantics 层挂进
`SMTState.pending_constraints`，executor 消费后并入**当前路径**的 `world_state.constraints`
——与 `pending_errors` 同范式，未消费会 fail-closed。因为上界只提及 term 自身的参数，它是
全局事实而非 path-local，中途并入不会越界约束 sibling。

⚠️ **上界是 assume，不是定理。** 写小了会静默缩域：两侧仍共享同一个 UF、仍相消、仍
UNSAT，被排除的真实轨迹在 Python 侧**没有任何测试看得见**。所以：

- Python 侧的测试只能证明"上界确实接进了求解、两侧 wiring 一致、drain 没漏"，**证不了
  数值**（`tests/unit/test_host_gas_bounds.py`）；
- 数值**没有可执行的 oracle**：跨仓库放验证测试的维护成本高于它挡住的风险。代之以逐条
  记 provenance —— 每条上界取自哪个 Go 函数的哪条分支、常量在
  `params/protocol_params.go` 哪一行，全写在 `HOST_GAS_UPPER_BOUNDS` 的注释里，照行号
  读源码即可复核；
- ⚠️ **依据必须取 AOT 实际执行的实现，即 `evm/host.go` 与 `evm/aot/*`**。
  `evm/gas_table.go` 是**解释器**的 gas 表，AOT 从不调用；两边目前数值一致纯属巧合，
  照它复核会验错对象（本表初版就引错了源文件）；
- **没有机器防线，也没有自动提醒**：曾有一条比对本地 go-hpc-evm HEAD 的 revision pin，
  已删——它绑错了对象（本地工作区状态与"产出这批签入 fixture 的编译器版本"没有因果关系）
  且信噪比为负。理由与替代流程见 `docs/关键问题记录.md` #20；上次复核参照的版本记在
  `tests/data/README.md`；
- 结论措辞只能说到"受外部审计所得上界约束"，不能写"按协议扣数"。

### host gas 耗尽后的终止：不在范围内，也不是缺口

两侧都钳零续跑、都不分叉，而 UF 是无约束自由函数（`cost > gas` 永远可满足），于是模型里
有一批真实执行不存在的"扣爆后带 gas=0 继续跑"路径。这不构成缺口：

- **那一处没有生成代码可验。** `compileCallGoFunction`（`impl_amd64.go:323-338`）只发射
  spill / 写 returnAddress / 写 status / 写 SP / RET，返回地址处**不检查** host 结果；
  要不要重入完全由 Go 循环决定（`engine_evm.go:657` `if err != nil { return nil, err }`）。
  没有 x86 行为可以与 IR「不一致」。
- **方向是保守的。** 那些续跑状态是机器码的**不可达**状态，在其上比较是多验不是少验，
  只可能误报、不可能假绿；两侧带同一钳零值继续走，下游可见 gas 检查照常逐路径比较。
- 该调用点仅有的 codegen 已在存在的那条路径上验过（UF 只有两侧栈参数一致才相消）。

与 `evm_ir/semantics.py` 对**写保护**的既有判断同源（同样是 Go error 终止、不回写
native status）。作为 host-success 路径的 over-approximation，它可能引入额外路径造成假
阴性，但不会因省略真实 host-success 路径而假阳性——前提是结论明确限定为"不证明 host
exhaustion 分支"，这一条已写进成功消息（§3）。

## 8. 可验证范围守卫（allowlist）

`_find_unsupported_dynamic_gas_ops` 拒绝的是**「需要 gas 建模」减去「已建模」**：

```python
reject = (_DYNAMIC_GAS_KINDS - _MODELED_DYNAMIC_GAS_KINDS) | _MANUAL_REJECT_KINDS
```

| 集合 | 含义 | 当前内容 |
| --- | --- | --- |
| `_DYNAMIC_GAS_KINDS` | 协议层面需要额外 gas 建模的 IR kind 全表 | 25 项（见下） |
| `_MODELED_DYNAMIC_GAS_KINDS` | 真证明集 ∪ `HOST_GAS_UF_KINDS` | 与全表相等 |
| `_MANUAL_REJECT_KINDS` | 人工钩子：临时挡下某个已建模的 kind | **空** |

**为什么是 allowlist 而不是黑名单**：黑名单（本文件的历史形态）意味着新增或漏建模的
动态 gas 指令默认放行——两侧都漏扣就是假绿，且只能靠有人记得手工登记。allowlist 下
只要指令登记进 `_DYNAMIC_GAS_KINDS` 而没接建模，就会自动被拦下。差集为空是不变量，
由 `test_dynamic_gas_allowlist_has_no_gap` 守着（含反向：已建模集不得溢出全表，否则
说明全表漏登记，那才是真正的 fail-open）。

**`_DYNAMIC_GAS_KINDS` 的抽取口径**（改动时按这个重新核对 `evm/jump_table.go`）——
带动态 gas 的全部条目，**两种语法形式都要看**：

1. struct literal 里的 `dynamicGas:` 字段（25 处）：EXP / SHA3 / CALLDATACOPY /
   CODECOPY / EXTCODECOPY / MLOAD / MSTORE / MSTORE8 / SSTORE / LOG0-4 / CREATE /
   CALL / CALLCODE / RETURN / SELFDESTRUCT，以及 EIP 覆盖区的 MCOPY / CREATE2 /
   STATICCALL / RETURNDATACOPY / REVERT / DELEGATECALL。
2. **`instructionSet[common.X].dynamicGas = f` 的赋值形式**（`jump_table.go:142-155`，
   `enable2929`）：SLOAD / BALANCE / EXTCODESIZE / EXTCODEHASH。这一形式
   `grep "dynamicGas:"` 抓不到，实际漏抽过一次。

LOG0..LOG4 映射到 IR kind 统一是 `"LOG"`（topic 数在 `op.immediate`）。取超集是安全的：
多列一个 kind 只会多拒（fail-closed），不会假绿。

### EXTCODECOPY / CREATE / CREATE2 的解禁（曾长期 fail-closed）

三者的可见 fee 一直是建了的（`memoryCreate{,2}GasN` / `memoryCopierGas(3)`），拒绝理由
是另外两条，现均已消解：

- **缺专用 fixture** → 已补：`gas_create`（size=0x20/offset=0x40/value=7）、
  `gas_create_returngas`（returnGas=13）、`gas_create2`（salt=0x7b）、`gas_extcodecopy`
  （size=4/offset=7/destOffset=0x20/addr=1）。操作数取互不相同的可辨识值——旧
  `gas_create` 三个操作数全 0 且 `size==0`，内存扩展 fee 与 word gas 双双为 0，既掩盖
  槽位交换也掩盖 UF 参数顺序错误。
- **`MAX_INIT_CODE_SIZE_EXCEEDED`(16) 两侧行为未核对** → 已核对：**amd64 codegen 根本
  不产生这个状态码**。`evmNativeCallStatusMaxInitCodeSizeExceeded` 在 `evm/aot` 全包只
  出现于 `engine_evm.go:260`（枚举）与 `:280`（error 映射）；`memoryGasCreate`
  （`gas_dynamic_amd64.go:437-461`）里那句 `// check if codeSize > params.MaxInitCodeSize`
  注释**下面没有任何比较指令**。它与 host gas 耗尽同类：Go host 内 error 终止、不回写
  native status，没有 x86 行为可以不一致（论证见 §7 与 `state/host_gas.py`）。

`HOST_GAS_UF_KINDS` 算已建模（含 `FULL`）：按本项目口径
（`docs/关键问题记录.md` #19，目标是 IR↔AOT 而非 IR↔解释器），host gas 耗尽那一处没有生成
代码，没有 x86 行为可以不一致；结论范围由成功消息声明（§3）而非由拒绝承担。`FULL` 曾额外
拒绝它们，已删除，回归证据见 `test_gas_consistency_host_uf.py` 的 `*_under_full` 用例
（`gas_sload` / `gas_exp` / `gas_call_returngas` 三条接线的正向 + 篡改 UF opcode 的 SAT）。

其它已知边界：

1. **host gas 公式本身是 assume**（§7 强度边界）；SSTORE refund、CALL 63/64 转发同理。
2. **`FIXED_BUDGET` 是单点结论**。tamper 测试全绿只说明该预算下检查有牙，不等于其它预算
   下也成立；只在临界预算附近出现的差异不被覆盖。要量化所有 gas 用 `FULL`。
3. **`OFF` 是条件性结论，不是 fail-closed 修复**（§3）。它不建模 host gas，OOG 阈值短
   一个 `ΣH`；要求具体预算只关掉了符号 `G` 那一类反例，具体预算下仍有反例。前提写在每条
   VERIFIED 消息里。
4. **执行期 assumption 的域收缩不可见**。`_path_observation` 把 `state.assumptions` And
   进各路径 condition，而 `coverage_precondition` 只拿得到 `initial_state.assumptions`；
   叠加 `_check_path_coverage` 在 `coverage.complete` 时短路，执行期加的假设会静默缩小
   验证域。这是既有隐患（现有 CALLDATALOAD hi-192==0 等假设同样受影响），修法是给
   `PathObservation` 加独立 `precondition` 字段。**因此不要用执行期 assumption 表达 gas
   前提**——gas 假设只能写在初始共享符号上。

## 9. 测试矩阵

Gas 主验收命令：

```bash
poetry run pytest tests/unit/*gas* tests/integration/*gas* -q
```

预期无非预期失败；有意标记为 skip 的用例由测试自身的 `reason` 说明范围与启用条件。
不在文档中固化 passed/skipped 数量或耗时，避免正常的测试增减与机器性能差异造成陈旧信息。

- `test_gas_consistency_stage0.py` — 静态 gas 正向 + 篡改 static gas 被抓。
- `test_gas_consistency_stage1.py` — mstore_return / mload / sha3 / calldatacopy /
  codecopy / mcopy / mstore8 / revert / log1 正向 + 逐项篡改（memory gas、word gas、
  LOG flat/topic/data gas）+ 并行 path-observations 正反向。
- `test_gas_consistency_host_uf.py` — 13 类 host/builtin 正向 + 篡改 opcode 名 / 参数
  次序 / 漏扣 x86 侧 / 篡改 returnGas + 并行正反向；另含 CREATE/CREATE2/EXTCODECOPY
  这一组「可见 fee + host UF 混合」的正向（FIXED_BUDGET × FULL 双模式）、四条篡改
  （InitCodeWordGas 2→9 / CREATE2 word 8→2 / copy word 3→9 / returnGas +1）与三条
  **可达性**用例（见下）；调用序号（§7.1）另有 `gas_sload_same_key` 双模式正向、
  cold/warm 轨迹可满足性（含一元 UF 对照组必须 UNSAT）、序号递增与 per-path 隔离、
  x86 单侧序号偏移（workers 1/2 × enable_merge）、EVM 单侧序号冻结、
  `HOST_GAS_SEQ_KINDS` 精确集合锁定，以及 SSTORE old_val 取错时机篡改。
- `test_host_gas_seq_merge.py` — 合流点分歧合并：一支执行过 SLOAD、一支没有时序号合成
  `If(cond,1,0)`，合流后两支继续各自递增；序号相同时折成常量（验 `simplify` 没漏）。
  这条路径**现有 fixture 覆盖不到**（实测 perf_erc20_lite 143 次合并只有 6 次多路径，
  且那 6 次两支 gas 逐位相同），只能直接构造状态测合并逻辑。
- `test_gas_consistency_stage3.py` — status code 逐终止路径一致 + OOG 路径 status 一致
  + TAG 守卫次序 + 四类入口 fail-closed（模式-gas 错配双向、两侧初始 gas 不一致、
  可折叠为常量的 gas）+ 成功消息带范围 + 并行跨 context。
- `test_gas_error_codes.py` — `calcMemSize64` 各错误分支、快照类、returnGas 窗口。
- `test_gas_verifier_stage0_guard.py` — allowlist 三集合（差集为空的不变量、摘掉某个
  已建模 kind 后立刻被拒、人工钩子仍生效）、IR 不变量正负例、CLI 参数、枚举归一化。
- `test_gas_consistency_contracts.py` — 真实完整合约规模（见下节）。

**每个 gas 能力都配一条反向篡改测试**（篡改后必须 SAT/失败）。这是本维度防假绿的主要
手段，新增 gas 建模时必须同时补篡改用例。篡改用例的断言要落到
`COUNTEREXAMPLE FOUND` + `<observable> differs` 上——只断言 `not verified` 或
`"gas" in msg` 的话，配置拒绝、scope 守卫拒绝、超时都能让它变绿。

**正例还要防 vacuous**：`*_visible_fee_actually_charged` 在 EVM 侧扣费入口装计数器，
确认符号执行真的走到了该指令并钉死其 word gas 常量（CREATE=2 / CREATE2=8 /
EXTCODECOPY=3）。「VERIFIED」本身不排除「这条指令压根没被执行到」——路径被剪掉时两侧
同样不扣，gas 照样相等。

### 9.0 fixture 与生成器

`tests/data/gas_*.{json,hex}` 由 go-hpc-evm `evm/aot` 包内的 `TestGenGasFixtures` 产出
（`GOARCH=amd64 go test -run TestGenGasFixtures`），绑定 go-hpc-evm commit `b3ddbdb`；
用法、GOARCH 陷阱与每条覆盖点见 `tests/data/README.md`。

CREATE 系新增的 fixture（操作数取互不相同的可辨识值）：

| fixture | 操作数 | 覆盖点 |
| --- | --- | --- |
| `gas_create` | size=0x20, offset=0x40, value=7 | 内存扩展 + `InitCodeWordGas`(2)，returnGas=0 |
| `gas_create_returngas` | 同上 + 尾部 POP/PUSH/ADD | **returnGas=13**：可见 fee 落在 add/sub 窗口内 |
| `gas_create2` | salt=0x7b, size=0x20, offset=0x40, value=7 | `CREATE2_WORD_GAS`(8) 与 CREATE(2) 的区分 |
| `gas_extcodecopy` | size=4, offset=7, destOffset=0x20, addr=1 | `calcMemSize64(Back(1),Back(3))` 槽位 + `CopyGas`(3) |
| `gas_create_sym` / `gas_extcodecopy_sym` | size/offset 来自 CALLDATALOAD | 符号边界，**当前 skip**（见 9.2） |
| `gas_sload_same_key` | 两次 `SLOAD(0x07)` | 调用序号（§7.1）：同 slot 读两次的 cold→warm 轨迹。现有 `gas_two_sload` 用的是两个**不同** key，验不到这条 |

### 9.1 合约级端到端覆盖

上面各 stage 的被验对象都是单指令级或极小 fixture。`test_gas_consistency_contracts.py`
是 gas 检查在真实合约规模上的覆盖——三类 gas（静态 / 可见动态 / host UF）在同一程序里
混合、完整 dispatcher、多条 RETURN/REVERT 终止路径：

| fixture（规模） | 模式 | 耗时 | 路径 EVM/x86 |
| --- | --- | --- | --- |
| perf_erc20_lite（13 block，全符号 calldata） | FIXED_BUDGET | 8.7s | 7 / 8 |
| perf_erc20_lite | FULL | 12.7s | 24 / 29 |
| CErc20 `decimals()`（723 block） | FIXED_BUDGET | 4.9s | 5 / 5 |
| CErc20 `decimals()` | FULL | 7.6s | 18 / 18 |
| ENSRegistry `owner(bytes32)`（127 block） | FIXED_BUDGET | 9.3s | 11 / 11 |

配套反向用例：篡改入口 block `static_gas`（+1）、篡改 x86 侧 SLOAD 的 host UF opcode、
`perf_erc20_lite_bug.hex` 的 SBB→SUB 功能 bug（确认新增的 OOG 分支与 path-local
assumption 没有把功能反例约束掉）。

Safe 曾是「拒绝集在真实合约上生效」的证据；EXTCODECOPY 解禁后该用例反转为断言它
**不再**被 scope 守卫拒绝。Safe 的全合约端到端验证仍未跑通（无 selector 约束时 742
block 的 dispatcher 撑开路径，实测 >6.5min 停在符号执行阶段），已 `@pytest.mark.skip`
并注明启用条件。**这不是 EXTCODECOPY 解禁引入的**——Safe 在本仓库从来没有任何端到端
覆盖，连 `GasCheck.OFF` 的功能等价测试都不存在。EXTCODECOPY 自身的 gas 覆盖由
`gas_extcodecopy` fixture 承担，其可达性由 spy 计数坐实（§9）。

**关于路径膨胀**：`GasCheck` 的注释预警过，开 gas 会打开 host gas UF，使后继 block 的
`ULT(gas, static_gas)` 折不掉、OOG 分支全部存活（合成 12 block + 1 SLOAD 实测 EVM 终止
路径 1→12、候选 pair 1→144）。上表是大合约上的实测：**膨胀远小于该量级**，723 block 的
CErc20 在 FULL 下仍是 7.6s，决定规模的是输入形态而非 block 数。

曾经的例外 `muti_block`（40 block，符号 calldatasize + `abstract_calldataload_words`）
**已由 §7.2 的协议上界解决**：它的输入形态本就撑开路径，再乘 OOG 分支后 x86 终止路径从
30 涨到 102+，>25min 仍停在 pair feasibility；加上界后实测 **41s / 16 EVM × 30 x86 路径
/ 30 个可行 pair**，路径数回到与 `OFF` 相同的 30，`@pytest.mark.skip` 已移除。这条用例
现在同时是"上界确实在剪枝"的端到端凭证——单元测试只能证明约束进了求解器，压不出这个
量级的差别。

⚠️ 顺带暴露的一件事：路径规模下来后瓶颈换成了 **AST 遍历的递归深度**——
`common/div_bridge.collect_div_subexprs` 原是递归 walker，而这里的表达式上千层嵌套，在
Python 默认上限 1000 处抛 `RecursionError`（还报在 `Z3_func_decl_to_ast` 这种看不出根因
的地方）。

一度用 `tests/conftest.py` 调高 `recursionlimit` 顶过去——**那是错的**：只盖住 pytest，
CLI 与库调用方照样崩。已改成显式栈迭代，回归测试
`test_collect_handles_deeper_nesting_than_python_recursion_limit` 刻意跑在默认上限上；
pytest 外直接调用 muti_block 实测 46.3s 通过。

### 9.2 符号操作数 fixture

`gas_create_sym` / `gas_extcodecopy_sym`（size/offset 来自 `CALLDATALOAD`）把
`memoryGasCost` 的 cap 支、`makeSafeMul`/`SafeAdd` 的溢出支与动态 OOG 推到**端到端**
层面真实可达——常量 fixture 只能证明正常路径。这是这些错误分支**唯一的 IR↔x86 对照**
（`test_gas_error_codes.py` 那组是 EVM 侧单测，没有 x86 侧对照）。

**跑得动依赖一套特定配置，缺一不可**（`_SYMBOLIC_KWARGS` +
`_verify_symbolic`）：

| 配置项 | 作用 | 少了会怎样 |
| --- | --- | --- |
| `abstract_calldataload_words` **+** `summary_config` | 两侧 CALLDATALOAD 都走抽象 | **必须成对**。抽象在 EVM 侧无条件生效（`semantics.py`），x86 侧只在 CALLDATALOAD summary 里生效（`x86_64/summaries/calldataload.py`）。只开抽象不给 summary_config → 两侧取值不同 → 1.2s 就"抓到"一个 status code 反例，**那是配置不对称造成的假反例** |
| `enable_merge=False` + `x86_reachability_timeout_ms=250` | 把 x86 终止路径 17→8 | 不加时 7×17=119 对 pair，实测 >40min 未完成；`skip_feasibility=True` 也救不回来 |
| 固定 `calldata_size_bytes` | 去掉符号 calldatasize 那一层 | 路径再乘一层 |

不加这套配置时**瓶颈不是求解不动**：逐对 verbose 显示每对的 status / memory / storage /
gas 检查都是毫秒级 `unsat` 且**无一 unknown**，时间花在每对约 6s 的固定开销上
（pair feasibility 预筛占大头）。与 `muti_block` 是同一个规模问题。

实测结果：

| fixture | 模式 | 结果 |
| --- | --- | --- |
| `gas_create_sym` | FIXED_BUDGET | ✅ ~12s |
| `gas_extcodecopy_sym` | FIXED_BUDGET | ✅ ~62s |
| `gas_create_sym` | FULL | ⏭ 单独跑 86s 通过，但同进程里排在自己的 FIXED_BUDGET 之后会退化到 >600s（见下） |
| `gas_extcodecopy_sym` | FULL | ⏭ >420s 未完成 |

FULL 两格 skip 不影响错误分支的覆盖：**12/13 分支在 FIXED_BUDGET 下同样可达**——它们由
符号 offset/size 触发，与 gas 是否符号无关。`test_symbolic_fixture_error_branches_reachable`
对两种 gas 形态都逐条枚举 EVM 终止路径并判可满足性，钉死 12 与 13 都在被验证的路径集合
里（实测 7 条终止路径：13 四条、12 两条、STOPPED 一条）。FULL 只额外提供「对所有初始
gas 量化」。

**顺带发现的既有问题**：`gas_create_sym` 的 FULL 那格单独跑 86s 通过，但同进程里先跑过
同一 fixture 的 FIXED_BUDGET 之后会退化到 >600s。两个测试顺序跑即可复现（与 CPU 竞争
无关；排在其后的 `gas_extcodecopy_sym` 仍是 62s，所以是**同一 fixture 第二次执行**的
问题，疑似 Z3 全局 context 累积——`effect_id` 取自 `op.pc`，两次执行符号名相同）。根因
未定位，非 gas 改动引入。注意这是**性能**问题不是健全性问题：超时走 fail-closed，报
TIMEOUT 失败而非假绿。

## 10. 关键文件

| 文件 | 职责 |
| --- | --- |
| `state/evm_gas_state.py` | `EVMGasState`、费用纯函数（`memory_expansion_fee`/`word_fee`/`log_fee`） |
| `state/host_gas.py` | host/builtin gas UF、returnGas 链、x86 侧扣减 |
| `state/smt_state.py` | `symbolic_gas` / `gas_budget` 初始化、`host_gas_uf_enabled` |
| `evm_ir/semantics_gas.py` | `charge_dynamic_gas` / `charge_memory_and_word_gas` / `return_gas_for` |
| `evm_ir/semantics.py` | 各 opcode 的扣费点次序（CREATE 系的 add→fee→host→sub 四段） |
| `evm_ir/cfg_executor.py` | block 入口静态 gas、TAG 守卫内的 OOG 分叉 |
| `verification/program_verifier.py` | `GasCheck` 模式、allowlist 范围守卫、结论范围标注 |
| `verification/refinement_gas.py` | gas 终值等价检查 |
| `x86_64/go_function_semantics.py` | builtin memory grow、x86 侧 host gas UF 注入 |
| `tests/data/README.md` | gas fixture 用法、GOARCH 陷阱与覆盖点，绑定上游 commit |

## 11. 模型演进（为什么旧文档的做法不能照抄）

上一版文档描述的模型已整体废弃，逐条记录原因：

- **钳零扣减 + 恒足假设**。旧模型让 `consume_static/consume_dynamic` 在 gas 不足时归零
  续跑，靠 `_inject_gas_sufficiency_assumption` 注入 `UGE(G, Σstatic×500)` 保证该分支
  恒假。问题是"归零续跑"在解释器里没有对应物（`UseGas` 失败是**终止**），恒足假设一旦
  不生效（它只覆盖静态 gas）就会出现 IR 给 STOPPED 而 AOT 给 OUT_OF_GAS。现改为
  纯减法 + 无条件 OOG 分叉，恒足假设整套删除。
- **三个 gas 开关**（`gas_modeling_enabled` / `oog_modeling_enabled` / `check_gas` +
  `check_oog`）。前两个能关掉本该无条件成立的东西；后两个的真实差异只有一条（要不要注入
  恒足假设），却用两个 bool 表达，`check_gas=True, check_oog=True` 时 oog 静默夺权。
  现收敛为单个 `GasCheck` 三值枚举，只剩 `host_gas_uf_enabled` 一个 state 字段。
- **scope assumption 排除错误域**。旧模型对 offset/length 无条件 assume 高 192 位为 0、
  对 requested assume `≤ 0x1FFFFFFFE0`，把 `GAS_UINT_OVERFLOW` 与 cap-OOG 整片排除在
  验证域外，连 `RETURN(offset=2^200, length=0)` 这条合法路径也一并排除。现改为按
  `calcMemSize64` 的短路顺序建真实错误分支（§6.2）。
- **具体 gas 曾被一律拒绝**。旧守卫要求 `check_gas` 必须用符号 gas，真实理由却是
  `create_initial_state` 把 `host_gas_uf_enabled` 与 `symbolic_gas` 耦合在一起（具体 gas
  会连带关掉 host UF，比较对 host 段 vacuous）。耦合解除后，具体预算成了
  `FIXED_BUDGET` 的正常配置且剪枝更彻底。
