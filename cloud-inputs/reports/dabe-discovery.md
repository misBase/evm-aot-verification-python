# 任务 J：DABEManager 发现阶段的实例爆炸与 Z3 异常（dabe-discovery）

基线：分支 `cloud/inputs-dabe`（= 冻结提交 caa01b1 + 任务输入）。交付分支 `cloud/dabe-discovery`。
所有发现阶段数据都用新工具 `tools/discovery_stats.py` 在本容器（4 核，CPU 竞争较重）上测得，
参数与证书一致：`--gas-check full --timeout-ms 30000 --max-depth 400 --max-parameter-values 32 --summaries`。

## 1. 结论

1. **Z3 异常已定位并修复**：`common/uninterpreted.py` 的 `sha3_semantics` 在长度为常量 1 时调用
   `Concat(*bytes_list)`，此时只有一个参数，z3py 抛出 `Z3Exception: At least two arguments expected.`
   （带句号的这条消息只来自 `Concat`）。修复后，单字节哈希直接以 8 位字节作为 `sha3_bytes_1` 的参数。
   仓库里原本已有一处测试绕开了这个缺陷（`test_gas_error_codes.py` 把 SHA3 长度从 1 改成了 32），现在改回 1。
2. **实例爆炸的主因不是 (MSize, fmp) 参数，而是返回地址被当成普通常量加宽后引起的全跳转域扇出。**
   DABE 有 **13 个动态 `JUMP` 的 IR `immediate_set` 为空**（Go 的 `resolveSymbolicJumps` 没能解析，
   全是内部函数返回块），CErc20 和 Safe 都是 **0 个**。这些函数的返回地址不在 `_return_tags` 里，
   于是被当作普通常量，在"变化即加宽"规则下被丢掉，返回 JUMP 的目标变成符号。块模式下
   `complete_jump_domain=True`，符号目标会分叉到程序里**全部 627 个 JUMPDEST**，发现阶段又不检查
   `target == pc` 的可行性，所以每个这样的上下文都会提出约 626 个新上下文，并继续级联。
   基线（只修 SHA3）在 20 001 个实例时，**20 个扇出源直接提出了 11 799 个实例（59%）**；
   在前 8 000 个实例中，11 个扇出源占了 85%。
3. **第二个原因是真正的递归**。打开开关 P1 消除扇出后，DABE 仍会发散：存在一个类似
   `quickSort(arr, left, j - 1)` 的递归函数（块 11824，经 `checked_sub`（17655）→ 共享返回尾 3859 →
   跳板 9496 回到 11824），每递归一层栈深加 10、返回标签串加一段。调用串敏感的上下文在递归下
   没有不动点，只受 1024 栈上限约束。这一点在现有关系（绝对深度）下无法通过合并消除，见 §4、§5。
4. **疑似编译器缺陷（需在本地 go-hpc-evm 核实，本任务未改 Go）**：块 3859（`SWAP3 SWAP2 POP POP JUMP`，
   `checked_add`/`checked_sub` 共用的返回尾）的 `immediate_set` 只有 9 个目标
   `[403, 652, 9342, 11357, 11413, 12720, 12779, 13200, 13323]`，**不含 9496**。但 9473、12394、12676
   三处都把 9496 压栈作为 `checked_sub` 的返回地址（`PUSH2(9496) … JUMP(17655)`），逐指令推演可知
   3859 的 JUMP 目标就是 9496。x86 侧的 3859 块在 9 路 `cmp/je` 比较链之后直接写
   `[r13+0xe0]=8`、`[r13+0x28]=-12` 并 `ret`（错误退出）。如果这些调用点在真实执行中可达，
   AOT 代码会在 EVM 正常返回的地方报错，也就是不等价。验证器在证明 3859 的
   "返回标签 = 9496" 上下文时应得到 SAT。
5. **三个削减方案（全部默认关闭，各有开关）**，实测发现阶段实例数（上下文 = 关系节点）：

   | 合约 | 默认 | P1 | P1+P2+P3 | 证明实例（constant-insensitive）默认 → P1+P2+P3 |
   | --- | ---: | ---: | ---: | --- |
   | Safe | 3240 | 3270 | **2107（−35%）** | 2066 → 1873 |
   | CErc20 | 4708 | 4708（不变） | **3625（−23%）** | 2605 → 2461 |
   | DABE | > 46 306（发散） | 发散（递归）；剪掉递归后 9113 | 发散（递归）；剪掉递归后 **5021** | 剪掉递归：4032（P1）→ 3395 |

   - **P1 `--pushed-code-return-tags`**：把被 PUSH 的 JUMPDEST 常量（返回地址/函数指针）也视为返回标签，
     永不加宽。它消除 DABE 的扇出，对 Safe/CErc20 几乎无影响。
   - **P2 `--terminal-constant-projection`**：以 STOP/RETURN/REVERT/INVALID/SELFDESTRUCT 结束的块只保留块内消费的常量登记。
   - **P3 `--context-constant-projection`**（要求 P1）：每个上下文保留全部返回标签，非返回常量只保留本块消费的那些；
     并在加宽判断之前先投影。
   - 参数（MSize/fmp）维度对 DABE 几乎没有贡献（92–97% 的实例已经是 TOP；去掉参数维度最多只减少 0.5%），
     不推荐调低 `--max-parameter-values`。
   - 深度维度是剩余最大的维度，但关系里写死了绝对深度，本任务只给估算，不实现（§4）。

6. 全量快测：1704 passed，0 failed（§7）。

## 2. Z3 异常：复现、根因与修复

### 2.1 复现与 traceback

在 caa01b1 代码上，用证书参数（`--max-instances 200000`，只做发现）重跑 DABE，**6952 s、登记 46 306 个实例后**抛出与服务器相同的异常。
服务器报告里没有 traceback，这里给出完整调用栈（行号按 caa01b1 原文件；运行期间文件被编辑过，Python 打印的源码行
已不对应，这里略去）：

```
tools/discovery_stats.py            run  -> block_parallel.discover(verifier, setup, budget)
verification/block_parallel.py:118  discover -> run_evm_segment(prover.evm_blocks, state.copy(), spec.pc, ...)
verification/loop_induction.py:379  run_evm_segment -> executor.execute(cut_state, entry_pc=entry_pc)
evm_ir/cfg_executor.py:258          execute -> self.execute_state(global_state)
evm_ir/cfg_executor.py:409          execute_state -> self._execute_op_with_outcome(...)
evm_ir/cfg_executor.py:587          _execute_op_with_outcome -> op.to_z3(mstate)
evm_ir/models.py:102                to_z3 -> evm_operator_to_z3(self, state)
evm_ir/semantics.py:1096            evm_operator_to_z3 (SHA3) -> uninterpreted.sha3_semantics(memory, ..., length_bv)
common/uninterpreted.py:67          sha3_semantics -> Concat(*bytes_list)        # concrete_length == 1
z3/z3.py:4207                       Concat -> _z3_assert(sz >= 2, "At least two arguments expected.")
z3.z3types.Z3Exception: At least two arguments expected.
```

这次失败发生在**发现阶段**，所以 `attempted_instances` 为 0，与服务器的现象一致。服务器 1.5 小时、本容器 1.9 小时都没有收敛，
说明在异常之前实例数已经发散（§3）。修复后同样的配置会在 `max_instances` 处停下（`N=20000` 时 2330 s 耗尽预算）。

单独复现（任意内存、长度常量 1）：

```
poetry run python3 -c "from z3 import *; from common.uninterpreted import sha3_semantics; m=Array('m',BitVecSort(64),BitVecSort(8)); sha3_semantics(m,BitVecVal(0,64),BitVecVal(0,64),BitVecVal(1,256))"
→ z3.z3types.Z3Exception: At least two arguments expected.
```

DABE 中没有字面长度为 1 的 SHA3（90 个 SHA3 前面都不是 `PUSH1 1`），长度 1 来自栈上算出的值。
它在发现阶段出现，是因为扇出把上下文送进了任意 JUMPDEST，栈上恰好是常量 1。合法程序里的
`keccak256(abi.encodePacked(bytes1))` 同样会触发。EVM 侧（`evm_ir/semantics.py:1096`）和 x86 侧
（`x86_64/go_function_semantics.py:450`）共用这个函数，所以两侧都会抛异常。

### 2.2 修复与健全性

`common/uninterpreted.py:67-72`：参数不少于 2 个时用 `Concat`；只有 1 个字节时直接用该 8 位字节；
0 个字节保持原来的 `BitVecVal(0, 8)`。

- 没有跳过任何检查：原来是异常导致整个运行中止，现在构造出正常的 UF 项 `sha3_bytes_1(byte)`，
  后续检查照常进行。
- `sha3_bytes_<n>` 按长度区分 UF，单字节 UF 的签名是 BV8→BV256，与其他长度的 UF 互不相关，
  和其余长度一样没有任何哈希公理。这只是过近似，任何哈希函数都是它的模型。
- 两侧调用同一个函数，得到同一个项，"同输入同哈希"靠的是函数同一性，与修复前其他长度的做法一致。

### 2.3 测试

- `tests/unit/test_go_function_semantics.py::TestSha3Memory::test_sha3_single_byte_fast_path_hashes_the_byte`：
  UF 名称、8 位参数；切片外写入不改变哈希；字节相同则哈希相同；字节不同时哈希相等、不等都可满足（没有假设哈希性质）。
- `…::test_sha3_single_byte_x86_handler_matches_shared_semantics`：x86 sha3 host 调用在长度 1 时与共享语义给出同一个项（UNSAT）。
- `tests/unit/test_gas_error_codes.py::TestPerOpcodeWiring::test_offset_overflow_yields_gas_uint_overflow[SHA3-operands5-None]`：
  去掉原来的绕行，长度改回 1。
- 变异核对：回退修复后上面 3 个用例都失败，恢复后都通过。

## 3. 实例爆炸的量化

### 3.1 方法

`tools/discovery_stats.py` 调用与生产一致的 `block_parallel.build_inputs` / `_setup` / `discover`，
只做观察：包装 `_discover` 记录新实例，包装 `run_evm_segment` 记录每个实例的来源（来源 pc、深度）。
提议本身不变（`assert set(ordered) == seen`）。`analyze()` 输出以下内容：

- 实例总数与覆盖块数；每块实例数直方图；前 25 块的深度数、参数值数、返回上下文数、额外常量集数和证明实例数；
- 各维度投影后的不同键数（`no_parameters`、`no_constants`、`no_extra_constants`、`no_return_tags`、`pc_depth`、`pc`），
  它近似于只合并该维度后剩下的实例数（下游影响未建模，只作估计）；
- constant-insensitive 证明实例数，以及 P2/P3 的离线估计。

用这个工具重现了服务器的数字：Safe **3240**、CErc20 **4708**，与证书运行完全一致；
DABE 在 `N=8192` 时约 240 s 耗尽预算，与服务器上的"约 4 分钟"一致。

### 3.2 分布对比（默认参数）

| 指标 | Safe | CErc20 | DABE（基线，前 20 001 个，未收敛） |
| --- | ---: | ---: | ---: |
| 实例 | 3240 | 4708 | 20 001（预算耗尽，仍在增长；旧代码那次在 46 306 时因 Z3 异常中止） |
| 覆盖块 | 741 | 721 | 959（全部） |
| (pc, depth) 不同键 | 1638（2.2/块） | 1828（2.5/块） | 12 398（12.9/块） |
| 去掉参数维度 | 3153（−3%） | 4574（−3%） | 19 906（−0.5%） |
| 去掉全部常量 | 1744（−46%） | 2296（−51%） | 12 734（−36%） |
| 参数 TOP 占比 | 72% | 72% | 97% |
| 发现耗时 | 662 s | 930 s | 2330 s 到 20 001 |
| 扇出 > 8 的来源 | 0 | 0 | 20 个，直接提出 11 799 个（59%） |

DABE 的特征是每块的深度数异常多（例如 Panic 共享 revert 块 14355 在 0…32 的几乎每个深度都有实例），
而且大量实例不带任何返回标签。来源追踪显示，这些实例全部来自少数几个"返回目标为符号"的上下文，
例如 `(17714, d=11, K=((9,284),))`、`(16223, 11)`、`(11813, 19)`，每个都扇出到 626/627 个 JUMPDEST。

### 3.3 扇出机制（根因 A）

1. `_setup` 中 `_return_tags` 只取各 op 的 `immediate_set`。DABE 的 13 个返回 JUMP（6315、9773、10023、10050、
   10138、10247、10501、11813、13176、13692、16682、16717、17714）没有 `immediate_set`，它们的返回地址
   （共 139 个被 PUSH、却不在任何 immediate_set 中的 JUMPDEST，例如 3100、9521）都不算返回标签。
2. `_discover` 的"变化常量加宽一次"规则（`block_program.py` 中 `previous_extra != extra` 分支）在同一
   `(pc, depth, returns)` 下遇到不同调用点压入的不同返回地址时，把它们和计数器一起丢掉。
3. 被丢掉的槽在 havoc 中是符号。返回 JUMP 在 `complete_jump_domain` 下分叉到 `valid_jump_targets`
   全集（`evm_ir/cfg_executor.py:694-703`），发现阶段只做 `is_false(simplify(joint))`，
   `slot == pc` 这样的约束永远可满足，于是在同一深度提出约 626 个上下文。这些上下文的深槽也是符号，
   会继续级联到各种深度。
4. CErc20/Safe 没有空 `immediate_set` 的返回 JUMP，所以不触发这个机制。

### 3.4 递归（根因 B）

打开 P1 后不再有扇出源（P1 部分集合中扇出 > 8 的来源为 0），但最大深度从 32 增长到 67 以上并持续增长。
最深实例的返回标签串里出现周期为 8 个槽的重复（`12687` 出现 3 次，`12412` 出现 3 次）。祖先链显示一个循环：
`11824 → 11842 → 11891 → 11898 → 12383 → 12394 →（调用 17655 checked_sub）→ 3859 → 9496 → 11824`，
每圈深度加 10（第二个递归调用点经 12412/12432 回到 11824）。静态边加调用摘要边的可达性分析看不到这个环，
因为它经过 3859 的动态返回。这是源码层面的递归，不是发现阶段的伪路径。

## 4. 削减方案、健全性论证与实例数

共同前提（`block_specialization.py` 模块文档、`block_program._discover` 文档）：发现阶段只产生
**不可信提议**，证书要求冻结集合中每个实例都证出，H0/H2 对冻结集合闭合。三个开关只改变"登记哪些常量"，
不改变证明、H0/H2 或消费者。

### P1：被压栈的代码地址视为返回标签（`--pushed-code-return-tags`）

- 位置：`verification/block_program.py:169-183`（`pushed_code_addresses`），`:410-413`（并入 `_return_tags`）。
- 规则：`{op.immediate | op 是 PUSH 且 immediate 是 JUMPDEST 块 pc}`。静态跳转的目标折叠在 JUMP/JUMPI
  自身上，所以被 PUSH 的 JUMPDEST 就是作为数据使用的代码地址（返回地址或函数指针）。
- 健全性：`_return_tags` 只决定哪些常量在加宽时保留（`_setup` 注释："Untrusted hints only"）。
  多保留常量会让上下文更具体：局部定理的前提更强，所以更容易证；H2 进入它更难，前驱必须给出这个常量，
  给不出就是 H2 失败，即证不出，不会误证。集合有限（不超过 JUMPDEST 数），资源上限 `max_instances` 不变。
  字面量碰巧等于某个 JUMPDEST 也一样，只是更具体。
- 效果：DABE 扇出源从 20 个降到 0；Safe 3240→3270（+1%）；CErc20 4708→4708（不变）。

### P2：终止块的上下文投影（`--terminal-constant-projection`）

- 位置：`verification/block_specialization.py:106-115`（`terminal_block`），`block_program.py:414-415`、`:592-593`。
- 规则：块的活控制操作是 STOP/RETURN/REVERT/SELFDESTRUCT/INVALID 时（与 `cfg_executor` 约定一致），
  登记 `π(c)`，只保留 `sensitive_slots` 中的常量（连返回标签也丢掉）。
- 健全性：`R_π(c) = R_c` 去掉若干常量等式，是 `R_c` 的弱化。凡满足 `R_c` 的出口都满足 `R_π(c)`（H2 更容易）；
  `T_π(c)` 对所有满足 `R_π(c)` 的入口成立，与 constant-insensitive 的 `k = π(c)` 是同一个"前提加强"论证
  （`docs/块级实例常量去敏化方案.md` §3.3），丢错槽只会让证明更难。终止块没有后继，所以丢掉的常量不影响任何
  其他提议；它也没有 H2 出边，不需要 `E_c`。
- 效果：Panic/revert 共享块按调用串复制的问题（DABE pc 16949 有 219 个返回上下文）收敛为按深度一个。
  单独使用时离线估计：Safe 3240→2983（−8%）、CErc20 4708→4256（−10%）。

### P3：上下文常量投影，保留返回标签（`--context-constant-projection`，要求 P1）

- 位置：`block_program.py:216-222`（要求 P1，否则 `ValueError`；CLI 同样报错），`:416-417`、`:560-563`。
- 规则：非返回常量只保留本块 `sensitive_slots` 中的；返回标签全部保留。投影在加宽判断**之前**做，
  这样只被搬运、却在变化的常量不会把被消费的常量一起加宽掉。
- 健全性：同 P2，登记的是弱化的上下文。丢掉的常量若被某个后继块消费，后继看到的是符号，证明更难、
  可能失败，但不会误证。要求 P1，是因为不把代码地址当返回标签时，P3 会丢掉空 `immediate_set` 的返回地址，
  重新引入根因 A 的扇出（这不影响健全性，但会让实例数爆炸）。
- 效果（P1+P2+P3 实测）：Safe 3240→**2107**，CErc20 4708→**3625**，发现耗时分别减半、减少 31%。
  证明实例数（constant-insensitive）分别为 1873、2461。

### 不推荐 / 未实现

- **调低 `--max-parameter-values` 或改成按 (pc, depth) 共享参数域**：对 DABE 无效。参数维度已经是 TOP
  （`parameters_per_context` 绝大多数为 1）；去掉参数维度，DABE 只减少 0.5%，Safe/CErc20 减少 3%。
- **深度类合并**：剩余最大维度（DABE P1+P2+P3 下 5021 → `pc` 959；Safe 1639 → 741）。但 `stack_geometry`、
  TAG 序言的深度检查、`live_stack_prefix` 都用绝对深度（`docs/块级实例常量去敏化方案.md` §6），
  需要"栈顶 w 槽相对寻址 + 不透明调用帧"的新关系，另立专题。
- **返回标签 k-limiting / 递归重复标签加宽**：丢掉深层返回标签会在递归展开时让返回目标变成符号，
  重新触发全域扇出；而且深度本身仍随递归层数增长。不解决根因 B。

## 5. DABE 的剩余规模

为了在递归存在时仍得到一个有定义的估计，`tools/discovery_stats.py --cut-recursion`（**只用于估算，绝不是证明模式**）
不登记返回标签有重复的上下文，因此也不探索它们的后代：

| DABE 配置 | 实例 | 被剪的递归上下文 | 耗时 | 证明实例 |
| --- | ---: | ---: | ---: | ---: |
| P1，剪递归 | 9113 | 29 | 2320 s | 4032 |
| P1+P2+P3，剪递归 | **5021** | 18 | 1198 s | 3395 |

也就是说：P1 消除扇出后，非递归部分收敛到 9113；P2/P3 再把常量维度削掉 45%，降到 5021，**非递归部分**的规模与 CErc20（4708）相当。剩下的问题是递归函数
（约 18 个递归入口上下文），每层 +10 深度，直到 1024 栈上限。在现有绝对深度关系下没有有限的覆盖。
要拿到 DABE 的证书，需要递归/深度泛化（§4 不推荐项第 2 条），或者对该递归函数做摘要。
另外，§1 第 4 条的 3859 问题如果属实，证书本来就不应该成立。

## 6. 改动位置

| 文件 | 位置 | 内容 |
| --- | --- | --- |
| `common/uninterpreted.py` | :67-72 | 单字节 SHA3 不再调用单参数 `Concat` |
| `verification/block_program.py` | :169-183 | `pushed_code_addresses` |
| 同上 | :190-223 | 构造参数 `pushed_code_return_tags` / `terminal_constant_projection` / `context_constant_projection`（默认 False；P3 要求 P1） |
| 同上 | :410-417 | `_setup` 中计算返回标签并集、终止块与各块敏感槽 |
| 同上 | :560-563、:586-594 | `_discover` 中 P3 的加宽前投影、P2 的登记投影 |
| `verification/block_specialization.py` | :106-115 | `terminal_block` |
| `verification/block_parallel.py` | :81-84 | `build_inputs` 透传三个选项 |
| `tools/verify_block_lockstep.py` | :150-158 及 worklist 调用 | 三个 CLI 开关（默认关；P3 无 P1 时报错） |
| `tools/discovery_stats.py` | 新文件 | 仅发现的统计工具，支持离线 `--from-specs` 和估算用的 `--cut-recursion` |

生产默认值未改：三个开关默认关闭，关闭时 `_return_tags`、`_discover` 的行为与原来逐字节相同
（Safe/CErc20 的 3240/4708 在默认参数下重现）。

## 7. 测试结果

新增用例（均已按节点 ID 单独运行，确认被收集）：

- `tests/unit/test_go_function_semantics.py::TestSha3Memory::test_sha3_single_byte_fast_path_hashes_the_byte`
- `tests/unit/test_go_function_semantics.py::TestSha3Memory::test_sha3_single_byte_x86_handler_matches_shared_semantics`
- `tests/unit/test_gas_error_codes.py::TestPerOpcodeWiring::test_offset_overflow_yields_gas_uint_overflow[SHA3-operands5-None]`（改为长度 1）
- `tests/unit/test_block_candidate_discovery.py::test_pushed_code_addresses_are_pushed_jumpdests_only`
- `…::test_pushed_code_return_tag_survives_constant_widening`（默认会加宽掉，P1 下保留，计数器仍只加宽一次）
- `…::test_pushed_code_return_tags_switch_defaults_off_and_unions_in_setup`（`muti_block_08` 上的真实 `_setup`）
- `…::test_terminal_block_detection_follows_the_live_control_op`
- `…::test_terminal_projection_registers_a_weakening_with_consumed_constants_only`（`weakens(π(c), c)`；非终止块不变）
- `…::test_context_projection_keeps_return_tags_and_consumed_constants`（无 P1 报错；保留返回标签；只被搬运的变化常量不再触发加宽）
- `tests/unit/test_discovery_stats.py::test_recursive_means_a_repeated_return_tag`
- `tests/unit/test_discovery_stats.py::test_analyze_counts_dimension_projections`

全量快测 `poetry run pytest tests/unit -q -m "not slow" -p no:cacheprovider`**1704 passed, 2 skipped, 0 failed**（693 s，`-n 2`）。
基线（改动前）同一命令收集 1696 项；本次新增 10 个用例，1696 + 10 = 1704 passed + 2 skipped，数目相符（SHA3 参数化用例是改写已有用例，不计入新增）。

## 8. 离线验证数据

`cloud-inputs/reports/dabe-discovery-data/` 下是各次运行的 `discovery_stats` JSON（含配置、耗时、错误
traceback、维度统计）：

| 文件 | 配置 |
| --- | --- |
| `safe_default.json` / `cerc20_default.json` | 默认（重现 3240/4708） |
| `dabe_default_caa01b1_z3exception.json` | caa01b1 原代码，46 306 处 Z3 异常（含完整 traceback） |
| `dabe_default_sha3fix_cap20000.json` | 只修 SHA3，`N=20000` 预算耗尽 |
| `safe_p1.json` / `cerc20_p1.json` | P1 |
| `safe_p123.json` / `cerc20_p123.json` | P1+P2+P3 |
| `dabe_p1_cut_recursion.json` / `dabe_p123_cut_recursion.json` | P1 / P1+P2+P3，`--cut-recursion`（估算） |
| `dabe_p1_partial12000_offline.json` | P1 未剪递归，前 12 000 个实例的离线统计（发散中） |

其中 default 系列和 partial 文件的 `stats` 是事后用当前工具 `--from-specs` 对该次运行的完整实例清单重算的，
运行级字段（耗时、错误、traceback）保留原值。重新生成用：

```
PYTHONPATH=. poetry run python -m tools.discovery_stats <stem> [--pushed-code-return-tags] \
  [--terminal-constant-projection] [--context-constant-projection] [--cut-recursion] \
  --max-instances 100000 --output stats.json --specs specs.txt
PYTHONPATH=. poetry run python -m tools.discovery_stats <stem> --from-specs specs.txt   # 离线分析
```

建议在服务器上核对：

1. Safe/CErc20 在 `--pushed-code-return-tags --terminal-constant-projection --context-constant-projection`
   下跑完整证书（`--discover-first --constant-insensitive`），确认仍是 VERIFIED，并比较墙钟。
   本容器只测了发现阶段，没有跑证明，P3 对证明难度的影响未知。
2. 在 go-hpc-evm 上对一个会调用排序（经 9473/12394/12676 → `checked_sub`）的 DABE 外部函数做
   解释器与 AOT 的具体执行对照，确认 §1 第 4 条的 3859 `immediate_set` 缺 9496 是否导致 AOT 报 InvalidJump。

## 9. 未解决的问题

- DABE 的递归（根因 B）在现有绝对深度关系下没有有限覆盖，需要深度/递归泛化或函数摘要。
- 3859 的 `immediate_set` 疑似不完整（§1 第 4 条），只做了 IR 与 x86 反汇编层面的核对，未在 Go 侧执行确认。
  13 个空 `immediate_set` 的返回 JUMP 也说明 Go 的符号跳转解析在这个合约上覆盖不全。
- P3 只在发现阶段测量。它丢掉的常量若被后继块消费，后继的证明可能变难，需要服务器上的证明对比。
- 已知快测例外：COMMON.md 提到的 msize_absint 相关用例（依赖被忽略的 `tmp/prov_common.py`）在本容器中没有失败。
  改动前的基线快测在重负载（`-n 8`，同时跑 3 个发现进程）下有 2 个用例因超时失败：
  `test_block_uf_unification.py::test_alias_split_keeps_satisfiable_pairs_open`、
  `test_div_summary.py::test_lemma_proves_every_path_including_builtin_bridge`。单独运行都通过（46 s），与本改动无关。
