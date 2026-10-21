分支：`claude/inputs-n-remaining-blocks-rm2fog`（会话只允许推送 `claude/...` 分支，未使用任务书建议的 `cloud/remaining-blocks`）。基线 = `cloud/inputs-n`（d15c606，即任务 M 的 3F）。

# 任务 N：剩余块 —— 根因与通用修法

## 1. 结论

**没有出现任何 SAT（反例），也没有发现编译器问题**，所以不需要做具体执行。PoolManager 9089 服务器上的 `x86_maps_7_0` / `8_0` SAT 只是对应关系的提议错了，不是反例（§2.6）。

共七处通用修法，全部只改 Python 端，没有按合约或块号特化：

| # | 修法 | 位置 | 解决的问题 |
|---|---|---|---|
| 1 | 乘积字泛化 | `check_paths` 执行假设的候选 | Aave 11831 |
| 2 | 内存势函数 P 的值域/单调公理 | potential 路线最后一步、空行提议 | Permit2 1327 `pair_0_6` / `pair_0_7` |
| 3 | summary 入口 SAT 未判定时照常证明 | `VerifiedSummaryRuntime.apply` | Aave 7200 x86 执行超时（第一层） |
| 4 | 用 blast 过的路径条件找回模型见证 | x86 可达性检查、summary 入口检查 | Aave 7200（第二层） |
| 5 | 所有复制循环模板的"空命中" | `dead_hit` | Aave 7200（第三层） |
| 6 | 节点级 UF 参数合并限时 1/4 | `_unify_node` | PoolManager 16670 |
| 7 | 复制循环前提蕴含的 blast 回退 | `copy_loop._implication_result` | Aave 7200（第四层） |

逐块结论（本机：4 核，z3 4.15.4，每查询 30s，多进程并行；"1h 分诊"= `--node-seconds 3600 --keep-going`）：

| 合约 | 块 / 实例 | 义务是否成立 | 卡住的类别 / 根因 | 修法 | 修法前 | 修法后（本机） |
|---|---|---|---|---|---|---|
| Permit2 | 1327 d10 符号 | 成立 | **不是 SSTORE gas 等价**。x86 路径 6/7 最后一项是 LOG2 费用 `8·len + 1125 + 扩展费` 的 64 位溢出检查；前缀已检查 `32w < 2^37`，费用 ≤ 2^40 + 1125 + C(2^32−1) ≪ 2^64，**x86 路径 6/7 本身不可行**。要证它需要 C(w)=3w+⌊w²/512⌋ 的上界与单调性 | 2 | 行 6/7 为 "all"：`pair_0_6` 5925s、`pair_0_7` 1943s unknown（任务 M） | 行 6/7 改为空行；**`x86_empty_6` 147.4s、`x86_empty_7` 127.9s proved**（空行提议 43.0s / 41.4s）。整节点 6h 复跑见 §6.4 |
| Permit2 | 1327 d10 m=192 f=128 | 1h 内无失败 | 1h 分诊：1892 个查询，无失败，预算用完。导出路径后逐行检查 13 个 "all" 行的末项：**没有** LOG 费用溢出那一类（都是内存上限、gas、`fmp+32` 溢出检查等普通错误路径） | — | 任务 M 未跑 | **没有同类 pair**；整节点本机未跑完（§8） |
| Aave | 11831 d12 m=96 f=128 | 成立 | `evm_assumption_7` 是 256 位乘积 `P = x·1e27` 的比较桥接 `P == 1e27 ⇔ 两向都不借位`，对任意 256 位字成立；逐 `bvmul` 泛化后 limb 仍是带进位的和 | 1 | 209s inconclusive（该义务 202.9s unknown） | **整节点 74.5s proved**（该义务 0.0s） |
| Aave | 7200 d13 m=96 f=128 | 待定（x86 执行先要做完） | **符号执行爆炸**，见 §2.3：可达性检查 unknown → 丢失见证 → 每个 summary 命中要单独解入口 SAT（17–37s，贴着 30s 预算）→ 超时被拒 → 回退到原始代码，符号长度的 CALLDATACOPY 复制循环（copy_loop@0x72fc8）逐圈展开。属于"已有 summary（copy-loop、memgas）应当覆盖却没覆盖"：summary 本身可证，被与健全性无关或可判定的检查挡住 | 3、4、5、7 | 服务器 21603s `x86 segment execution deadline exhausted` | §2.3 / §6.3 |
| Aave | 6182 d14 符号 | 1h 内无失败 | 1h 分诊：EVM 95 / x86 49 条路径，4511 个查询，无失败，预算用完（服务器 6h 只有 4640 个查询） | — | 21621s 预算用完 | **预算类**；1h 无失败 |
| Aave | 8248 | 未跑整节点 | 本机 15GB、同时有 3–4 个重进程，没有跑整节点（任务 M 曾被 OOM）；`pair_0_1` 的回归见 §6.2（1231.5s proved） | — | — | 未跑（§8） |
| PoolManager | 4418 符号 | 1h 内无失败 | 1h 分诊：EVM 63 / **x86 885** 条路径，2502 个查询，无失败，预算用完 | — | 6h 预算用完 | **预算/路径数**类 |
| PoolManager | 4418 f=320 | 未跑 | 重启中断，未重跑 | — | — | 未跑（§8） |
| PoolManager | 9089 d2 符号 | 成立（卡住的义务单独已证） | 1h 分诊：唯一失败 `x86_maps_0_9`（RETURN 前的内存 gas 检查，5 级扩展费链）节点内 1100s unknown；单独跑生产 `_check` **153.1s proved**（blast* 路线中的 potential 重试），关掉修法 2 时 186.2s，所以不是能力问题，是节点内的预算/路线顺序 | — | 1100s unknown（节点内） | 单独 153.1s proved |
| PoolManager | 16670（三个实例） | 待定 | **预算分配**：pair 阶段进入 `_check_rows` 后，节点级 `unify_across` 不限时，16670 m=768 的 83 个 host-call pair 上 189 个参数对失败、1 个成功，**60 分钟后仍没有检查任何义务**。符号实例 1h 只有 113 个查询 | 6 | 服务器 6h 预算用完 / `pair_2_74`、`pair_4_84` unknown | 限时后 `_unify_node` 1378.9s，随后义务开始推进（`x86_maps_74_0` 2.5s，`pair_2_74` 的 goal 部分各 0.1s）；完整结果见 §6.5 |
| PoolManager | 6084 m=864 f=768 | 待定 | 1h 分诊见 §6.5 | — | 6h 预算用完 | §6.5 |

## 2. 逐块分析

### 2.1 Aave 11831 `evm_assumption_7`

块 11831 = `POP PUSH 1e27 SWAP2 MUL PUSH 5e26 ADD DIV`（rayDiv）。EVM 执行器给乘积 P（逐 limb 计算的 256 位字）的比较留了一条桥接假设 `(P == 1e27) == (¬borrow(P − 1e27) ∧ ¬borrow(1e27 − P))`，借位按 65 位逐 limb 链写出。`check_paths` 要求每条执行假设都被证明。这条假设对任意 256 位字都成立；原有候选 `_generalize_products`（把每个 `bvmul` 换成新常量）后 30.6s unknown，直接查询 30.2s unknown。把整个乘积字（≥128 位、含 `bvmul` 的极大 concat）换成新常量后 0.0s unsat。

### 2.2 Permit2 1327 `pair_0_6` / `pair_0_7`

- `dump_paths.py` 导出：61 条 EVM 路径、65 条 x86 路径；`_correspondence` 给行 6、7、8 的都是 "all"。
- x86 路径 6 的末项：`Extract(64,64, zext(8·len) + zext(1125 + t24)) == 1`，t24 = `If(new ≤ msize, 0, C(new) − C(old))`，C(old) 本身是前面各次扩展的 ite 链。前缀中有 `32w < 2^37`、`8·len` 不溢出 64 位、`fmp + len` 不回绕。
- 所有路线失败的原因：精确求解要 bit-blast 8 个 64 位平方（30s unknown）；乘法抽象 + 平方单调性没有平方的绝对上界（abstract-SAT，1.2s）；potential 路线把 C 换成任意函数 P（abstract-SAT，1.4s）。
- 加上 P 的值域 + 单调公理：bvabs 3.1s unsat，精确 8.6s unsat；只有值域也是 SAT（要用 C(old) ≤ C(new) 去掉减法）。
- 任务 M 说"SSTORE 一类的 gas 检查"：实际失败的合取项里没有 `host_gas_sstore`，是 LOG2 的费用溢出检查。

### 2.3 Aave 7200 x86 分段执行

- 静态规模（`segment_jcc.py`）：0x6d87e..0x76f89，7380 条指令，556 个条件跳转，180 个 ret。主路径基本线性（每个分叉的另一边是错误 stub）。四次 CALLDATACOPY 都是符号长度。
- 第一层（修法 3）：路径条件变大后可达性检查多为 unknown（REACH_STATS：incremental unknown 平均 3.9s，之后的乘法抽象探针 unknown 平均 2s），路径丢失模型见证。此后每个 summary 命中要单独解 `entry`（命中前提 SAT），实测 17.6–28.3s sat 或 30.4s unknown。被拒的前提单独求解 36.5s sat（没有 UF，常函数见证不适用）。unknown 时 summary 被拒，回退原始代码；拒绝出现的位置随负载变化（0x719d4 / 0x72dd4），说明是预算边界问题。
- 第二层（修法 4）：用前缀扫描定位到让求模型变难的合取项：一个 203KB 的内存字读取，经过 3 个 lambda 数组上的 store 链（前面复制循环的结果）。`simplify(F, blast_select_store=True)`（精确改写）后同一前提 **4.1s sat**，模型在原式上求值为字面 true；`expand_select_store` 仍 30s unknown。修法 4 之后，前 29 次 incremental unknown 中 blast 判定了 25 次（18 次 unsat 被剪掉，7 次 sat 找回见证）。
- 第三层（修法 5）：`copy_loop@0x72fc8` 的命中前提被判为 **unsat**（路径不可行），但 `dead_hit` 只覆盖 MCOPY 模板，于是在不可行路径上回退原始代码、逐圈展开。
- 第四层（修法 7）：同一命中的复制循环自身前提（`makedata-byte-copy no-wrap#0/#1`）蕴含查询 unknown（约 166s），被拒。
- 修法 3–7 之后的整段结果见 §6.3。

### 2.4 Aave 6182、PoolManager 4418

两个节点 1h 都没有任何失败，查询数与服务器 6h 相当或更多：6182 EVM 95 / x86 49 条路径；4418 x86 885 条路径。属于预算类。4418 的 885 条 x86 路径是主要成本，本次没有找到针对它的通用修法。

### 2.5 PoolManager 16670

- 16670 m=768 的 pair 阶段：EVM 3 / x86 83 条路径，对应关系全部给出（行 0..68 → EVM 0，69..81 → 2，82 → 1）。
- `_check_rows` 在检查任何义务前，先对所有 host-call pair 做节点级 `unify_identities` + `unify_across`。前者已有 4 个查询超时的上限，后者只受 `max_lemmas`（成功次数）限制，失败不计。实测：限时前 60 分钟后仍在 `unify_across` 里（py-spy 多次采样）；限时后 1378.9s 内 `_prove_equal` 成功 1 次、失败 189 次（1147.6s），之后义务开始推进，服务器上失败的 `pair_2_74` 的各 goal 部分各 0.1s。

### 2.6 PoolManager 9089

- 1h 分诊：EVM 35 / x86 51 条路径，869 个查询；唯一的失败 `x86_maps_0_9` 在节点内 1100s unknown，单独 153.1s proved。
- `x86_maps_7_0` / `8_0` SAT 的含义：`x86_maps_j_k` = "x86 路径 j ⇒ 被提议 EVM 路径的第 k 个合取项"。SAT 只说明行 j 不对应那条 EVM 路径；`_pair_phase` 把该行退回 "all"，第二轮逐个证明 `pair_i_j`，失败的提议不进入证书（`BlockTheorem.complete` 只看最终对应关系下的清单）。所以它**不是反例**。

## 3. 改动位置

- `verification/block_equivalence.py`
  - 修法 1：`_generalize_product_words`；`check_paths` 中执行假设的候选列表（乘积字候选最先试）。
  - 修法 2：`_POTENTIAL_WORDS`、`_POTENTIAL_MONOTONE_APPS`、`potential_range_axioms`、`refute_over_bounded_potential`（紧跟 `telescope_potential`）；`_retry_over_potential` 末尾的一次带公理尝试；`_empty_by_bvabs` 的第二个尝试。
  - 修法 6：`_unify_node` 中 `unify_across` 的截止时间。
- `verification/block_summaries.py`：修法 3（`apply` 中 `entry` 的异常分支）；修法 4（`_solve` 对 expected sat 的 blast 回退）。
- `x86_64/cfg_state.py`：修法 4（`X86Constraints.is_possible` 中 incremental unknown 之后的 blast 查询）。
- `verification/mcopy_induction.py`：修法 5（`dead_hit` 覆盖所有 copy-loop 模板）。
- `x86_64/summaries/copy_loop.py`：修法 7（`_implication_result` 末尾的 blast 回退）。
- 测试：`tests/unit/test_block_remaining_blocks.py`（新增 20 条）；`tests/unit/test_copy_loop_summary.py::test_structural_fact_fallback_reuses_one_forward_cache` 的查询次数断言 1 → 2（修法 7 有意增加了一次回退查询，测试的本意"复用同一个 forward 缓存"不变）。
- 数据：`cloud-inputs/n/smt2/`（`aave_11831_evm_assumption_7.smt2`、`permit2_1327/x86_empty_6.smt2`、`x86_empty_7.smt2`）。
- 诊断工具：`cloud-inputs/n/tools/`（§7）。

## 4. 健全性论证

- **修法 1**：G = F[w_i := c_i]，c_i 新常量，w_i 是 F 中含 `bvmul` 的极大宽 concat。¬G 不可满足 ⇒ G 对 c_i 任意取值成立 ⇒ F 作为代换实例有效。只是多一个候选（5s 上限）；不成立时落到原有候选和 `_check`。非恒真式不会通过（`test_generalised_words_do_not_prove_a_non_tautology`）。
- **修法 2**：`abstract_memory_potential` 把 E(w) 换成 P(w) − 3w（P 读作 C 时还原），只增加模型；`telescope_potential` 是 P 读作 C 下的等价变换（恒等改写有证明，记为 lemmas）。新增公理对每个 P(a)、P(b)（位宽 n ≥ 64，W = 2^32−1）：`a ≤ W ⇒ P(a) ≤ C(W)`，`a ≤ b ≤ W ⇒ P(a) ≤ P(b)`。P 读作 C 时 a ≤ W ⇒ a² < 2^64，3a + ⌊a²/512⌋ < 2^n，C 在 [0, W] 上不减，所以每条公理成立，合取后保留原式全部模型；之后的乘法抽象和数组泛化也只增加模型。所以只有 unsat 有意义且可以传回原式。< 64 位不生成公理；单调公理超过 32 个 P 应用时不生成（只是少证）。在 `_empty_by_bvabs` 中只是**提议**：`x86_empty_j` 仍由 `_check` 独立证明，提议错了只会让该义务失败、退回 "all"。
- **修法 3**：summary 证书的结论"对满足前提 P 的每个状态，原始切片 = summary 效果"来自 coverage、effect、copy_domain、copy_param_*、exit_guard_excluded 等 **UNSAT 查询**（P ∧ ¬目标），对 P 可满足与否都成立；P 不可满足时命中是空洞的。`entry`（P 可满足）只用来区分空命中与正常命中。只改了 `entry` **unknown** 的情形：不再拒绝，记录的 expected 写成 `unknown`（证书如实显示"未判定"），其余义务照常必须证出，任何一条失败照旧拒绝。`entry` 为 unsat 的处理不变。
- **修法 4**：`simplify(·, blast_select_store=True)` 是 Z3 的等价改写。可达性：其 unsat 就是路径条件 unsat，剪枝正确；sat 时只有当模型使**原**路径条件字面为 true 才作为见证（见证只用于跳过求解器调用，对应的分支本来就会被保留）；unknown 照旧保留路径。summary 入口：等价式 sat ⇒ 前提 sat。
- **修法 5**：入口 unsat ⇒ 没有状态满足命中前提，任何后继都空洞地正确；证书仍是只含该 unsat 证明的 `DeadHitCertificate`。与 MCOPY 已有的论证相同，只是去掉了模板限制。
- **修法 6**：`unify_across` 的每次合并都由被反驳的查询支持；提前停止只是少合并，未合并的 pair 照常走自己的全部路线（其中也有 unify 路线）。只影响耗时。
- **修法 7**：同修法 4，blast 是等价改写，`_implication_result` 只有 unsat 才算证出。
- 没有"提议出错就会误证"的通道：乘积字、公理实例、空行、见证、合并顺序都只是候选或加速；每个结论最终都落到被反驳的查询，或落到对所有解释都成立的公理上。

## 5. 测试结果

- 新增 `tests/unit/test_block_remaining_blocks.py`（21 条），逐个按节点 ID 单独运行全部 1 passed，确认都被收集到。真实 SMT2 用例：Aave 11831（<1s）、1327 行 6/7（各约 10–12s）。修法 3 的两条、修法 4 的两条在旧代码上失败（已确认能区分新旧行为）。
- 全量快测：见 §5.1（最终数字在最后一次提交中更新）。
- 负载敏感的已有测试：`test_mcopy_induction.py::test_symbolic_length_mcopy_has_complete_certificate[mcopy-high-word]` 在本机 5 个重进程并行时两次出现 `step_1_other: unknown`（20s 预算的引理查询），单独运行 2 passed（161s / 179s，修法 3 和修法 3–5 之后各一次）。失败的是引理查询，不是 `entry`。

### 5.1 全量快测

（待最终运行）

## 6. 离线验证数据

### 6.1 单条义务

| 对象 | 修法前 | 修法后 |
|---|---|---|
| Aave 11831 `evm_assumption_7` | `_generalize_products` 30.6s unknown；直接 30.2s unknown | 0.0s unsat |
| Aave 11831 整节点 | 服务器 209s inconclusive | 74.5s proved（16 个查询） |
| 1327 `premise ∧ x86_6`（bvabs / 精确） | 30.4s / 30.2s unknown | 3.1s / 8.6s unsat |
| 1327 `x86_empty_6` / `x86_empty_7`（生产 `_check`） | "all" 行：`pair_0_6` 5925s / `pair_0_7` 1943s unknown | 147.4s / 127.9s proved |
| PoolManager 9089 `x86_maps_0_9` | 节点内 1100s unknown | 单独 153.1s proved（无修法 2：186.2s） |
| Aave 7200 被拒命中前提（`entry`） | 30.4s unknown（直接 36.5s sat） | blast 4.1s sat |

### 6.2 回归：任务 L / M 的 SMT2（`regress.py`，生产 `_check`）

| 义务 | 之前报告 | 现在 |
|---|---|---|
| 5802 `model_domain_nonempty` | 0.28s sat | 0.3s sat |
| 4837 `x86_maps_12_0` | 23.8s | 23.4s proved |
| 4837 `x86_maps_14_0` | 14.1s | 13.7s proved |
| 1327 `x86_maps_0_0` | 82.4s | 76.9s proved |
| 1327 `x86_maps_0_1` | 58.5s | 51.7s proved |
| 1327 `x86_maps_0_46` | 96.6s | 85.4s proved |
| 1327 m192 `x86_maps_0_46` | 85.8s | 95.2s proved |
| Aave 8248 `pair_0_1`（只走 `_check`） | 1227.9s | 1231.5s proved |

（以上在修法 1–2 之后、修法 3–7 之前测得；修法 3–7 只改 x86 执行与 summary，不影响这些义务的 `_check` 路径，修法 6 只影响节点级合并。）

### 6.3 Aave 7200 x86 分段（`x86_profile.py`）

（待最终运行）

### 6.4 Permit2 1327 d10 符号整节点

（待最终运行）

### 6.5 PoolManager 16670 m=768（限时后）与 6084

（待最终运行）

## 7. 诊断工具（`cloud-inputs/n/tools/`，仅用于诊断）

- `dump_paths.py`：跑到 pair 阶段为止，导出前提、每条路径条件、对应关系与指定 pair；或导出名字匹配的义务（如 `evm_assumption_7`）。
- `build_maps.py`：按 `_check_rows` 的做法重建 `x86_maps_J_K`。`row_tails.py`："all" 行的末项。
- `empty_row.py`：某 x86 行的空行提议和 `x86_empty_J` 的 `_check`。
- `x86_profile.py`：x86 分段剖析（分叉、可达性耗时、summary 命中/拒绝及失败义务、互补检查命中），导出被拒命中前提与失败的 summary 查询。
- `entry_sat.py`、`segment_jcc.py`、`show_block.py`。
- `trace_node.py`：整节点逐义务计时，并统计 `_unify_node` 的耗时与 `_prove_equal` 成败。
- `regress.py`：SMT2 上跑生产 `_check`。`without.py FIX TOOL ...`：关掉某个修法再跑（A/B）。

## 8. 未完成的块及原因

（待最终更新）
