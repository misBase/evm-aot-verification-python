分支（任务 N2 / remaining-blocks-2）：`claude/remaining-blocks-2-cn9veq`（会话只允许推送这个 `claude/...` 分支，未使用任务书建议的 `cloud/remaining-blocks-2`），基于 `cloud/inputs-n2`（4dd0baa）。任务 N2 的结果见 §9“冻结版机器码复核”。

任务 N 的原分支：`claude/inputs-n-remaining-blocks-rm2fog`（会话只允许推送 `claude/...` 分支，未使用任务书建议的 `cloud/remaining-blocks`）。基线 = `cloud/inputs-n`（d15c606，即任务 M 的 3F）。

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

任务 N2 在本分支上运行（`poetry run pytest tests/unit -q -m "not slow" -p no:cacheprovider -n 4 --dist=loadscope`，本机 4 核，机器上没有其他负载）：

- 第一次运行：**1 failed, 1768 passed, 3 skipped（524s）**。失败的是 `test_block_speedups.py::test_prefix_unknown_pruned_only_by_probe_unsat`。
  - 原因：修法 4 的预期结果，不是代码缺陷。这条测试只把增量检查强制成 unknown，想单独检验 bvmul→UF 探针。修法 4 之后，增量检查 unknown 时先跑 blast 过的**精确**查询；`x*x == 6` 在 8 位上本来就不可满足，blast 查询直接给出 unsat 并剪枝，所以断言“被保留”失败。这次剪枝是正确的：精确 unsat 就是路径不可行。
  - 修复（只改测试）：同时把标签为 `"blast"` 的 `_bounded_check` 强制为 unknown，让这条测试重新只检验探针。blast 查询的行为另有 `test_block_remaining_blocks.py` 中三条专门测试（恢复见证、unsat 剪枝、unknown 时保留）。修复后按节点 ID 单独运行 1 passed；旧版本测试仍是 1 failed；整个文件 16 passed。
- 修复后的全量结果见 §9.1。

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

任务 N 的会话中断前没有跑完。在任务 N2 中改用**冻结版**机器码复核，见 §9.4。

### 6.4 Permit2 1327 d10 符号整节点

任务 N 的会话中断前没有跑完。在任务 N2 中改用**冻结版**机器码复核，见 §9.2、§9.8、§9.9。

### 6.5 PoolManager 16670 m=768（限时后）与 6084

任务 N 的会话中断前没有跑完。在任务 N2 中改用**冻结版**机器码复核，见 §9.5。

## 7. 诊断工具（`cloud-inputs/n/tools/`，仅用于诊断）

- `dump_paths.py`：跑到 pair 阶段为止，导出前提、每条路径条件、对应关系与指定 pair；或导出名字匹配的义务（如 `evm_assumption_7`）。
- `build_maps.py`：按 `_check_rows` 的做法重建 `x86_maps_J_K`。`row_tails.py`："all" 行的末项。
- `empty_row.py`：某 x86 行的空行提议和 `x86_empty_J` 的 `_check`。
- `x86_profile.py`：x86 分段剖析（分叉、可达性耗时、summary 命中/拒绝及失败义务、互补检查命中），导出被拒命中前提与失败的 summary 查询。
- `entry_sat.py`、`segment_jcc.py`、`show_block.py`。
- `trace_node.py`：整节点逐义务计时，并统计 `_unify_node` 的耗时与 `_prove_equal` 成败。
- `regress.py`：SMT2 上跑生产 `_check`。`without.py FIX TOOL ...`：关掉某个修法再跑（A/B）。

## 8. 未完成的块及原因

以冻结版机器码为准（任务 N2，§9）：

| 合约 | 块 / 实例 | 状态 | 原因 / 瓶颈 | 下一步 |
|---|---|---|---|---|
| Permit2 | 1327 sym / m192 | 见 §9.9 | r4 的 `pair_0_3` 已消除（`x86_empty_3` 证出）。剩下的是预算问题：924 个义务，每个 maps 义务约 21–25s，另外 `_unify_node` 要 1500–2200s；进程内存随运行时间增长（sym 在 20405s 时 10.5GB，被 OOM 杀掉） | 节点内并行（`BLOCK_PAIR_WORKERS`），或更大的预算/内存；进一步压缩 maps 义务的固定开销（`quick0`、normalize 中未缓存的部分） |
| Aave | 7200 | 未跑完（§9.4） | x86 分段：summary 都能应用，但同一组 summary 在每条路径上重复（每圈约 2600s）；进程 8GB | summary 命中证书在节点内复用 |
| Aave | 6182、8248 | 未在冻结版上跑 | 本机内存与时间不够（6182 是预算类，8248 曾被 OOM） | 服务器 |
| PoolManager | 16670 m=768 | inconclusive | `pair_2_74` goal 2：SDIV 符号分支下的 UF 参数合并（§9.5） | 实现“按守卫分情形后再合并”，并让各情形、兄弟 pair 共享合并结果 |
| PoolManager | 16670 另外两个实例 | 未跑 | 时间不够 | 同上 |
| PoolManager | 6084 | 预算类，另有卡住的义务 | 4028 个义务；`x86_maps_0_0` 是 10 级内存扩展费链，所有路线 unknown | potential 路线对长扩展链的支持 |
| PoolManager | 4418 sym / f=320 | 预算类（路径数） | x86 877 条路径，1h 内进不了 pair 阶段 | x86 路径合并或 summary |
| PoolManager | 9089 | **已证出**（10643s） | — | — |

## 9. 冻结版机器码复核（任务 N2）

输入：`cloud-inputs/n2/fixtures/`（Permit2、Pool=Aave、PoolManager；已用 `sha256sum -c` 对照 `cloud-inputs/n2/FROZEN_SHA256SUMS` 核对，一致）。代码：本分支 = 任务 N 的 6bbad7f（修法 1–7）+ §5.1 的一处测试修正 + **修法 8**（§9.7，d28298f 起：已证恒等式跨义务记忆化，只影响耗时）。各次运行用的是哪个版本，在相应小节中注明。本机 4 核 / 15GB，z3 4.15.4，capstone 5.0.6；每个查询 30s，`BLOCK_SUMMARY_LEMMAS=1 PYTHONHASHSEED=0`。长任务通常 3 个并行。

运行脚本：`cloud-inputs/n2/tools/run_probe.sh`，它调用 `probe_traced.py`：原样运行 `tools/probe_block_obligations.py`，另外给每个 `_check` 记一行耗时日志。节点文件在 `cloud-inputs/n2/nodes/`，完成的结果在 `cloud-inputs/n2/results/`。
会话中途容器重启过一次，当时在跑的任务全部中断。中断前的日志保存在 `results/partial-r1/`，这些任务之后从头重跑。

### 9.1 全量快测

- 开工时（6bbad7f，即任务 N 的最终代码）：1 failed, 1768 passed, 3 skipped（`-n 4`，524s）。唯一的失败已在 §5.1 说明并修正，只改了测试。
- 最终代码（修法 1–8 + 测试修正，`poetry run pytest tests/unit -q -m "not slow" -p no:cacheprovider -n 2 --dist=loadscope`，同时有两个整节点证明在跑）：**1775 passed, 3 skipped, 0 failed（693s）**。新增的 6 条测试都在 `tests/unit/test_block_remaining_blocks_2.py` 中，逐个按节点 ID 单独运行均为 1 passed。
- 修法 8 的 6 条测试在旧代码上：3 条失败（只查一次、同一次调用内不重试、兄弟义务复用证明），说明能区分新旧行为；另外 3 条是不变量（失败后会重试、不会证出非恒等式、`clear_memo` 会清空），新旧代码上都通过。
- 并行运行时有一条负载敏感的测试失败：`test_block_uf_unification.py::test_alias_split_keeps_satisfiable_pairs_open`（与 4 个重进程一起运行时）。单独重跑通过。在上面的最终全量运行中也通过了。
- `-m slow` 中有两条测试（`test_safe_9733_*`、`test_safe_11803_*`）读取 `tests/data/block_obligations/`，该目录不在仓库中，所以报 `file access error`。这是已有问题，与本任务无关，也不在快测范围内。

### 9.2 Permit2 1327（冻结版）

- 两个实例的 pair 阶段相同（852s）：EVM 61 / **x86 43** 条路径（任务 N 的旧机器码为 65 条）。对应关系为 `[0, 0, all, None, None, None, all×10, 39, 28, 17, None, 16, 15, 14, 60, 54, 53, 49, 48, 47, 46, 45, 12..1]`。
- **r4 的 `pair_0_3` 消失了**：x86 行 3 是 `terminal@73543`，即 r4 失败信息中的那条路径。它的首个合取项是 `Extract(64,64, zext(8·len) + zext(1125 + 扩展费)) == 1`，也就是任务 N §2.2 的 LOG2 费用溢出检查（旧编号 x86 路径 6）。修法 2 让空行提议成立（`_empty_by_bvabs` 用时 42.1s），对应关系从 `0` 变成 `None`（空行）。
- `x86_empty_3`（`empty_row.py`，生产 `_check`）：**140.8s proved**（186 条引理）。SMT2 存于 `cloud-inputs/n2/smt2/permit2_1327_frozen/x86_empty_3.smt2`，与旧机器码的 `x86_empty_6.smt2` 大小相同，只有 let 绑定名不同。日志见 `results/p2-1327-row3.log`。
- 其余 "all" 行（2、6–15）的首项都是普通错误路径：内存字数上限 `32w < 2^37`、gas 不足、`fmp+32` 溢出、零检查。**没有其他 LOG 费用溢出类的行。**
- 节点级合并：第一次运行（被重启中断）中，`_unify_node` 对 924 个义务用了 1590.0s，得到 9 条引理；之后 `x86_maps_0_*` 逐个 unsat，每个约 33–36s。
- 整节点结果：（运行中）

### 9.3 SMT2 回归（生产 `_check`）

用 `cloud-inputs/n/tools/regress.py` 运行：每个文件一个新的 prover，每个义务上限 1800s，同一进程内按表中顺序依次运行。与 1–2 个整节点证明并行。日志见 `results/regress-smt2.log`（修法 1–7）和 `results/regress-smt2-fix8.log`（修法 1–8）。

| 来源 | 义务 | 任务 N 报告 | 修法 1–7 | 修法 1–8 |
|---|---|---|---|---|
| r3c | 5802 `model_domain_nonempty`（预期 sat） | 0.3s sat | 0.4s sat | 0.3s sat |
| r3c | 4837 `x86_maps_12_0` | 23.4s | 24.4s | 18.4s |
| r3c | 4837 `x86_maps_14_0` | 13.7s | 13.9s | 14.2s |
| r3c | 1327 `x86_maps_0_0` | 76.9s | 78.4s | 76.6s |
| r3c | 1327 `x86_maps_0_1` | 51.7s | 57.7s | 45.8s |
| m | 1327 `x86_maps_0_46` | 85.4s | 96.0s | 77.8s |
| m | 1327 m192 `x86_maps_0_46` | 95.2s | 96.0s | 85.2s |
| m | 1327 `pair_0_6`（任务 M：5925s unknown） | — | **191.0s** | **172.4s** |
| m | Aave 8248 `pair_0_1` | 1231.5s | 1244.2s | 1236.5s |
| n | Aave 11831 `evm_assumption_7`（只走 `_check`，见下） | — | 12.9s | **1029.9s unknown** |
| n | 1327 `x86_empty_6` | 147.4s | 154.9s | 167.9s |
| n | 1327 `x86_empty_7` | 127.9s | 157.5s | 153.0s |
| n2 | 冻结版 1327 `x86_empty_3` | — | 140.8s（`empty_row.py`） | 142.5s |
| n | Aave 7200 被拒命中前提（预期 sat） | 直接查询 30.4s unknown | 直接查询 30.3s unknown；常函数 UF 0.4s unknown；**blast 5.9s sat，模型在原式上求值为 true** | （修法 8 不涉及） |

除 11831 外，其余结果都与预期一致，没有退化；耗时差异在并行负载的波动范围内。修法 8 之后，Permit2 / 4837 的几条 maps 义务快了 0–20%。

**11831 `evm_assumption_7` 的 unknown 不是修法 8 造成的退化**（`results/regress-11831/`）：
- 这个文件只走普通 `_check`，结果取决于计时。成功的那次（12.9s，1 条引理）是在 `lia` 路线中证出的；该路线的 LIA 查询上限 `_LIA_MS = 10s`，证出时贴着这个上限。
- 单独运行（上限 300s）：修法 8 之前和之后都是 unknown（236s / 235s）。
- 前面只放一个 `x86_maps_14_0`：修法 8 之前和之后也都是 unknown（241s / 238s）。
- 前面放与回归相同的 7 个文件，用 `trace_after.py` 逐路线计时：修法 8 之前和之后都是 unknown（411s / 409s），两边 `lia` 都在约 12s 时给出 unknown，各路线耗时几乎相同。
- 前缀相同、上限 1800s 时，修法 8 之前的版本在 `results/regress-pre8-prefix.log` 中证出（12.9s），但这一结果不能稳定复现。
- 生产中这条执行假设走 `check_paths` 的候选列表，乘积字泛化（修法 1）排在最前，0.0s 证出。对应测试 `test_aave_11831_evm_assumption_7_is_proved_by_word_generalisation` 在最终全量快测中通过。

### 9.4 Aave 7200 x86 分段（冻结版 Pool，修法 1–7）

`x86_profile.py --seconds 10800`。两次都没有跑完：第一次被容器重启打断（`results/partial-r1/aave-7200-x86.log`）；第二次（`results/aave-7200-x86-r2-oom.log`）在 9464s 时被内核 OOM 杀掉，当时 RSS 7.8GB，同时还有 Permit2 1327 的 7GB 进程在跑。
- **修法 3–7 在冻结版上起了作用**：没有任何 summary 命中被拒，也没有回退到原始的复制循环。每个命中都照常应用：`copy_loop@0x6ee68`（340–360s，其中 `copy_domain` 60–70s）、7 个 `memgas`（每个 60–80s，其中 `entry` sat 35–55s、`memgas_exit_guard_excluded` 23–28s）、2 个 `div`（每个 490–570s，其中 `entry` sat 41–58s）。补集检查共命中 46 次（22.6s）。
- **瓶颈是同一段代码被反复执行**：上面这组命中按 copy_loop → memgas×3 → div → memgas×3 → div → memgas 的顺序循环出现，每圈约 2600s，每圈对应一条新的路径。9464s 时共执行 817 个基本块，可达性检查 449 次（2315s），剪掉 117 个分支，还没有任何路径到达终点。
- 修法 3–7 之前（任务 N 服务器）的失败原因是 `x86 segment execution deadline exhausted`，当时的卡点是 summary 被拒后逐圈展开复制循环。现在的卡点是每条路径都要单独付全部 summary 的代价（`entry` 求解与 `div` 的义务）。可行的通用方向是在同一节点内复用 summary 命中的证书（前提相同时），本任务没有实现。
- 整段要单独跑才能跑完（内存 8GB 以上），这需要等 Permit2 1327 m192 结束之后（§9.9）。

### 9.5 PoolManager 16670 m=768、6084（冻结版）

**16670 m=768 整节点**（修法 1–7，`results/pm-16670-m768.{json,log}`）：**inconclusive**，16405s，原因 `outcome mismatch pair_2_74: terminal@16670 / terminal@689761 (solver=unknown)`，与服务器上的失败是同一个义务。
- 时间线：pair 阶段 212s（EVM 3 / x86 83，对应关系完整）；`_unify_node` 对 87 个义务用了 5418.2s（修法 6 给的上限，即剩余预算的 1/4），只得到 2 条引理；之后 `x86_maps_*` 很快，`pair_2_74` 的 goal 0、1 各 0.1s，**goal 2 单独用了 10664.8s，结果 unknown**。
- **根因**（`results/pm16670/`、`cloud-inputs/n2/smt2/pm16670/pair_2_74_goal_2_of_7.smt2`）：块 16670 是 `SDIV; …; SAR 8; MSTORE ×2; SHA3(0,0x40)`，goal 2 是内存观测量。EVM 端的 SDIV 是 `holiman_udiv(|a|, |b|)`，其中 `|x| = If(sign(x), 0−x, x)`；x86 端是按符号分支的树，每个分支各有一个 UF 应用，参数为 `(a,b)`、`(−a,b)`、`(a,−b)`、`(|a|,|b|)`，共 6 个 `holiman_udiv` 应用。这些参数**只在对应的符号分支下才相等**，无条件比较时并不相等。`uf_args.py` 显示：同一类的参数对 0.1–1.2s 就能证等，跨类的参数对 20s unknown。所有路线都失败（单独运行 1289s unknown；unify 路线 30 个 `_prove_equal` 中只成功 2–3 个）。
- **候选通用修法（已离线验证，未进生产）**：在 UF 参数合并**之前**，先按 UF 应用之上的 ite 守卫分情形（`guard_split.py`），每个情形内再做 `unify_uf_arguments`，然后求解。只按最小的守卫（两个操作数符号相同）分 2 个情形：**两个情形都 unsat**（622s、601s，分别合并 21 次、34 次）。按 4 个守卫分 16 个情形时，前 3 个情形各 100–500s。
  - 健全性：与 `_refute_by_cases` 相同。c 与 ¬c 覆盖所有模型，`F[c:=v]` 在对应文字下与 F 等价，每个情形里的合并仍由被反驳的查询支持。所以所有情形都 unsat 时 F unsat。
  - 未进生产的原因：每个内存目标约 1200s，而 83 个 pair 都有这个目标，6h 放不下。还需要让情形之间、兄弟 pair 之间共享合并结果（`_lemma_cache`），本任务没有完成。
- 另外两个 16670 实例（符号 7296 / 7324）没有跑。

**6084 m=864 f=768**（修法 1–7，`results/pm-6084-triage.log`）：pair 阶段 593s（EVM 56 / x86 114），节点共 **4028 个 pair 阶段义务**，`_unify_node` 用了 11.4s。第一个义务 `x86_maps_0_0` 在 `_check` 中卡了 2800s 以上（py-spy 看到在 unify 路线中），之后由会话停止。单独运行 `route_trace`：1800s 内所有路线 unknown（`results/pm6084/trace_maps_0_0.json`）。EVM 0 的第 0 个合取项是 gas 检查：约 10 级内存扩展费（围绕 `stack_1`/`stack_2` 的符号偏移做 MLOAD/MSTORE）之和 ≤ `gas_remaining`。这和任务 N 中 9089 `x86_maps_0_9`（5 级）是同一类，但链更长：potential 路线 231s unknown。即使这一项能证出，4028 个义务在 6h 内也跑不完，所以 **6084 属于预算类，另有一个卡住的 gas 链义务**。SMT2 存于 `cloud-inputs/n2/smt2/pm6084/x86_maps_0_0.smt2`。

### 9.6 PoolManager 9089、4418（冻结版）

- **9089 整节点（修法 1–8）：proved**，10643s，4932 个查询，29 次 summary 命中（`results/pm-9089.{json,log}`）。
  - pair 阶段 683s：EVM 35 / x86 50，对应关系中只有 1 个 "all" 行。
  - `_unify_node`：728 个义务，3.8s。
  - 最慢的义务：`pair_34_0` 212.5s，`x86_maps_0_9` 196.3s（即任务 N §2.6 中节点内 1100s unknown 的那个），`x86_maps_2_7` 188.1s。
  - r4 失败的 `pair_34_25` 没有出现：本次 x86 行 25 被提议为空行，`x86_empty_25` 57.1s 证出。
  - 1h 分诊（修法 1–7，`--keep-going`，`results/pm-9089-1h.*`）：没有失败，平均每个义务约 11s，当时按此估计整节点约 9400s。
- **4418 符号，1h 分诊**（修法 1–8，`--keep-going`，`results/pm-4418-sym-1h.*`）：EVM 63 / **x86 877** 条路径，548 个查询，**1h 内没有进入 pair 阶段**，也没有任何失败。时间全部花在 x86 路径枚举和对应关系上。瓶颈仍然是路径数（任务 N 为 885 条），修法 1–8 没有改善。
- **4418 f=320，1h 分诊**：见 §9.9。

### 9.7 修法 8：已证恒等式跨义务记忆化

- 问题：`normalize_word_arith` 对每个候选改写证明 old == new（`_identity_proof`，每次最多 1s）。同一节点的兄弟义务共享前提和路径项，会反复遇到相同的改写。冻结版 1327 的 `x86_maps_0_5/0_10/0_20`（`normalize_profile.py`）：每个义务 199 次恒等式证明，第二个起有 191–192 次是之前证过的（约 23s，占 24s 中的大部分）；即使在同一个义务内，各轮之间也重复了 81 次。
- 改动：
  - `verification/block_equivalence.py:828` `_identity_proof`：证出的结果按 (old, new) 的 AST id 记忆化，放在 `common.store_forwarding` 的节点级 memo 中（每个节点开始时 `clear_memo` 清空，并有条目上限）。失败**不**跨调用缓存。
  - `verification/block_equivalence.py:1069` `normalize_word_arith`：同一次调用内，不重试已失败的 (t, new)，这是同一个查询。
  - `common/store_forwarding.py:78` `_memoized`：新增可选参数 `keep`，只缓存满足条件的值。
  - 非 AST 参数（如 new 为 None）不走记忆化。
- 健全性：old == new 是否恒真只取决于这两个项，与它出现在哪个义务中无关，所以一次证出的结果在所有义务中都成立。记忆的值就是原来的证明（引理），证书结构不变。memo 保留 AST 引用，id 不会被复用。不重试只可能少证一个改写，不会多证。失败不跨调用缓存，是因为第一版缓存了失败时，`x86_maps_0_20` 少了 1 条改写（160 → 159 条引理）；现在的版本引理数与修法前一致。
- 效果（`--plain`，离线）：兄弟义务的 normalize 从 23.5s / 26.1s 降到 16.8s / 15.4s。在节点内，冻结版 1327 每个 maps 义务平均从 24.7s（修法前，sym 实例前 150 个）降到 21.0s（修法后，m192 实例），提升有限：节点内还有其他固定开销（`quick0` 约 3s、blast 查询、pin）。
- 测试：`tests/unit/test_block_remaining_blocks_2.py` 共 6 条（见 §9.1）。回归见 §9.3。

### 9.8 Permit2 1327 整节点

- **sym（修法 1–7，`results/p2-1327-sym-oom.log`）**：没有任何义务失败，但在 20405s 时被内核 OOM 杀掉（RSS 10.5GB，内存随运行时间持续增长：14000s 时 7GB）。
  - 时间线：pair 阶段 852s，`_unify_node` 1524.8s（924 个义务，9 条引理），4551s 起开始检查义务。
  - 进度：到 20405s 共证出 **588/924** 个义务：498 个 maps（10412s）、86 个 pair（4987s）、4 个空行（453.8s，其中 `x86_empty_3` 174.5s），unknown 为 0。
  - 剩余 336 个义务按当时的速度还需约 9000s，所以修法 8 之前整节点约需 29000s，**超出 6h 预算**。即使没有 OOM，也会以预算耗尽结束，而不是卡在某个义务上。
- **m192（修法 1–8）**：见 §9.9。

### 9.9 汇总（冻结版）

（运行中，最后更新）
