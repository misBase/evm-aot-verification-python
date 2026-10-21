分支：`claude/inputs-n-remaining-blocks-rm2fog`（会话只允许推送 `claude/...` 分支，未使用任务书建议的 `cloud/remaining-blocks`）。基线 = `cloud/inputs-n`（d15c606，即任务 M 的 3F）。

# 任务 N：剩余块 —— 根因与通用修法

> 草稿：数据仍在补充，§1 表中标 "待定" 的项会在后续提交更新。

## 1. 结论

**没有出现任何 SAT（反例）**，因此不需要做具体执行，也没有发现编译器问题。本次找到并修掉三个通用根因：

| 合约 | 块 / 实例 | 义务是否成立 | 根因 | 修法 | 修法前 | 修法后（本机） |
|---|---|---|---|---|---|---|
| Aave | 11831 d12 m=96 f=128 | 成立 | `evm_assumption_7` 是 EVM 侧 256 位比较的桥接提示：`P == 1e27 ⇔ (P−1e27 与 1e27−P 都不借位)`，P 是逐 limb 计算的 256 位乘积 `x·1e27`。它对任意 256 位字都成立，但现有的泛化只把每个 `bvmul` 换成新常量，limb 仍是带进位的和，30s 仍 unknown | **修法 1：乘积字泛化**（`_generalize_product_words`） | 209s inconclusive（`evm_assumption_7` 202.9s unknown） | **整节点 74.5s proved**（该义务 0.0s） |
| Permit2 | 1327 d10 符号 | 成立 | `pair_0_6` / `pair_0_7` **不是** SSTORE 的 gas 等价问题。x86 路径 6/7 的最后一个合取项是 LOG2 费用 `8·len + 1125 + 扩展费` 的 **64 位溢出检查**（x86 先算费用、再查溢出）。路径前缀已检查新内存尾 `32w < 2^37`（w < 2^32），所以费用 ≤ 2^40 + 1125 + C(2^32−1) ≪ 2^64，**x86 路径 6/7 本身不可行**，与 EVM 无关。证明它需要 `C(w)=3w+⌊w²/512⌋` 的上界与单调性；P 抽象把 C 当任意函数，于是 abstract-SAT，精确求解卡在平方上 | **修法 2：内存势函数的值域/单调公理**（`potential_range_axioms`，用于 potential 路线的最后一步和"空行"提议） | 行 6/7 为 "all"：`pair_0_6` 5925s、`pair_0_7` 1943s unknown（任务 M 本机） | 行 6/7 改为空行：**`x86_empty_6` 147.4s、`x86_empty_7` 127.9s proved**（提议 43.0s / 41.4s） |
| Aave | 7200 d13 m=96 f=128 | 待定（x86 执行先要能做完） | **x86 符号执行超时的根因**：路径条件一旦让可达性检查 unknown，路径就丢了模型见证；之后每个 summary 命中都要单独证明入口前提 SAT（`entry`），这个查询要 17–37s，在 30s 预算附近徘徊。超时（unknown）时 summary 被**拒绝**，回退到逐指令执行：符号长度的 CALLDATACOPY 复制循环（copy_loop@0x72fc8）每转一圈都重新命中、再花约 53s 尝试 summary、再被拒绝，于是逐圈展开直到 6h 预算用完。这属于"已有 summary（copy-loop、memgas）应当覆盖却没覆盖"：summary 本身都能证，只是被一个与健全性无关的 SAT 检查挡住 | **修法 3：入口未判定时照常证明 summary**（`VerifiedSummaryRuntime.apply`） | 服务器 21603s `x86 segment execution deadline exhausted`；本机复现：拒绝从 `memgas@0x72dd4` 开始，之后 `copy_loop@0x72fc8` 每圈 53s 被拒 | 待定（x86 分段执行剖析进行中） |
| PoolManager | 9089 d2 符号 | 成立（单条义务已证） | 本机 1h 分诊：卡在 `x86_maps_0_9`（x86 路径 0 ⇒ EVM 路径 34 的合取项 9，即 RETURN 前的内存 gas 检查，带 5 级扩展费链）1100s unknown。单独用生产 `_check` 跑：**153.1s proved**（blast* 路线中的 potential 重试） | 见 §6（修法 2 是否起作用的 A/B 正在跑） | 1100s unknown（节点内） | 153.1s proved（单独） |
| Permit2 | 1327 d10 m=192 f=128 | 1h 内无失败 | 1h 分诊：1892 个查询，`keep_going_failures` 为空，预算用完 | — | 任务 M 未跑 | 1h 无失败；整节点待跑 |

服务器上 PoolManager 9089 的 `x86_maps_7_0` / `8_0` 为 SAT：这只是对应关系的提议错了（行 7/8 退回 "all" 行后逐个 pair 证明），**不是反例**。判断依据见 §2.4。

## 2. 逐块分析

### 2.1 Aave 11831 `evm_assumption_7`

块 11831 = `POP PUSH 1e27 SWAP2 MUL PUSH 5e26 ADD DIV`（rayDiv）。EVM 执行器给乘积 `P = x·1e27`（逐 limb 计算的 256 位字）的 EQ/LT 比较留了一条桥接假设：`(P == 1e27) == (¬borrow(P − 1e27) ∧ ¬borrow(1e27 − P))`，借位按 65 位逐 limb 链写出。`check_paths` 要求每条这样的执行假设都被证明（不能悄悄缩小证明域）。

- 这条假设对任意 256 位字 P 都成立。原有的两个候选：`_generalize_products`（把每个 `bvmul` 换成新常量）后，P 的各 limb 仍是若干新常量带进位的和，30s unknown；`div_quotient_axioms` 不适用。
- 把整个乘积字（`Concat(l3,l2,l1,l0)`，≥128 位且含 `bvmul`）换成一个新常量后，查询 0.0s unsat。

### 2.2 Permit2 1327 `pair_0_6` / `pair_0_7`

- 用 `cloud-inputs/n/tools/dump_paths.py` 拿到前提、61 条 EVM 路径、65 条 x86 路径。`_correspondence` 给出的行 6、7、8 都是 "all"。
- x86 路径 6 的 136 个合取项里，最后一项（`conj 0`）是 `Extract(64,64, zext(8·len) + zext(1125 + t24)) == 1`，t24 = `If(new ≤ msize, 0, C(new) − C(old))`，即 LOG2 费用在 64 位里溢出。路径前缀里已有：`32w < 2^37`（新内存尾检查）、`8·len` 不溢出 128 位低半、`fmp + len` 不回绕。
- 所以 x86 路径 6 自身不可行：w < 2^32 ⇒ C(w) ≤ C(2^32−1) ≈ 2^55，len < 2^37 ⇒ 8·len < 2^40，C(old) ≤ C(new)（单调），和远小于 2^64。
- 为什么所有路线都失败：精确求解要 bit-blast 8 个 64 位平方（30s unknown）；乘法抽象 + 平方单调性（`refute_over_bv_abstraction`）没有平方的绝对上界，abstract-SAT（1.2s）；potential 路线把 C 换成任意函数 P，同样 abstract-SAT（1.4s）。
- 加上 P 的值域与单调公理之后：bvabs 3.1s unsat，精确 8.6s unsat。只有值域、没有单调也是 SAT（因为要用 C(old) ≤ C(new) 去掉减法）。

### 2.3 Aave 7200 x86 分段执行

- 静态规模（`segment_jcc.py`）：0x6d87e..0x76f89，7380 条指令，556 个条件跳转，180 个 ret（错误出口/桥）。
- 剖析（`x86_profile.py`，REACH_STATS_FILE）：主路径基本是线性的（每个分叉的另一边是错误 stub）。可达性检查在路径条件变大后多为 unknown（incremental unknown 平均 3.9s，接着的乘法抽象探针 unknown 平均 2s），路径的模型见证随之丢失。
- 此后每个 summary 命中都要单独解入口前提：`entry` 是 SAT 查询，实测 17.6–24.7s（sat）或 30.4s（unknown）。捕获的一个被拒前提（`rejected_entry_71f8d`）单独求解 36.5s sat，没有 UF，常函数见证不适用。
- 被拒后的回退：`copy_loop@0x72fc8`（符号长度的 CALLDATACOPY 字节复制循环）每圈命中一次、每次约 53s 后被拒、执行一圈原始代码，再命中……逐圈展开。三次运行中，拒绝出现的位置随负载变化（0x719d4 / 0x72dd4），说明是预算边界问题。

### 2.4 PoolManager 9089

- 本机 1h：EVM 35 条路径，x86 51 条路径，869 个查询；唯一记下的失败是 `x86_maps_0_9`。
- `x86_maps_7_0` / `8_0` 为 SAT 的含义：`x86_maps_j_k` 是"x86 路径 j ⇒ 被提议的 EVM 路径的第 k 个合取项"。SAT 只说明行 j 不对应那条 EVM 路径；`_pair_phase` 把这一行退回 "all"，第二轮逐个证明 `pair_i_j`，失败的提议不进入证书（`BlockTheorem.complete` 只看最终对应关系下的清单）。所以它不是反例。

## 3. 改动位置

- `verification/block_equivalence.py`
  - 修法 1：`_generalize_product_words` L327；`check_paths` 的执行假设候选（先试乘积字泛化）L4224 附近。
  - 修法 2：`_POTENTIAL_WORDS`、`_POTENTIAL_MONOTONE_APPS` L1243；`potential_range_axioms` L1247；`refute_over_bounded_potential` L1281；`_retry_over_potential` 的最后一步 L3770 附近；`_empty_by_bvabs` 的第二个尝试 L3644。
- `verification/block_summaries.py`
  - 修法 3：`VerifiedSummaryRuntime.apply` 中 `entry` 检查的异常分支（L945 附近）。
- 测试：`tests/unit/test_block_remaining_blocks.py`。
- 数据：`cloud-inputs/n/smt2/`（`aave_11831_evm_assumption_7.smt2`，`permit2_1327/x86_empty_6.smt2`、`x86_empty_7.smt2`）。
- 诊断工具：`cloud-inputs/n/tools/`（见 §7）。

## 4. 健全性论证

- **修法 1（乘积字泛化）**：G = F[w_i := c_i]，c_i 是新常量，w_i 是 F 中含 `bvmul` 的极大宽 concat 子项。若 ¬G 不可满足，G 对 c_i 的任意取值都成立，F 是 G 在 c_i := w_i 下的代换实例，所以 F 有效。只是在原有候选之前多试一个候选：候选不成立（sat/unknown，5s 上限）时落到原来的候选和原来的 `_check`。它只能多证出有效的假设，不会让无效的假设通过（测试 `test_generalised_words_do_not_prove_a_non_tautology`）。
- **修法 2（P 的值域/单调公理）**：`abstract_memory_potential` 把 C(w) 的平方部分 E(w) 换成 P(w) − 3w（P 读作 C 时恰好还原），只增加模型；`telescope_potential` 是在 P 读作 C 的公理下的等价变换（其恒等改写有证明，记为 lemmas）。新增的公理：对每个 P(a)、P(b)（位宽 n ≥ 64，W = 2^32−1）
  - `a ≤ W ⇒ P(a) ≤ C(W)`；
  - `a ≤ b ≤ W ⇒ P(a) ≤ P(b)`。

  P 读作 C 时：a ≤ W ⇒ a² < 2^64 ≤ 2^n 不回绕，3a + ⌊a²/512⌋ < 2^n，C 在 [0, W] 上不减，所以每条公理都成立，合取后保留原公式的全部模型。之后 `refute_over_bv_abstraction` 再做乘法抽象和数组泛化，也只增加模型。因此只有 unsat 有意义，此时原公式 unsat。位宽 < 64 时不生成公理（`test_no_range_axioms_below_64_bits`）；单调公理是 O(k²) 的，超过 32 个 P 应用时只保留值域公理（只是少证）。在 `_empty_by_bvabs` 中它只是一个**提议**：行被标为空之后，`x86_empty_j` 仍由 `_check` 独立证明；提议错了只会让 `x86_empty_j` 失败、退回 "all"。
- **修法 3（入口未判定）**：summary 证书证明的是"对满足前提 P 的每个状态，原始切片 = summary 效果"。这一结论来自 coverage、effect、copy_domain、copy_param_*、exit_guard_excluded 等 **UNSAT 查询**（P ∧ ¬目标），它们对 P 可满足与否都成立；P 不可满足时整个命中是空洞的（路径本身不可行，后面的 pair 义务也空洞成立）。`entry`（P 可满足）只用来区分"空命中"（`dead_hit`，答案 unsat 时照旧处理）和正常命中，不是任何结论的前提。修法只改了 `entry` **unknown** 的情形：不再拒绝，而是把记录的 expected 写成 `unknown`（证书里如实显示"未判定"），其余所有义务照常必须证出；任何一条失败照旧拒绝并回退（`test_undecided_entry_does_not_excuse_a_failed_obligation`）。`entry` 被判为 unsat 的情形不变（`test_refuted_entry_is_still_rejected`）。
- 没有"提议出错就会误证"的通道：乘积字的选择、公理的实例、空行提议都只是候选；每个结论最终都落到被反驳的查询，或落到对所有解释都成立的公理上。

## 5. 测试结果

- 新增 `tests/unit/test_block_remaining_blocks.py`，逐个按节点 ID 单独运行，全部 1 passed（含两条真实 SMT2 用例，各约 10–12s）。
  - 修法 1：乘积字被泛化且结果有效；没有乘积/没有宽字时不泛化；非恒真式不会被证出；Aave 11831 真实 SMT2 经 `check_paths` 证出（<5s，且送进 `_check` 的是泛化后的查询）。
  - 修法 2：溢出的 LOG 费用只有加上公理才被反驳（去掉公理不适用，只有 P 时 abstract-SAT）；公理在 P 读作 C 时对 200 组随机值都成立；< 64 位不生成；单调公理有上限；1327 行 6/7 的真实 SMT2 被反驳。
  - 修法 3：`entry` 未判定时 memgas summary 照常应用、证书完整、其余义务全部 unsat；未判定不能掩盖失败的义务；`entry` 为 unsat 时照旧拒绝。前两条在旧代码上失败（已确认测试能区分新旧行为）。
- 全量快测 `pytest tests/unit -m "not slow" -p no:cacheprovider`：修法 1–2 后 **1757 passed, 3 skipped, 0 failed**（基线 1747）。修法 3 之后的全量结果见后续更新。
- 负载敏感的已有测试：`test_mcopy_induction.py::test_symbolic_length_mcopy_has_complete_certificate[mcopy-high-word]` 在本机 5 个重进程并行时出现过一次 `step_1_other: unknown`（20s 预算的引理查询），单独运行 2 passed（161s）。与本次改动无关（失败的是引理查询，不是 `entry`）。

## 6. 离线验证数据（本机：4 核，z3 4.15.4，每查询 30s，多任务并行）

| 对象 | 修法前 | 修法后 |
|---|---|---|
| Aave 11831 整节点（1h 预算） | 服务器 209s inconclusive（`evm_assumption_7` unknown） | 74.5s proved（16 个查询） |
| Aave 11831 `evm_assumption_7`（单独） | `_generalize_products` 30.6s unknown，直接 30.2s unknown | 乘积字泛化 0.0s unsat |
| Permit2 1327 `premise ∧ x86_6`（bvabs / 精确） | 30.4s unknown / 30.2s unknown | 3.1s unsat / 8.6s unsat |
| Permit2 1327 `x86_empty_6` / `x86_empty_7`（生产 `_check`） | 行为 "all"：`pair_0_6` 5925s / `pair_0_7` 1943s unknown | 147.4s / 127.9s proved |
| PoolManager 9089 `x86_maps_0_9` | 节点内 1100s unknown | 单独 153.1s proved（blast*） |

## 7. 诊断工具（`cloud-inputs/n/tools/`）

- `dump_paths.py STEM NODES.json IDX OUT [--pairs I_J,..] [--names RE --stop-on-name]`：跑到 pair 阶段为止，导出前提、每条路径条件、对应关系提议和指定 pair；或导出名字匹配的义务（如 `evm_assumption_7`）。
- `build_maps.py DUMP EVM_I X86_J K|all OUT`：按 `_check_rows` 的做法重建 `x86_maps_J_K`。
- `empty_row.py DUMP J...`：某 x86 行的空行提议（`_empty_by_bvabs`）和 `x86_empty_J` 的 `_check`。
- `x86_profile.py STEM NODES.json IDX`：剖析 x86 分段执行：执行块数、分叉、可达性耗时、summary 命中/拒绝及失败义务，被拒的 `entry` 前提导出为 SMT2。
- `entry_sat.py FILE`：用直接查询和常函数见证判定捕获的命中前提。
- `segment_jcc.py STEM PC`：x86 分段的静态规模。
- `regress.py FILE...`：在 SMT2 上跑生产 `_check`。`without.py FIX TOOL ...`：关掉某个修法再跑工具（A/B）。
- `show_block.py STEM PC`：打印 EVM 块。

## 8. 未完成的块

（分诊进行中，后续更新）
