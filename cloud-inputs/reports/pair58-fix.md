# 任务 A 报告：pair58 候选修法转正（pair58-fix）

分支：`cloud/pair58-fix`（基于 `cloud/inputs-5377` = develop-cutpoint + cloud-inputs，代码与 snap-r35b 一致）。

## 1. 结论

- `cloud-inputs/pair58/fix.diff` 的修法已正式实现到 `verification/block_equivalence.py`，并补了 7 条单元测试。实现与补丁只有一处不同：补丁里的 2s 探针没有受节点 deadline 约束，现在加了约束，剩余预算 ≤0 时直接跳过（z3 的 timeout=0 表示不限时，不加这个检查会失控）。
- 健全性：修法只会去掉一部分合取项。去掉合取项只会增加模型，所以只有 UNSAT 能传回原式；SAT 或 unknown 都退回原路线，不产生任何结论。
- 回归（服务器 reg_base 对比 reg_patched，共 22 条义务）：没有 unsat 变成别的答案，也没有 sat 变成 unsat。共 4 条答案变化，都能用时间预算解释（见 §5）。
- 离线验证（云端 4 核，4 路并行，每条 1800s）：修法后 `pair_58_13`、`pair_58_12`、`pair_63_10`、`pair_68_8` 均 proved，其中 `pair_58_13`、`pair_63_10`、`pair_68_8` 修法前都是 unknown；`pair_58_12` 修法前离线也能证（620s）。`pair_68_9` 在并行负载下修法前后都是 unknown，单独重跑的结果见 §6。
- 全量快测：1579 passed，2 skipped，35 failed。35 条失败全部是已知例外 `test_msize_absint`（依赖被忽略的 `tmp/prov_common.py`），除此之外没有失败。

## 2. 根因

材料：`pair58/diff_58_8_vs_13.txt`、`shape_*.txt`、`sha3args_58_13.txt`、`unify_*_f*.log`，以及服务器上的 `f2_*_all.log`。

- **义务形状。** 三条卡住的义务（a 的 `pair_58_13`、`pair_68_9`，b 的 `pair_58_12`）和已证的兄弟 `pair_58_8` 都是第 58/68 行 correspondence 的 "all" 行。目标里有两个 `sha3_slice` 应用，EVM 侧和 x86 侧各一个，第 0 个参数是内存切片 lambda。两侧 lambda 的写法不同：x86 侧把 CALLDATACOPY 的截断写成 `ite(bvule a!2 CallDataSize)`，EVM 侧写成 `bvule CallDataSize (CallDataSize + i)`，因此必须先由 `unify_uf_arguments` 证明两个参数相等（`sha3args_58_13.txt`："arg 0: direct unknown 1.1s"）。
- **和 `pair_58_8` 的差别。** 前提合取项：58_13 有 228 个，58_8 有 205 个，共有 204 个；58_13 多出 24 个（`diff_58_8_vs_13.txt` 中的 "ONLY A 24"）。多出来的都是内存扩张 gas 和 msize 的关系式，含 `memory_size_bytes` 的符号平方 `bvmul(concat(..extract(63,5) msize), concat(..))`，以及由 `fmp = mem[88..95]` 推出的多层 `extract(63,8)(256 + fmp)` 偏移（见 `shape_58_13.txt` 的 [2]–[13]）。在 58_8 里，这些偏移在同样的位置是 `383 + fmp`、`352 + fmp` 这类单层线性式（`shape_pair_58_8_*.txt` 的 [7]–[11]），不会生成 msize 的非线性平方和。
- **为什么卡住。** 证明 sha3 参数相等实际上只需要约 8 个线性合取项（0.3s 内 unsat）。但 `_prove_equal` 把整个前提（约 200 个合取项）交给 `unsat_core` 的 2s 探针和 `_refute_by_cases` 的 2s 叶节点，gas 平方和的位爆破使查询需要约 47s，所以每次都在 2s 预算内放弃（`unify_58_13_f2.log` 里大量 `_refute_by_cases ... -> NoneType`），合并失败，后续路线全部 unknown，最终耗尽约 2500–2800s 的节点预算。同理，合并之后的 `opaque_array_uf` 查询在 `pair_68_9` 上带着 gas 和需要 60s 以上，超过 30s 的单查询预算；去掉 gas 和只要约 6–10s（`unify_68_9_f2.log`："_refute_over_light_premise 6.0s -> tuple"）。
- **`pair_58_8` 为什么能证。** 它的偏移是单层线性的，`normalize_word_arith` 加 LIA 或精确路线在 88s 内就证出来了（`p58_8_all.log`），根本不需要走 unify 路线。

## 3. 修法内容（改动位置）

| 位置 | 内容 |
|---|---|
| `verification/block_equivalence.py:1797` `_heavy` | 合取项含"两个非字面量相乘"或"有参数的 UF 应用"时为真（gas 平方和、乘法抽象产生的 UF、host 结果） |
| `:1816` `_LIGHT_MS = 2000` | `_prove_equal` 里轻前提探针的固定上限，与 unsat_core 探针相同 |
| `:1819` `_refute_over_light_premise(parts, goal, budget_ms)` | 去掉无 binder 且 `_heavy` 的合取项，对剩下部分 ∧ goal 求解。UNSAT 时返回 `([(query, 秒)], 保留的合取项 id)`，否则返回 None；没有可去的项或预算 ≤0 时直接返回 None |
| `:1859-1866`（`_prove_equal`） | 在 unsat_core 和 case-tree 之前先试轻前提（预算取 min(budget, 2s, 剩余 deadline)）。成功时缓存键为"保留的合取项 id 集合"，可以传给拥有这些合取项的兄弟前提 |
| `:3031-3039`（`_retry_with_uf_unification`） | 在 opaque_array_uf 查询前，先对 opaque 后的整式试轻前提（预算为单查询预算）。成功时记为引理 `opaque_array_uf_light`；失败时按 deadline 重算预算，再走原来的 `opaque_array_uf` |
| `tests/unit/test_block_light_premise.py` | 7 条测试，见 §4 |

## 4. 健全性论证

1. **去掉合取项只会弱化公式。** 设 P = ∧ parts，L ⊆ parts，则 P ⊨ ∧L，所以 (∧L ∧ G) 为 UNSAT 时 (P ∧ G) 也为 UNSAT。这对任意子集都成立，与 `_heavy` 怎么选无关。因此 `_heavy` 只是一种"提议"：选错只会导致证不出，不会导致误证。
2. **只信 UNSAT。** `solve_query` 的结果不是 "unsat" 时返回 None，调用方继续走原路线，没有任何 sat 或 unknown 被当成证明，也不会产生新的 sat 答案。
3. **`_prove_equal` 里的 hide。** goal 用的是 `hide(differ)`，即 UF 应用被换成新常量，而 light 前提保留原样。把新常量 k 只换进 goal：原式的任何模型取 k := t 的值后，仍是新式的模型，所以新式只多出模型，UNSAT 能传回。这和原有 `_uf_app_constants` 的论证相同。
4. **缓存。** 缓存登记的是 (保留的 id 集合, 证明)，复用条件沿用原逻辑 `used <= conjuncts`：新前提包含这些合取项，就蕴含 ∧L，所以 ∧L ∧ (x≠y) 的 UNSAT 对新前提同样成立。测试 `test_prove_equal_light_proof_transfers_to_premises_with_other_heavy_conjuncts` 覆盖了这一点。
5. **`_retry_with_uf_unification`。** query 是 unify 之后（每次合并都有已证引理）、opaque 之后的公式，再交给 `_conjuncts` 拆分。整个 query 里任何一个合取项被去掉都只是弱化，论证同第 1 条。被去掉的即使是"否定目标"本身，也只是说明前提自身不可满足，仍然可靠。记录的引理 `opaque_array_uf_light` 带着实际被反驳的查询 sexpr，可以复查。
6. **binder 下的合取项保留**（例如内存目标、以 lambda 为参数的 sha3 应用）：这是为了效果，对健全性无影响。

单元测试（`tests/unit/test_block_light_premise.py`，全部按节点 ID 单独跑过，7 passed）：

- 命中：`test_light_premise_refutes_without_the_heavy_conjuncts`、`test_opaque_array_uf_light_after_unification`（记录 `opaque_array_uf_light`，不再走 `opaque_array_uf`）、`test_prove_equal_light_proof_transfers_...`
- 不命中：`test_light_premise_misses_when_nothing_is_dropped_or_the_proof_needs_a_heavy_conjunct`（无重项、证明依赖重项、预算 0 三种情况）、`test_light_premise_keeps_conjuncts_under_a_binder`
- 健全性：`test_opaque_array_uf_light_soundness_satisfiable_formula_is_not_refuted`（可满足式不被反驳），以及 `_prove_equal` 在只能靠乘积推出相等时返回 None
- 原有 `test_block_lambda_arrays.py::test_opaque_array_uf_query_right_after_unification` 仍然通过：没有重项时不命中，记录仍是 `opaque_array_uf`

## 5. 回归：reg_base.log 对比 reg_patched.log

22 条义务。答案有变化的有 4 条：

| 义务 | base | patched | 说明 |
|---|---|---|---|
| pair_48_16 | unknown 975.2s | **proved** 464.7s | 补丁新证出 |
| pair_53_14 | unknown 970.5s | **proved** 521.8s | 补丁新证出 |
| x86_maps_group_23 | unknown 241.8s | sat 233.1s | 预算挪动 |
| pair_group_30 | sat 225.0s | unknown 242.2s | 预算挪动 |

- **unsat → 其他：0 条。** 两次都 proved 的有 pair_62_12、pair_57_14、pair_52_16、pair_67_9、pair_47_17。其中 pair_52_16 从 164s 增加到 421s，pair_67_9 从 340s 增加到 523s：这是每次 `_prove_equal` 多了 0.2–0.5s 的轻前提探针（不命中时），累积起来变慢。
- **sat → unsat：0 条。**
- **两条 sat 和 unknown 互换的解释。** 补丁的两个入口只会返回 "unsat" 或 None，代码上不可能产生 sat，也不可能把 sat 改写成别的答案。`_check` 的 sat 来自对 F 或其等可满足变形的精确求解（quick exact、pin_split 的 sat 情形等），这些求解受 `_check` 按路线均分的节点 deadline 约束。补丁让 unify 路线多花或少花时间，改变了后面精确查询拿到的剩余预算，因此 pair_group_30 的 sat 查询这次没在预算内跑完（unknown，是更弱的答案，不影响健全性），x86_maps_group_23 反过来在预算内跑出了 sat。两条的耗时都在 225–242s 左右，正是 sat 查询一贯的耗时量级，与此解释一致。sat 本身表示存在反例模型，不是"证明"，这两条变化都不涉及误证。

## 6. 离线验证数据

工具：`cloud-inputs/tools/check_obligation.py`（生产 `_check`，单查询 30s，单义务 1800s）。修法前的代码 = 基于 HEAD（`a84f7d4`）的 git worktree；修法后的代码 = 本分支。云端 4 核上 4 路同时跑（base 和 fix 各 2 路），耗时受 CPU 争用影响，比服务器慢。

| 义务 | 修法前 | 修法后 |
|---|---|---|
| cap5377d30-local `pair_58_13_82bafc15a954` (a) | unknown 1402.7s | **proved 813.1s** (lemmas=7) |
| cap5377d30-local `pair_58_12_7495947f8f3d` (b) | proved 619.7s | proved 808.2s |
| cap5377d30-local `pair_68_9_bceb041a18a6` (a) | unknown 1434.4s | unknown 1570.3s（4 路并行）；单独重跑：SOLO_68_9 |
| r37c `smt2-a/pair_63_10_f768074e3e1a` (a) | unknown 1427.6s | **proved 795.4s** |
| r37c `smt2-b/pair_68_8_ade8b21d7787` (b) | unknown 1435.3s | **proved 1009.6s** |

（服务器参考数据：`f2_58_13_all.log` proved 574s，`f2_68_9_all.log` proved 833s，`pair58/f2_58_12_all.log` proved 546s。）

说明：

- `pair_58_12` 修法前离线也能证（620s）。服务器上它卡了约 2500s，是在整节点并行、预算被分摊的环境下发生的。修法后离线反而慢了约 190s，原因是单独跑时并没有走到需要轻前提的分支，探针成本白花了。这个数字受并行争用影响，以服务器全量结果为准。
- 修法同时对 r37c 留下的两个新卡点 `pair_63_10`（a）和 `pair_68_8`（b）有效：修法前离线都是 unknown，修法后都 proved。由此推断，r37c 加 pair58 修法后，5377 两个上下文都可能闭合，需要在服务器上做全量验证确认。

## 7. 测试结果

- `poetry run pytest tests/unit -q -m "not slow" -p no:cacheprovider -rf`：**1579 passed，2 skipped，10 deselected，35 failed**（1036s）。35 条失败全部是 `tests/unit/test_msize_absint.py`（已知例外，依赖被忽略的 `tmp/prov_common.py`）。为了看到全部失败，没有加 `-x`。
- `tests/unit/test_block_light_premise.py`：按节点 ID 单独跑，7 passed。

## 8. 未解决的问题

- `pair_68_9`：在云端 4 路并行下修法前后都是 unknown，单独重跑的结论见 §6 表格。服务器上它在 833s 内 proved，靠的是 unify 路线里的 `opaque_array_uf_light`。如果服务器全量跑时它仍然卡住，就是节点预算分摊问题（P1–P6 提速，即任务 B 的范围），不是本修法的问题。
- 成本：每次不命中的 `_prove_equal` 多 0.2–0.5s（一次化简加一次短求解）。回归里 pair_52_16、pair_67_9 明显变慢，但答案没变。如有需要，可以在前提中没有重项时跳过化简（现在已经是"无可去项直接返回"，开销主要来自 `_heavy` 的遍历和查询本身）。
- 补丁的轻前提没有对 light 合取项做 hide（与 unsat_core 路线不一致）。为了与服务器验证过的行为保持一致，这里没有改；两种写法都健全。
- 本地数据只覆盖上面 5 条义务和服务器回归的 22 条义务，两个上下文的全量节点验证需要在服务器上跑。
