# 任务 F：合并批次 3B 候选（b3b-final）

分支：`cloud/b3b-final`，基于 `cloud/b3b-merged`（7f94f0b）。依次合并 `origin/cloud/review-3b`（48cf910）、`origin/cloud/test-hygiene`（4fee802）、`origin/cloud/pair-throughput`（525f670），之后加一个提交（收尾修复和测试）和本报告。

| 提交 | 内容 |
|---|---|
| `2ecf0ab` | merge cloud/review-3b（无冲突） |
| `6b86b26` | merge cloud/test-hygiene（无冲突） |
| `81d767b` | merge cloud/pair-throughput（`_prove_equal` 冲突，见 §1） |
| `aab1c19` | correspondence 墙钟 = 预算；合并后缓存的新测试；轻前提预算的守护测试 |
| 本提交 | 报告 |

## 结论

- 三个分支都已合并。唯一的文本冲突在 `verification/block_equivalence.py` 的 `_prove_equal`：review-3b 和 pair-throughput 都修了"缓存 id 回收"问题，但条目格式不同。合并后只保留一套实现（§1），满足任务的三条要求，两边的测试都保留并通过。
- 按 id 做的缓存已逐个核对（§2）：`_memoized`（含新增的 `_heavy`、`_no_binder`）持有参数项；`_lemma_cache` 只由 `_prove_equal` 写入；没有发现别的问题。
- review-3b 的两条"建议修"，pair-throughput 都没有处理：
  - **correspondence 墙钟上限**：已按建议修复，墙钟与原来的 timeout（= 预算）对齐（§3.1），附测试。
  - **`_retry_with_uf_unification` 轻前提查询改用 `_LIGHT_MS`**：**没有照做**。pair-throughput 的路由剖析数据显示，在 5377 的 16 条慢 pair 上（base 和 new 两次序列运行，共 32 次），这条查询**每次都命中**，而且正是证出内存目标的那一步，耗时 3.2–20.0s；从未出现过不命中。改成 2s 上限会让这 32 次全部变成不命中，回退到带 gas 的 `opaque_array_uf`（pair58-fix 报告实测 60s 以上，超过 30s 单查询预算）。这会让 pair58-fix 修好的义务重新卡住。审查报告原文也写了"或者设一个单独的上限"；但任何低于 20s 的上限都会切掉实测的命中，而现在的上限（单查询预算 30s）只比它高 1.5 倍，所以保持不变。我加了一条守护测试，防止以后有人按字面"修"掉它（§3.2）。**需要你确认是否接受这个偏离。**
- 全量快测：**见 §5**。block 相关集成测试：**见 §5**。

## 1. 合并冲突及处理：`_prove_equal` 缓存

### 两边的写法

| | review-3b（883b97a） | pair-throughput（5fe1787） |
|---|---|---|
| 条目 | `(id 集合, proofs, alive)` | `(id 集合, proofs, keep)` |
| alive/keep | 成功条目扁平持有 `(x, y, *id 集合里的合取项)`；失败条目 `()` | 所有条目（成功和失败）都持有 `(x, y, tuple(全部合取项))` |
| core 探针 SAT 时跳过 case tree | 无 | 有，写入失败条目，持有 `keep` |

两种写法都健全。区别在于：pair-throughput 让失败条目也持有项；成功条目持有的是全部合取项，不只是用到的那些。条目格式不同（扁平和嵌套），双方的测试都按自己的格式解包。

### 保留的实现（`verification/block_equivalence.py:1886-1941`）

以 review-3b 的扁平格式为准，并入 pair-throughput 的 `outcome` 和"SAT 跳过"：

| 写入点 | 行 | 第三字段 |
|---|---|---|
| 轻前提成功 | `:1919` | `(x, y, *kept)`，kept = parts 中 id ∈ `proofs[1]` 的合取项 |
| unsat_core 成功 | `:1929` | `(x, y, *used)` |
| core 探针 SAT（pair-throughput 新增）：失败条目 | `:1936` | `()` |
| case tree 成功 / 失败 | `:1940` | 成功 `(x, y, *parts)`，失败 `()` |

对照任务要求：

1. **所有成功条目都持有键里的 x、y，以及 id 集合中的全部合取项**：
   - 轻前提条目的 id 集合是 `proofs[1]`，即 `_refute_over_light_premise` 保留下来的合取项的 id。这些合取项都取自 `parts`，所以 `kept` 恰好覆盖了这个集合；
   - unsat_core 条目的 id 集合就是 `used` 的 id；
   - case tree 条目的 id 集合是 `conjuncts`，也就是 `parts` 的 id。
2. **失败条目可以不持有任何项**：失败条目只在 `conjuncts ⊆ used` 时返回 None。即使 id 被回收、误命中，也只是少证一条（miss），不影响健全性。
3. **"core 探针 SAT 时跳过 case tree"写入的条目**：这是一个失败条目（`proofs is None`），以完整前提的 id 集合登记，与 case tree 失败的条目相同，按第 2 条不需要持有项。

健全性论证沿用 review-3b §1：成功条目存活期间，x、y 和 id 集合里的全部合取项都存活，所以键和集合里的 id 不会被分配给别的项。因此 `used ⊆ conjuncts(P′)` 在语义上就意味着 P′ 包含了当时用到的全部合取项，于是 P′ ⊨ ∧used，而 ∧used ∧ x≠y 已经被反驳。

"SAT 跳过"本身（pair-throughput 的论证）：`hide(premise) ∧ hide(differ)` 有模型，而 case tree 反驳的正是这个公式，所以 case tree 不可能成功。跳过它只省时间，不会产生证明。

### 测试适配

- `tests/unit/test_block_prove_equal_sat.py:60-70`（`test_cache_entries_keep_their_terms_alive`）：原来按嵌套格式取 `keep[2]`，现在按扁平格式取 `keep[2:]`。同时把断言加强为"`proofs` 非 None，且 `used ⊆ keep[2:]` 的 id"（原断言 `all(t.get_id() …)` 恒为真）。这是唯一的测试改动。
- `tests/unit/test_block_light_premise.py:62`：两边都改成了三元组解包，内容相同，自动合并。
- `tests/unit/test_block_uf_unification.py`：test-hygiene 的 `answer_rlimit` 改动和 pair-throughput 的 `unsat_core` 桩（`outcome=None`）是不同的行，自动合并。
- review-3b 的 `test_prove_equal_cache_entries_keep_their_ids_alive[cases]` 用 `lambda *args: None` 作为 `unsat_core` 的桩，能接收新增的 `outcome` 参数；桩不写 `answer`，所以 case tree 照常运行。

## 2. 按 id 的缓存核对

| 缓存 | 位置 | 是否持有项 |
|---|---|---|
| `_memoized`（`_MEMO`） | `common/store_forwarding.py:78-87` | 值存为 `(args, value)`，持有参数项，与 `_put` 的做法相同。超过 20 万条时整体清空，键和项一起丢掉，不会留下悬空 id |
| `_no_binder` / `_heavy`（pair-throughput 新增） | `block_equivalence.py:1733-1737`、`:1837-1842` | 经 `_memoized`，持有 term。两者都是项的纯函数，返回 bool |
| `ov_unshift`、`base_offset`、`linearize`、`subtract`、`unshift` | `block_equivalence.py:611`、`:1107`；`store_forwarding.py` | 都经 `_memoized`，持有参数 |
| `_lemma_cache` | `BlockEquivalenceProver.__init__` `:2498` | 只由 `_prove_equal` 写入（经 `unify_across` `:1716`、`unify_potential_arguments` `:1086`、`sweep_equalities` `:2067`）。`_prove_equal_lia` 虽然接收 `cache` 参数，但不读也不写。按 §1 处理 |
| `_route_stats`（pair-throughput 新增） | `:2500`、`:3360` | 键是义务类别名和 `(route, norm)`，不涉及 AST id |
| `PrefixSolver.stack` | `x86_64/cfg_state.py:55-104` | `stack` 持有已断言的项（review-3b 已核对） |
| `_forward_apart` 等函数内的 `cache`/`seen` | 各遍历函数 | 局部变量，只在一次遍历内使用，被遍历的根项在此期间存活 |
| `div_proof` / `memgas_proof` 的 `_SUCCESS` / `_FAILURE` | `x86_64/summaries/*.py` | 键是 `semantic_key(...)`（结构键），不是 id；本批没有改动 |

结论：本批引入或改动的、按 id 的缓存都持有项。review-3b §5.3 提到的 `state_digest` 的 `expression_cache` 不在本批 diff 内，没有再审。

## 3. review-3b 的两条建议

### 3.1 correspondence 的墙钟上限（已修）

- **问题**：P1 之前，每一行用一个新 solver，`timeout = budget`（`min(_QUICK_EXACT_MS, timeout_ms, 剩余 deadline)`）。P1 改走 `PrefixSolver` → `_bounded_check` 之后，墙钟上限变成了 `budget × REACHABILITY_WALL_SAFETY_FACTOR`（10 倍）。在临近节点 deadline 时，一行最多可能多跑约 9×budget。
- **修复**：
  - `x86_64/cfg_state.py:35-44`：`_bounded_check(solver, timeout_ms, tag, wall_ms=None)`。传入 `wall_ms` 时，墙钟上限等于 `max(wall_ms, 1)`；`max` 是为了不向 Z3 传 0（0 表示不限时）。不传时行为不变。rlimit 不变。
  - `x86_64/cfg_state.py:84`、`:103`：`PrefixSolver.check(..., wall_ms=None)`，原样传给 `_bounded_check`。
  - `verification/block_equivalence.py:2966-2968`：correspondence 按位置参数传入 `wall_ms=budget`。用位置参数，是为了兼容现有测试里 `lambda self, conjuncts, *a` 形式的桩。
- **健全性**：这里只改时间上限。correspondence 的结果只是映射"提议"，unknown 会进入 `propose_from_siblings`、`_empty_by_bvabs` 或 "all"，不会产生证明（review-3b §2 P4）。可达性检查（`is_possible`）不传 `wall_ms`，行为不变。
- **对 5377 的影响**：服务器 r37c 的 stage 日志显示，两个上下文的 171 行中，170 行由执行器 witness 直接映射，只有 1 行走 `prefix.check`（判为 empty），整个 `_correspondence` 阶段只用 21–24s。所以这项修改对 5377 基本没有影响。对其他块，最坏情况是原来 3–30s 才判出的行变成 unknown，与 P1 之前的行为一致。
- **测试**：
  - `test_bounded_check_wall_clock_defaults_to_the_safety_net_and_can_be_set`：记录 solver 的 `set` 调用；默认是 10 倍，传入 `wall_ms` 时等于 `wall_ms`，rlimit 两种情况相同。
  - `test_correspondence_rows_get_their_budget_as_wall_clock`：在 `_correspondence` 里，每个 `"correspondence"` 行的 `wall_ms == budget`，且 `0 < budget ≤ _QUICK_EXACT_MS`，映射结果与 `test_block_correspondence` 相同。
  - 变异：把调用处的 `budget` 参数去掉，后一条测试失败。

### 3.2 `_retry_with_uf_unification` 的轻前提预算（未改，附数据和守护测试）

- **位置**：`verification/block_equivalence.py:3172-3178`。预算 = `min(timeout_ms, 剩余 deadline)`，即单查询预算（生产 30s）。
- **数据**：来自 pair-throughput 提交的 `cloud-inputs/pair-throughput/seq-{base,new}-{a,b}/*.json`，字段 `probes["light<_retry_with_uf_unification@unify*"]`：

  | 运行 | 命中 / 不命中 | 命中耗时范围 |
  |---|---|---|
  | seq-base-a（8 条） | 8 / 0 | 5.7–20.0s |
  | seq-base-b（8 条） | 8 / 0 | 3.9–17.4s |
  | seq-new-a（8 条） | 8 / 0 | 4.9–13.9s |
  | seq-new-b（8 条） | 8 / 0 | 3.2–18.8s |

  另外，pair58-fix 的 `cloud-inputs/pair58/unify_68_9_f2.log:182` 记录 `_refute_over_light_premise 6.0s -> tuple`（pair_68_9 证出的那一步）。
- **为什么不照做**：`_LIGHT_MS = 2000`。按字面改成 2s 上限后，上面 32 次命中全部会超时。之后的路径是带 gas 和的 `opaque_array_uf`：pair58-fix 实测 60s 以上，超过 30s 预算，于是 unknown。然后是 sweep 和 case tree，这正是 pair58-fix 之前卡住的路径。审查担心的是不命中时的开销（最多一个单查询预算），但在这批数据里没有出现过不命中。另外，这条查询每条义务最多跑一次（只在 `lemmas and opaque` 时），不像 `_prove_equal` 的探针那样按候选对跑上百次。
- **守护测试**：`test_uf_unification_light_query_keeps_the_per_query_budget`。用 `test_opaque_array_uf_light_after_unification` 的形状，断言轻前提查询拿到的预算 > `_LIGHT_MS` 且 ≤ `timeout_ms`，结果是 `opaque_array_uf_light`。如果以后要设上限，必须先用服务器数据说明命中耗时，再修改这条测试。
- **如果仍然要求按字面修**：只需把 `:3176` 的 `budget` 改成 `min(budget, _LIGHT_MS)`。我判断这会让 5377 的 16 条慢 pair 回到 unknown，所以没有提交。

## 4. 最终改动清单（相对 `cloud/b3b-merged`，不含 cloud-inputs/）

| 文件:行 | 来源 | 内容 |
|---|---|---|
| `verification/block_equivalence.py:114-145` | pair-throughput | `unsat_core` / `_unsat_core` 的可选 `outcome` 参数，回传 sat/unsat/unknown |
| `verification/block_equivalence.py:1501-1527` | pair-throughput | `_ROUTE_ORDER_STATIC`、`_route_class`、`_winners_first` |
| `verification/block_equivalence.py:1733-1747`、`:1837-1850` | pair-throughput | `_no_binder` / `_heavy` 经 `_memoized` 缓存（原遍历改名为 `*_uncached`） |
| `verification/block_equivalence.py:1886-1941` | review-3b + pair-throughput + 合并 | `_prove_equal`：缓存条目三元组、持有规则（§1）、core 探针 SAT 时跳过 case tree |
| `verification/block_equivalence.py:2500`、`:3360` | pair-throughput | `_route_stats` 初始化，每个节点重置 |
| `verification/block_equivalence.py:2626-2724` | pair-throughput | LIA 作为一条路由；winner-first 排序；被提前的路由分到剩余的一半；路由统计 |
| `verification/block_equivalence.py:2966-2968` | 本任务 | correspondence 的 `prefix.check` 传入 `wall_ms=budget` |
| `x86_64/cfg_state.py:35-44`、`:84`、`:103` | 本任务 | `_bounded_check` / `PrefixSolver.check` 的可选 `wall_ms` |
| `tools/call_provenance.py`、`tools/msize_absint.py` | test-hygiene | msize_absint 改用 call_provenance 的 CFG，去掉对 `tmp/prov_common.py` 的依赖 |
| `tests/unit/test_block_uf_unification.py` | test-hygiene + pair-throughput | `answer_rlimit`（rlimit 2 亿）用于 step-lemma、telescope、div-quotient 检查；`unsat_core` 桩加上 `outcome=None` |
| `tests/unit/test_block_lemma_cache_ids.py` | review-3b | 6 条：id 回收复现和条目持有的不变式 |
| `tests/unit/test_block_review_3b.py` | review-3b | 6 条：P1–P6 和轻前提的随机化审查 |
| `tests/unit/test_block_prove_equal_sat.py` | pair-throughput（:66-70 由合并适配） | 6 条：SAT 跳过、缓存持有、memo 一致 |
| `tests/unit/test_block_route_order.py` | pair-throughput | 8 条：路由排序 |
| `tests/unit/test_block_light_premise.py:62` | review-3b = pair-throughput | 三元组解包 |
| `tests/unit/test_block_b3b_final.py` | 本任务 | 5 条，见下 |

`tests/unit/test_block_b3b_final.py` 的 5 条测试：

1. `test_every_prove_equal_route_writes_entries_that_keep_their_ids_alive`：同一个缓存里依次写入轻前提成功、unsat_core 成功、core SAT 跳过、case tree 成功、case tree 失败五种条目。释放全部项并 gc 之后，断言 3 个成功条目都持有键和 id 集合，2 个失败条目都是 `()`。
2. `test_core_sat_skip_entry_answers_weaker_premises_only`：SAT 跳过写入的失败条目不会挡住更强的前提。
3. `test_bounded_check_wall_clock_defaults_to_the_safety_net_and_can_be_set`：见 §3.1。
4. `test_correspondence_rows_get_their_budget_as_wall_clock`：见 §3.1。
5. `test_uf_unification_light_query_keeps_the_per_query_budget`：见 §3.2。

变异测试：
- 把轻前提条目的 alive 改成 `()`，第 1 条和 `test_prove_equal_cache_entries_keep_their_ids_alive[light]` 失败。
- 去掉 correspondence 的 `wall_ms`，第 4 条失败。
- 注：同样把轻前提条目改成 `()` 时，review-3b 的 id 回收复现用例 `test_prove_equal_cache_survives_id_recycling[light]` 在合并后的代码上**没有**失败。这个复现依赖 Z3 按 LIFO 回收 id。我推测原因是 pair-throughput 的 `_memoized(_heavy/_no_binder)` 持有了合取项，改变了回收顺序，但没有逐一核实。所以对"条目持有项"的回归检查，要依靠不变式测试（review-3b 的 `…keep_their_ids_alive` 和上面第 1 条），不能依靠复现用例。

## 5. 测试结果

（待填）

## 6. 离线验证数据

- 本任务没有重跑 5377 的义务（需要服务器全量运行）。合并后的代码在 pair-throughput A/B 的基础上只多了以下两点：
  - `_prove_equal` 的失败条目不再持有项：只影响内存，命中条件不变；
  - correspondence 的墙钟上限：5377 上只有 1 行经过 `prefix.check`。
  
  因此预计 5377 的结果与 pair-throughput 的 A/B（16/16 proved）一致，但需要服务器确认。
- §3.2 用到的数据来自 pair-throughput 已提交的 trace JSON，本任务没有重新测量。

## 7. 未解决的问题

1. **需要确认**：§3.2 没有按字面执行"轻前提查询改用 `_LIGHT_MS`"。
2. **需要服务器验证**：r37d + review-3b + test-hygiene + pair-throughput + 本任务，跑 5377 a、b 两个上下文的全量结果，以及原来已证块的回归。
3. review-3b 的 id 回收复现用例在合并后的代码上不再敏感（§4 末尾），不变式测试仍然有效。
4. test-hygiene 报告提到的两条 slow 测试依赖未提交的 `tests/data/block_obligations/*.smt2`，不在快测范围内，本任务没有处理。
