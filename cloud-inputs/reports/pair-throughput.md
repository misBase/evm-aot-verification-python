# 任务 E 报告：pair 阶段吞吐（pair-throughput）

分支：`cloud/pair-throughput`（基于 `cloud/b3b-merged` = r37d：P1–P6 + 轻前提修法，3c87bd6）。

## 1. 结论

- **路由剖析**（16 条慢义务，r37d 原码，每条单独一个进程）：每条 pair 都被 goal split 成 7 个部分（`pair_85_6` 是 2 个）。7 部分里第 0、1、3、4、5 部分在开头的 quick0 就证出；**真正花时间的只有第 2 部分（内存/sha3 目标）和第 6 部分**：
  - 第 2 部分（2 部分形状下是第 0 部分）**16/16 由 `unify*`（normalize 之后的合一路由）证出**，但在它之前要先跑完 lia、quick*、blast*、alias*、potential*、bvabs*、bvabs、exact*、mul、mul*，这些路由**在 16 条里一次也没有成功过**，每条花费 357–617s（平均约 450s，占义务总时间的 55%）。
  - 第 6 部分 14/14 由 `quick*` 证出（normalize 之后的 3s 精确查询，0.0s），但在它前面的 lia 每次空跑 20–40s。
  - `pair_85_6` 的第 1 部分由 lia 证出（17s）。lia 在 34 次尝试中只赢了这 2 次。
- **轻前提探针不命中的开销**：16 条共 680 次 `_prove_equal` 轻前提探针，命中 16 次；不命中 664 次共 731s（每次约 1.1s）。其中实际求解只有约 0.2s（结果都是 sat），**约 0.7s 花在对约 195 个前提合取项逐个做 `_heavy`、`_no_binder` 遍历**，每个候选对都重做一遍。不命中之后，unsat_core 探针（664 次，878s）和 case tree（664 次，1280s）也全部失败。
- **实现了 3 项通用改进**（只改顺序、预算和缓存，不改变"哪个公式被证"）：
  1. **按义务类别把赢过的路由提前**（winner-first）：类别 = 名字去掉路径编号、保留 goal 部分（`pair_67_9_goal_2_of_7` → `pair_goal_2_of_7`）。赢过的路由按"每秒证出数"排在前面，其余路由保持原表顺序。LIA 改为路由表里的一项，参与排序。
  2. **`_prove_equal` 在 unsat_core 探针得到 SAT 时跳过 case tree**：case tree 反驳的正是同一个公式，公式可满足时它不可能成功。
  3. **`_heavy` / `_no_binder` 按项缓存**（`_memoized`，持有项引用）。
  
  另外顺手加固了一个健全性隐患：`_prove_equal` 的缓存原来只存 AST id，没有持有项；z3 会回收被释放项的 id，id 可能被别的项复用。现在缓存条目持有 x、y 和前提合取项。
- **离线 A/B**（模拟一个 pair worker：同一进程、同一 prover，按行顺序依次跑每个上下文的 8 条慢 pair，每条 3600s；4 个进程同时跑，base 和 new 负载相同）：**答案 16/16 一致，全部 proved**。总耗时 a：TBD → 2240s，b：TBD → 2192s。从第 3 条起，类别已有统计，每条 62–307s（base TBD）。

## 2. 路由剖析（任务第 1 步）

工具：`cloud-inputs/tools/route_trace.py`。它从 `_check` 的源码重新编译出一个副本，在各阶段之间插入计时标记，逻辑不变。同时统计轻前提探针、unsat_core 探针和 case tree 的命中/不命中耗时，并按所在路由归类。汇总用 `route_summary.py`。单独模式每条一个进程（`route_trace.py OUT.json FILE`），序列模式（`--sequence`）一个进程按顺序跑多条。

环境：云端 4 核，4 路并行，每条 3600s 期限（生产 43200s 节点预算下，pair 的剩余期限也远大于单条耗时；1800s 会把路由份额压得比生产小）。

### 2.1 每条义务的阶段（r37d 原码，单独模式）

| 义务 | 总耗时 | 难部分（第 2 部分）赢家 / 之前失败的阶段耗时 | 第 6 部分 |
|---|---|---|---|
| a pair_43_18 | 475.0s | unify* 75s / 357s | quick*，之前 38s |
| a pair_53_14 | 669.1s | unify* 160s / 464s | quick*，之前 39s |
| a pair_58_12 | 792.0s | unify* 280s / 463s | quick*，之前 44s |
| a pair_63_10 | 881.5s | unify* 384s / 440s | quick*，之前 52s |
| a pair_67_9 | 640.6s | unify* 186s / 406s | quick*，之前 43s |
| a pair_68_8 | 958.9s | unify* 430s / 472s | quick*，之前 51s |
| a pair_72_7 | 802.4s | unify* 291s / 454s | quick*，之前 51s |
| a pair_85_6（2 部分） | 1040.2s | 第 0 部分 unify* 516s / 500s | 第 1 部分 lia 17s |
| b pair_48_16 | 534.1s | unify* 123s / 377s | quick*，之前 29s |
| b pair_53_14 | 640.3s | unify* 158s / 432s | quick*，之前 45s |
| b pair_57_13 | 548.2s | unify* 102s / 407s | quick*，之前 34s |
| b pair_58_12 | 764.9s | unify* 234s / 480s | quick*，之前 46s |
| b pair_63_10 | 880.9s | unify* 350s / 475s | quick*，之前 50s |
| b pair_68_8 | 1024.2s | unify* 527s / 435s | quick*，之前 56s |
| b pair_72_7 | 850.2s | unify* 318s / 469s | quick*，之前 57s |
| b pair_85_6（2 部分） | 1218.4s | 第 0 部分 unify* 576s / 617s | 第 1 部分 lia 18s |
| **合计** | **12720.9s** | | |

### 2.2 各阶段合计（16 条）

| 阶段 | 尝试 | 成功 | 成功耗时 | **失败耗时** |
|---|---|---|---|---|
| potential* | 16 | 0 | 0 | **2669.1s** |
| blast* | 16 | 0 | 0 | **1553.0s** |
| exact* | 16 | 0 | 0 | 964.0s |
| lia | 32 | 2 | 34.6s | 953.8s |
| mul* / mul | 16 / 16 | 0 / 0 | 0 | 493.6s / 492.8s |
| normalize（normalize_word_arith） | 30 | – | – | 344.1s |
| bvabs / bvabs* | 16 / 16 | 0 / 0 | 0 | 183.4s / 65.9s |
| quick0（开头 3s 精确） | 118 | 70 | 1.5s | 162.6s |
| quick* | 30 | 14 | 0.0s | 52.5s |
| alias*、pin | 16、102 | 0、0 | 0 | 2.9s、4.7s |
| **unify*** | 16 | **16** | **4710.0s** | 0 |

所以每条 pair 里，最终胜出的 unify* 平均 294s，在它之前失败的路由平均约 450s。

### 2.3 `_prove_equal` 内的探针（16 条，按路由归类）

| 探针（所在路由） | 命中 | 不命中 | 命中耗时 | 不命中耗时 |
|---|---|---|---|---|
| 轻前提 @unify* | 9 | 469 | 12.3s | 446.3s |
| 轻前提 @blast* | 19 | 99 | 21.6s | 99.4s |
| 轻前提 @potential* | 0 | 99 | 0 | 95.3s |
| unsat_core @unify* / @blast* / @potential* | 0 / 0 / 0 | 469 / 99 / 99 | 0 | 543.2s / 126.0s / 114.0s |
| case tree @unify* / @blast* / @potential* | 2 / 0 / 0 | 467 / 99 / 99 | 21.2s | 1030.0s / 150.1s / 120.9s |
| 轻前提 @`_retry_with_uf_unification`（opaque 查询） | 9 | 0 | 109.8s | 0 |

（blast* 和 potential* 的 `_prove_equal` 来自 `_retry_over_potential` 里的 `unify_potential_arguments`。前 6 条义务是在给 trace 加路由归类之前启动的，它们的探针只计入不分路由的合计：轻前提命中 16 / 不命中 664 / 730.5s，unsat_core 0 / 664 / 877.7s，case tree 0 / 664 / 1280.0s。）

- **轻前提探针不命中的开销**：每次约 1.1s。对 a pair_67_9 第 2 部分的单独测量（`light_cost.py`，195 个无 binder 合取项）：`_heavy` 遍历 0.48s，`_no_binder` 遍历 0.25s，构造查询约 0s，求解 0.15s（sat）。也就是说，探针约 70% 的开销是对同一批合取项反复做遍历，每个候选对一次。命中只发生在 unify 路由里（每条 pair 1–3 次），恰好是证明需要的那几次，所以探针本身应保留，只需要降低它不命中时的成本。
- **unsat_core 探针**：在这些义务上从未命中。改动后（§4）统计它的求解结果：new 两个上下文 1023 次探针中 765 次是 **sat**，258 次是 unknown。
- **case tree**：在 unify* 里 469 次只成功 2 次。按 §3.2 的论证，这 2 次的 unsat_core 不可能是 sat（公式可满足时 case tree 不可能成功），只能是 unknown。

## 3. 设计与健全性（任务第 2 步，按收益排序）

总的保证不变：块定理只由 `BlockTheorem.complete` 按 manifest 判定；每条记录只有在某条原有路由对它（或它的等价/弱化形式）给出 UNSAT 时才是 proved。以下改动都不新增路由，也不改任何路由内部的接受规则。

### 3.1 winner-first 路由顺序（已实现，收益最大）

位置：`verification/block_equivalence.py`

| 行 | 内容 |
|---|---|
| `:1503` `_ROUTE_ORDER_STATIC` | 环境变量 `BLOCK_ROUTE_ORDER=static` 关闭排序（服务器 A/B 用） |
| `:1506` `_route_class(name)` | 去掉末尾的路径编号，保留 `_goal_k_of_n`：`pair_67_9_goal_2_of_7` → `pair_goal_2_of_7`，`x86_maps_3_5` → `x86_maps` |
| `:1516` `_winners_first(routes, stats)` | 赢过的路由按 wins / 累计秒数（含失败）降序放前面，其余保持原表顺序；没有赢过的路由不会因为失败被重新排序 |
| `:2622-2632` | 路由表开头加 `("lia", False)`（原来 LIA 在路由循环之前单独跑）；取本类统计，排序；`promoted` = 赢过的路由数 |
| `:2649-2651` | 份额：被提前的路由拿剩余时间的 1/2（与 alias 相同）；其余路由仍是"剩余时间 /（后面非 lia 路由数 + 1）"。lia 不设份额（原来也不设，只受自身上限约束） |
| `:2654` | `route == "lia"` → `self._retry_over_lia(target)` |
| `:2717-2718` | 每个实际跑过的路由记录 (wins, 秒数)；因为"无改写"而跳过的不计 |
| `:2494`、`:3352` | `_route_stats` 挂在 prover 上，`prove()` 每个节点清空。worker 的 prover 本来就是按节点建的（`_worker_prover`），所以统计范围是"一个节点内的一个 worker" |

**没有统计时与原代码逐项等价**：路由集合和顺序相同（lia 在最前，等于原来先跑 LIA）；份额的分母去掉 lia 后与原来完全相同（原来第 i 个路由是 `11 − i + 1`，现在第 i+1 项是"后面非 lia 路由数 11 − i，再 + 1"）。现有单元测试（包括固定路由顺序的 `test_unification_first_still_falls_back_to_mul_abstraction`）不受影响。

**健全性**：
- 每条路由本身、它对 F 做的变换、接受规则都没有改。排序只决定先试谁。循环仍然在第一个 UNSAT 处停止；所有路由都失败时，后面的 pending potential 恢复和直接查询也与原来一样。
- 被提前的路由如果失败，后面的路由仍然全部按原顺序尝试（测试 `test_promoted_route_failing_falls_back_to_every_other_route`）。
- 统计只是"提议"：类别分错、统计过时，最多是先跑了一个不合适的路由、浪费它的份额，不会产生证明。没有任何路由赢的时候，结果仍是 unknown（`test_nothing_refutes_nothing_is_proved`）。
- 份额只影响预算。被提前的路由拿 1/2，代价是失败时后面的路由只剩一半时间。这只可能让结果从 unsat 变成 unknown，不可能反过来。各路由内部也有自己的上限（unify：每条引理 1 个查询预算，case tree 4 个，直接查询 300s）。

**为什么按 goal 部分分类**：同一个节点的 terminal pair 共用一组 relation goals，第 k 部分形状相同（本数据：第 2 部分 16/16 由 unify* 证，第 6 部分 14/14 由 quick* 证）。如果不分部分，unify* 会被排到第 6 部分前面，而第 6 部分在 normalize 之后用 0.0s 的 quick* 就能证。

### 3.2 `_prove_equal`：unsat_core 为 SAT 时跳过 case tree（已实现）

位置：`:114`、`:130` `unsat_core` / `_unsat_core` 新增可选参数 `outcome`（dict），回填求解器的答案；`:1926-1931` `_prove_equal` 中，若 `outcome["answer"] == "sat"`，记录失败并返回 None。

**健全性**：
- unsat_core 求解的是 `∧ hide(c_i) ∧ hide(differ)`；case tree 反驳的是 `hide(premise) ∧ hide(differ)`。`hide` 是同一个替换，对合取逐项作用，所以两者是同一个公式（`_conjuncts` 只是把嵌套的 And 展开）。
- case tree 只在全部叶子 UNSAT 时返回证明，而各叶子合起来覆盖原式。公式 SAT 时它必然返回 None，所以跳过不会少证任何东西。
- 即使 z3 错误地给出 sat，后果也只是少一个证明（返回 None）。这个方向永远不会产生证明。
- 失败缓存与 case tree 失败时一样：用完整前提的 id 集合登记，只在"前提不比它强"时复用。
- unknown 时 case tree 照常跑（`test_unknown_core_probe_still_tries_the_case_tree`）。基线里 case tree 仅有的 2 次成功，unsat_core 必然都是 unknown，改动后照样会走到 case tree。
- 只在 `cache is not None` 时生效（只有这时才会跑 unsat_core 探针）。

### 3.3 `_heavy` / `_no_binder` 按项缓存（已实现）

位置：`:1733` `_no_binder`、`:1837` `_heavy`，经 `common.store_forwarding._memoized` 缓存（键是项的 id，值连同项本身一起保存，所以 id 不会被复用；超过 20 万条时清空）。原遍历函数改名为 `_no_binder_uncached`、`_heavy_uncached`。

**健全性**：两个都是项的纯函数，缓存只改变计算次数（`test_memoized_conjunct_tests_agree_with_the_walk`）。`_heavy` 只是轻前提的"提议"，即使答错也只影响去掉哪些合取项，去掉合取项只会弱化公式（pair58-fix 报告 §4.1）。

### 3.4 健全性加固：`_prove_equal` 缓存持有项（已实现）

位置：`:1886-1934`。缓存条目从 `(id 集合, proofs)` 改为 `(id 集合, proofs, (x, y, 合取项))`。

- 原来的缓存以 `(x.id, y.id)` 为键，以前提合取项的 id 集合为复用条件，但条目不持有这些项（`proofs` 里的查询是 `hide(c)` 或 `simplify` 之后的新项，不一定引用原项）。z3 的 `ast_manager` 会回收被释放 AST 的 id，所以在长期运行的 worker 里（一个 prover 服务整个节点、跨多条义务），一个已释放项的 id 原则上可能被新项复用，缓存的证明就可能被转用到一个不同的 (x, y, 前提) 上。这是"错误 UNSAT"方向，概率极低（键和全部前提 id 都要碰上），但不可接受。
- 持有引用之后，id 在缓存存在期间唯一对应原项。par12930 R2 和 `_memoized` 也是同样的处理方式。
- 测试：`test_cache_entries_keep_their_terms_alive`。

### 3.5 未实现的方向（按估计收益排序）

1. **normalize 的跨部分缓存**（每条 pair 约 25s）：同一条 pair 的第 2、6 部分共用前提 R，`normalize_word_arith` 对 R 的同一批改写候选各做一次 `_identity_proof`（每部分 5–21s）。可以按 (old, new) 缓存已证出的恒等式（持有项，par12930 R2 的做法），这是闭合恒等式，复用总是成立。
2. **quick0 按类别跳过**（每条 pair 约 7s）：难部分和第 6 部分的 quick0 一次也没成功。可以照 par12930 的做法，在同类连续失败 N 次后跳过，每 M 次重新探测一次。跳过等同于这次探测 unknown（goal split 照常进行）。收益小，没有做。
3. **unsat_core 探针的 unknown**（new 中每条 pair 约 30–75s）：258 次 unknown，每次用满 2s。可以用轻前提探针的 sat 模型先在完整前提上求值：如果它也满足完整的 hide(premise)，就已经是 sat，unsat_core 和 case tree 都可以跳过。这同样只会少做无用功。没有做，因为还要处理模型补全和数组/lambda 求值的细节。
4. **兄弟义务之间共享引理**：`_lemma_cache` 本来就在同一个 worker 的兄弟义务之间共享（证出的等式按 unsat core 复用）。不过本数据里 unify 的命中都是轻前提，而且每条 pair 的前提不同，跨兄弟命中很少。没有找到需要另做的通用机制。
5. **x86_maps**：r37d 前 1.75 小时里，a 的 310 条 x86_maps 共 7472s，与 pair 的 7628s 相当，但这次没有它们的 SMT2，无法离线剖析。winner-first 同样作用于 `x86_maps` 类别。par12930 的剖析显示 x86_maps 主要由 quick* 和 LIA 证出，建议在服务器上用 `BLOCK_ROUTE_ORDER=static` 做 A/B，确认 x86_maps 也受益。

## 4. 离线验证（任务第 3 步）

脚本：`route_trace.py --sequence OUT_DIR FILE...`。一个进程、一个 prover，按 `_check_rows` 的行顺序（j 升序）跑一个上下文的 8 条，名字改回 `pair_i_j`。这等价于一个 pair worker 在一个节点内依次处理这些 pair：路由统计、lemma cache、`_node_needed_unification` 都会延续。base = r37d（3c87bd6）的 worktree，new = 本分支（d485adc）的 worktree。4 个进程（base-a、base-b、new-a、new-b）同时跑，每条 3600s 期限。

| 上下文 | 义务 | base | new | 说明 |
|---|---|---|---|---|
| a | pair_85_6 | TBD | 711.3s | 首条，无统计；节省来自 §3.2/§3.3 |
| a | pair_72_7 | TBD | 533.7s | `pair_goal_2_of_7` 类首条（85_6 是 2 部分形状） |
| a | pair_68_8 | TBD | 307.4s | 起 unify* 直接排第一 |
| a | pair_67_9 | TBD | 116.2s | |
| a | pair_63_10 | TBD | 223.9s | |
| a | pair_58_12 | TBD | 168.0s | |
| a | pair_53_14 | TBD | 118.0s | |
| a | pair_43_18 | TBD | 62.0s | |
| **a 合计** | | **TBD** | **2240.5s** | |
| b | pair_85_6 | TBD | 755.7s | |
| b | pair_72_7 | TBD | 522.9s | |
| b | pair_68_8 | TBD | 270.5s | |
| b | pair_63_10 | TBD | 216.3s | |
| b | pair_58_12 | TBD | 159.5s | |
| b | pair_57_13 | TBD | 73.2s | |
| b | pair_53_14 | TBD | 113.6s | |
| b | pair_48_16 | TBD | 80.1s | |
| **b 合计** | | **TBD** | **2191.8s** | |

**答案**：new 16/16 proved，base TBD。没有 unsat 变成其他答案，也没有出现新的 sat。

new 中有统计之后的阶段（a pair_68_8 第 2 部分）：`quick0 3.5s → pin 0.3s → normalize 15.7s → unify* 264.5s`。第 6 部分：`quick0 3.2s → pin 0.2s → normalize 14.4s → quick* 0.0s`。lia、blast*、potential*、exact*、mul 都不再在前面空跑。

new 两个上下文合计，unsat_core 探针 1023 次：sat 765 次（这些 case tree 被跳过），unknown 258 次。轻前提不命中 1005 次共 232s（每次约 0.23s，base 约 1.1s）。

## 5. 测试结果

- 全量快测：`PYTHONPATH=. poetry run pytest tests/unit -q -m "not slow" -p no:cacheprovider -n 2 -rf`（与 A/B 的 base 进程同时跑，未加 `-x`，否则会停在第一个已知失败上）：**1609 passed、2 skipped、35 failed，747s**。35 条失败**全部**是已知例外 `tests/unit/test_msize_absint.py::*`（依赖被忽略的 `tmp/prov_common.py`），除此之外没有失败。
- `test_block_uf_unification.py::test_offset_view_step_lemma_proves_the_rewrite_without_per_read_queries` 在开发中、机器上同时有 5 个求解进程时失败过一次（`assert unknown == unsat`，测试内部 3s 超时，b3b-port 报告里也记录过同一现象）；全量快测和按节点 ID 重跑都通过。
- 新测试按节点 ID 逐个跑过（`-v`），14 个全部被收集到，全部 passed，没有同名覆盖：
  - `tests/unit/test_block_route_order.py`（8 个）：类别划分；没有统计时顺序不变；按每秒证出数排序；赢家对同类兄弟提前、对别的类别不提前；`BLOCK_ROUTE_ORDER=static` 保持原表；被提前的路由失败后其余路由按原序全部尝试；没有路由成功时仍是 unknown；被提前的路由拿 1/2 剩余时间。
  - `tests/unit/test_block_prove_equal_sat.py`（6 个）：core 为 sat 时跳过 case tree 并登记失败；没有缓存时 case tree 照常跑；core unknown 时 case tree 照常跑并能证出；被蕴含的等式仍然证出；缓存条目持有项；`_heavy`、`_no_binder` 的缓存版本与遍历版本一致。
- 变异测试：把 `if outcome.get("answer") == "sat":` 改成 `if False:`，`test_satisfiable_difference_skips_the_case_tree` 失败。用 `BLOCK_ROUTE_ORDER=static` 关闭排序后，`test_route_that_refuted_a_class_goes_first_for_its_siblings`、`test_promoted_route_failing_falls_back_to_every_other_route`、`test_promoted_route_gets_half_of_what_is_left` 这 3 个失败，其余 5 个照常通过（它们本来就不依赖排序）。
- 现有测试的两处适配（只改桩，不改断言）：`test_block_uf_unification.py:77` 的 `unsat_core` 桩加上可选参数 `outcome=None`；`test_block_light_premise.py:62` 按三元组解包缓存条目。

## 6. 未解决的问题

1. **首条的学习成本**：每个 worker 的每个类别，第一条义务仍走原表顺序。本数据里 2 部分形状（`pair_85_6`）和 7 部分形状各学一次。生产中一个节点约 170 条 pair、4 个 worker，每个 worker 每个类别只付一次，摊薄后可以忽略。也可以按节点在父进程里汇总统计、发给 worker，但需要改 `_check_serialized` 的协议，这次没有做。
2. **被提前的路由拿 1/2 剩余时间**：在节点快到期的时候，如果被提前的路由失败，后面的路由时间会减半。本数据里 unify* 最多用了 576s，在 43200s 节点预算下不构成问题。如果出现"提前路由失败后其他路由预算不足"的情况，可以改回等份。
3. **x86_maps 没有离线数据**，见 §3.5 第 5 条。
4. **离线是 4 进程并行**，耗时受 CPU 争用影响，绝对值比服务器慢。base 和 new 同时跑、负载相同，相对比较有效。
5. 未做的方向见 §3.5。

## 附：工具

- `cloud-inputs/tools/route_trace.py`：路由剖析（单独模式 / `--sequence` 模式）。
- `cloud-inputs/tools/route_summary.py`：汇总 trace JSON，可加 `--per-obligation` 打印每条义务的明细。
