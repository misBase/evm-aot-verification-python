# 任务 H 报告：诊断模式下出错后继续跑（keep-going）

分支：`cloud/keep-going`（基于 `cloud/b3b-final`，4d56743）。

## 1. 结论

- 给 `BlockEquivalenceProver` 增加了构造参数 `keep_going`（默认 `False`），给诊断工具 `tools/probe_block_obligations.py` 增加了开关 `--keep-going`，也可以用环境变量 `BLOCK_KEEP_GOING=1` 打开。
- 打开后，pair 阶段（`_check_rows` 的第一轮和第二轮）遇到不在 `tolerated` 里的失败义务时，不再立即抛出 `ValueError: outcome mismatch …`，而是把这条失败（名字、答案、耗时、位置）记到 `_kept_failures`，然后继续证明其余的项和行。pair 阶段结束后，只要记录过失败，`prove()` 就抛出一个汇总的 `outcome mismatch (N pair obligations, keep-going): …`。所以节点只会是 inconclusive，**不可能被报告为 proved**。
- 输出 JSON 的每个节点新增字段 `keep_going_failures`，列出**全部**被记录的失败义务：`name`、`answer`、`seconds`、`where`。原有的 `failed_obligations` 也会包含这些义务（它来自 `result.obligations`）。
- 开关默认关闭。生产路径（`tools/verify_block_lockstep.py`、`verification/block_parallel.py`、`verification/block_program.py`）不传这个参数，代码里也不出现 `keep_going` / `KEEP_GOING`，有测试锁定这一点。开关关闭时，`_check_rows` 走的是原来的 `raise` 分支，消息格式和原来一字不差，第一条失败之后的义务一条都不会被尝试。
- 新增 12 条单元测试，全部通过。全量快测结果见 §4。

## 2. 用法

```bash
# Safe 5377 depth=30 上下文 a（stack_constants ((14,3575))，memory_size/fmp 符号）
cat nodes-5377a.json
# [{"pc": 5377, "stack_depth": 30, "memory_size": null, "free_memory_pointer": null,
#   "stack_constants": [[14, 3575]]}]

PYTHONPATH=. BLOCK_PAIR_WORKERS=3 poetry run python tools/probe_block_obligations.py \
    <SAFE_STEM> nodes-5377a.json --output /tmp/probe-5377a.json \
    --timeout-ms 30000 --node-seconds 43200 --keep-going --formula-dir /tmp/probe-5377a-smt

# 等价写法：用环境变量打开
PYTHONPATH=. BLOCK_KEEP_GOING=1 poetry run python tools/probe_block_obligations.py \
    <SAFE_STEM> nodes-5377a.json --output /tmp/probe-5377a.json --timeout-ms 30000 --node-seconds 43200
```

`<SAFE_STEM>` 是 Safe 合约 `.json`/`.hex` 的公共前缀（不带扩展名）。

输出（每个节点）里新增的字段（格式示意，数值不是实测）：

```json
"keep_going_failures": [
  {"name": "pair_<i>_<j>", "answer": "unknown|sat", "seconds": <float>, "where": "<evm kind@loc> / <x86 kind@loc>"},
  ...
]
```

`configuration.keep_going` 记录了本次运行是否打开了开关。`--formula-dir` 照常把每条失败义务的公式写到磁盘，可以和 `cloud-inputs/tools/check_obligation.py` 配合做离线复现。

注意事项：

- 继续跑仍然受节点预算 `--node-seconds` 约束。第 58 行之后还有 112 行，每条卡住的义务可能耗时约 2500s，所以要给足预算（上例用 43200s）。预算耗尽时会抛 `ProofBudgetExceeded`，节点中止。**此前已经记录的失败仍然会出现在 `keep_going_failures` 里**（`prove()` 在 `finally` 之后填写 `result.kept_failures`）。
- 只有 pair 阶段会继续跑。前面的 `entry_nonempty`、`havoc_relation`、`model_domain_nonempty`、`check_paths`（覆盖、假设）失败时，仍然立即终止。这些失败意味着后续义务无从定义（比如前提为空），继续跑没有意义。
- 第一轮里被提议（`propose_from_siblings`）的行失败时，按原来的逻辑降级为 "all" 或 empty，进入第二轮，**这不算 keep-going 失败**。只有降级后的第二轮义务仍然失败，才会被记录。

## 3. 改动位置与健全性论证

### 3.1 改动

| 位置 | 内容 |
|---|---|
| `verification/block_equivalence.py:2453-2454` | `BlockProofResult.kept_failures: tuple = ()` |
| `verification/block_equivalence.py:2485` | `BlockEquivalenceProver.__init__(…, keep_going=False)` |
| `verification/block_equivalence.py:2506-2510` | 保存 `self.keep_going`，初始化 `self._kept_failures = []` |
| `verification/block_equivalence.py:3305-3309` | `_check_rows` 文档说明 |
| `verification/block_equivalence.py:3350-3357` | 失败分支：关闭时照原样 `raise`；打开时记录失败并 `continue` |
| `verification/block_equivalence.py:3374` | `prove()` 开始时清空 `_kept_failures`（同一个 prover 连续跑多个节点，记录不会串到下一个节点） |
| `verification/block_equivalence.py:3448-3452` | `_pair_phase` 返回后，只要有记录的失败就抛 `ValueError`，此时还没有构造 `BlockTheorem` |
| `verification/block_equivalence.py:3469` | `result.kept_failures = tuple(self._kept_failures)`，放在 `try/finally` 之后，中途中止也会填写 |
| `tools/probe_block_obligations.py:5,15-19` | 文档 |
| `tools/probe_block_obligations.py:69,89` | `build_prover(…, keep_going=False)` 把参数传给 prover |
| `tools/probe_block_obligations.py:112-114` | 节点 JSON 输出 `keep_going_failures` |
| `tools/probe_block_obligations.py:129-131,152` | `--keep-going`，默认值读 `BLOCK_KEEP_GOING`（空串或 `0` 表示关闭） |
| `tests/unit/test_block_keep_going.py` | 新测试（12 条） |

### 3.2 健全性

1. **keep-going 下节点不可能 proved**，有两道独立的保证：
   - (a) `prove()` 在 `_pair_phase` 之后检查 `_kept_failures`，非空就抛 `ValueError`。这发生在构造 `BlockTheorem`、`_issued_theorems.append`、`result.status = "proved"` 之前，异常被 `prove()` 的 `except` 捕获后变成 `reasons`，`status` 保持默认的 `"inconclusive"`，`_issuer` 也不会被设置。而 `BlockProofResult.proved` 要求 `status == "proved"`、`_issuer` 非空、定理已签发，三条都不满足。
   - (b) 即使去掉 (a)，失败义务的记录（answer 是 sat 或 unknown，或者引理没证出）仍然留在 `records` 里，并按清单顺序进入定理。`BlockTheorem.complete` 要求 `all(o.proved for o in self.obligations)`，所以不会成立。`_pair_phase` 末尾的 `by_name` 合并只会让**已证出的** `ready` 记录覆盖同名记录，而 `_check_rows` 会跳过 `ready` 里已有的名字，所以一条失败记录不可能被同名的已证记录顶掉。
   - 测试 `test_pair_phase_keep_going_collects_failures_of_both_rounds` 直接检查 (b)：用 keep-going 跑完 `_pair_phase` 后，`theorem.complete` 为假。
2. **没有改变"什么算证出"**：每条义务仍然由同一个 `_check` 判定，记录内容也一样。keep-going 只决定"失败之后是否继续尝试别的义务"，不影响任何一条义务的答案。唯一可能的副作用是，继续跑的义务会更新 `_route_stats` / `_lemma_cache`。这两样本来就由同一节点的所有义务共享，每次查询各自独立，缓存的是已证等式，和原来 tolerated 行失败后继续跑的情形一样。
3. **生产路径不变**：`keep_going` 默认为 `False`，生产调用点都不传它（有测试检查源码）。`keep_going=False` 时，`_check_rows` 失败分支执行的语句和原来完全一样（同一个 `raise`、同一条消息），`prove()` 新加的检查也因为 `_kept_failures` 恒为空而不生效。`portable_identity` 没有包含 `keep_going`。这是有意的：这个开关不改变任何被签发的定理，而且生产调度器比较的身份也保持不变。
4. 兄弟提议（`tolerated`）的降级逻辑没有改动：第一轮 tolerated 行失败仍然进入 `failed`，第二轮按原样检查完整行。

## 4. 测试结果

命令：`PYTHONPATH=. poetry run pytest tests/unit -q -m "not slow" -p no:cacheprovider`（云端 4 核，未加 `-x`，以便看到全部失败）。

| 运行 | 结果 | 耗时 |
|---|---|---|
| 改动前（`cloud/b3b-final` 4d56743） | **1661 passed、2 skipped、10 deselected、0 failed** | 1140s |
| 改动后（`cloud/keep-going`） | **1673 passed、2 skipped、10 deselected、0 failed** | 1123s |

多出的 12 条就是新测试。msize_absint 相关测试全部通过，没有已知例外。

新测试按节点 ID 用 `-v` 逐条单独跑过：12 条都被收集到，都通过，没有同名覆盖。

| 测试 | 验证内容 |
|---|---|
| `test_keep_going_reports_both_failures_and_the_node_is_not_proved` | 真实 prover（muti_block pc=120）：`pair_0_0`、`pair_1_1` 失败，打开开关后 4 条 pair 全部被尝试，两条都在 `kept_failures`/`reasons` 里，`proved` 为假，`theorem` 为 None |
| `test_default_stops_at_the_first_failure` | 同一场景、开关关闭：只尝试到 `pair_0_0`，之后的 pair 一条都没有被尝试，消息格式和原来一样 |
| `test_kept_failures_survive_a_later_budget_abort` | 记录一条失败之后再遇到 `ProofBudgetExceeded`：节点中止，已记录的失败仍然输出 |
| `test_keep_going_without_failures_still_proves` | 没有失败时，打开开关也照常 proved |
| `test_pair_phase_keep_going_collects_failures_of_both_rounds` | `_pair_phase`：第一轮非提议行的失败和第二轮降级行的失败都被记录，`theorem.complete` 为假 |
| `test_pair_phase_keep_going_with_pair_workers` | 同上，走 `BLOCK_PAIR_WORKERS=2` 的进程池路径，结果一致 |
| `test_pair_phase_default_raises_at_the_first_failure` | 同上、开关关闭：在 `pair_0_0` 处抛出 |
| `test_tolerated_proposal_failure_is_not_a_kept_failure` | 只有提议失败、降级后证出：不算 keep-going 失败，节点 complete |
| `test_cli_keep_going_lists_every_failure` | CLI `--keep-going`：JSON 列出两条失败（name/answer/seconds），退出码 1，节点 inconclusive |
| `test_cli_environment_switch` | `BLOCK_KEEP_GOING=1` 等价于 `--keep-going` |
| `test_cli_default_is_off` | 默认关闭：`keep_going_failures` 为空，只有第一条失败 |
| `test_production_never_enables_keep_going` | 参数默认 False；三个生产模块的源码里不出现 `keep_going`/`KEEP_GOING` |

原有的相关测试（`test_block_prefix_maps.py`、`test_block_probe_cli.py`、`test_block_pair_workers.py`）单独跑过：32 passed。

## 5. 离线验证数据

本任务是诊断开关，没有服务器上的离线数据。在云端用 `tests/data/muti_block` 的 pc=120 节点（2×2 全积，0.3s）做了端到端验证：人为让 `pair_0_0`、`pair_1_1` 返回 sat，打开开关后 4 条 pair 全部被尝试，JSON 列出两条失败，节点 inconclusive，退出码 1；关闭时只尝试到 `pair_0_0` 就停止。

## 6. 未解决的问题

- Safe 5377 上下文 a/b 的实际 keep-going 运行要在服务器上做（单节点可能需要数小时）。云端没有 Safe 合约数据，也没有足够的预算。
- 每条卡住的义务仍然会耗尽自己的路由预算（约 2500s）。如果第 59–170 行里还有很多硬义务，`--node-seconds` 需要相应加大，否则会在 `ProofBudgetExceeded` 处中止。此前已记录的失败仍会输出。
- `_correspondence` 里的 `evm_disjoint_*` 失败本来就不会终止节点（会回退到全积），不在本开关的范围内。`check_paths` 阶段的失败仍然立即终止（见 §2）。
