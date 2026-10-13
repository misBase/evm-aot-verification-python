# 任务 F：合并批次 3B 候选（任务名 b3b-final）

先读 COMMON.md，以及 cloud-inputs/reports/ 下的四份报告：b3b-port.md、pair58-fix.md、review-3b.md、pair-throughput.md；test-hygiene.md 在分支 cloud/test-hygiene 上。

基于 `cloud/b3b-merged`，新建分支 `cloud/b3b-final`，依次合并：
1. `origin/cloud/review-3b`：`_prove_equal` 缓存持有 AST（必须修），以及审查测试；
2. `origin/cloud/test-hygiene`：msize_absint 去掉 tmp 依赖，偶发失败的测试改用 rlimit；
3. `origin/cloud/pair-throughput`：按类别 winner-first 的路由顺序；core 探针得到 SAT 时跳过 case tree；`_heavy`/`_no_binder` 按项 memo。它也**独立修了同一个缓存 id 回收问题**。

要求：
- review-3b 和 pair-throughput 对 `_prove_equal` 缓存的修法可能冲突。合并后只保留一套实现，并且必须同时满足下面几点：
  - 所有成功条目都持有键里的 x、y，以及 id 集合中的全部合取项；
  - 失败条目可以不持有任何项；
  - pair-throughput 新增的"core 探针 SAT 时跳过 case tree"所写入的条目也必须满足上述要求。
  两边的测试都要保留并通过：test_block_lemma_cache_ids.py、test_block_prove_equal_sat.py 等。
- `_memoized` 等按 id 做的缓存要核对：是否持有了项的引用（参考 common/store_forwarding.py 的 `_put`）。
- review-3b 的两条"建议修"（correspondence 的 PrefixSolver 墙钟上限是预算的 10 倍；`_retry_with_uf_unification` 的轻前提查询用了整条单查询预算），如果 pair-throughput 没有处理，就按审查建议做最小修复：轻前提查询改用 `_LIGHT_MS`；墙钟上限与原 timeout 对齐。每项附一条测试。
- 合并后跑**全量**快测：`poetry run pytest tests/unit -q -m "not slow" -p no:cacheprovider`，目标是 0 失败。再跑 `tests/integration` 中和 block 相关的测试（文件名含 block 的那些），报告结果。
- 交付到分支 `cloud/b3b-final`，报告写在 `cloud-inputs/reports/b3b-final.md`，内容包括：合并冲突及其处理、最终改动清单（文件:行）、测试结果。
