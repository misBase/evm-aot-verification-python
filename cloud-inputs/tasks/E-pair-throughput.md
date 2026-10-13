# 任务 E：pair 阶段吞吐（任务名 pair-throughput）

先读 COMMON.md、cloud-inputs/README.md、cloud-inputs/par12930-REPORT.raw.txt（之前做过的路由与调度分析）、cloud-inputs/reports/pair58-fix.md。基于分支 `cloud/b3b-merged` 开工（候选 r37d = P1–P6 + 轻前提修法）。

## 现状
r37d 跑 Safe 5377 的两个 depth=30 上下文。约 6 分钟就进入 pair 阶段，之后不再卡在单条义务上，但吞吐太慢。BLOCK_PAIR_WORKERS=4，前 1.75 小时的数据：
- 上下文 a：310 条 `x86_maps_*` 共 7472s（平均 24s），30 条 `pair_*` 共 7628s（平均 254s，最慢 848s）；只推进到 correspondence 的约 33/171 行。
- 照这个速度，两个上下文各需约 9 小时，原来的 10800s 节点预算不够。现在已改用 43200s 预算重跑。
- 数据在 `cloud-inputs/server/r37d-5377/`：
  - `answers-run1-{a,b}.txt`：每条义务的名字、答案、耗时、SMT2 文件名；
  - 两个上下文各自最慢的 8 条 pair 义务 SMT2，文件名带 `a-`、`b-` 前缀。

## 要做的
1. 用 `cloud-inputs/tools/check_obligation.py`，在本分支代码下对这些慢义务逐条做路由剖析：时间花在哪些路由上，哪个路由最终胜出，失败的路由各花了多少时间。可以给 `_check` 加 trace 的 monkeypatch，或者参考 par12930 报告里的 route_trace 方法。轻前提探针在不命中时的开销也要量化。
2. 设计**通用**的吞吐改进，按收益排序。不改变"哪个公式被证"，只改调度、路由顺序和缓存。可能的方向：
   - 按义务类别统计各路由的成功率，按成功率排序路由；
   - 跳过从未成功过的路由前缀；
   - 兄弟义务之间共享引理；
   - 轻前提探针的触发条件。
   每项都要附健全性论证：只改顺序和预算，UNSAT 仍然来自原有的可靠路由。
3. 实现收益最大的 1–3 项，补单元测试，然后在这些慢义务上离线对比改动前后：答案必须一致，或者从 unknown 变成 unsat；给出耗时。
4. 跑全量快测。交付到分支 `cloud/pair-throughput`，报告写在 `cloud-inputs/reports/pair-throughput.md`。
