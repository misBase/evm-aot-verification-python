# 任务 G：5377 最后一条硬义务 pair_68_58（任务名 pair6858）

先读 COMMON.md，以及 cloud-inputs/reports/ 下的 pair58-fix.md、pair-throughput.md、b3b-final.md。基于分支 `cloud/b3b-final` 开工（最终候选 r37f）。

## 现状
r37d（P1–P6 + 轻前提修法，不含 E 的提速和缓存修复）用 43200s 预算跑 Safe 5377 的两个 depth=30 上下文，前面一百多行的 pair 全部证出，最后两个上下文**都卡在同一条义务 `pair_68_58`**（EVM 第 68 行对 x86 第 58 条路径，terminal@5377 / terminal@284708），约 3900s 后仍是 unknown。同一 EVM 行的 `pair_68_8`、`pair_68_33` 分别用 295–848s、710s 证出。
- SMT2 文件：`cloud-inputs/server/r37d2-5377/{a,b}-pair_68_58.smt2`；
- 两次运行的全部答案：`answers-r37d2-{a,b}.txt`，兄弟义务 `pair_68_8`、`pair_68_33` 的耗时在里面。
- 本地正在用 r37f 离线跑这两条（7200s 上限），服务器也在用 r37f 跑完整的 5377，结果都还没出来。

## 要做的
1. 用本分支的代码和 cloud-inputs/tools/route_trace.py 剖析 `pair_68_58`：它拆成几个部分；卡在哪一部分、哪条路由上；与 `pair_68_8`、`pair_68_33` 在形状上有什么差别（参考 pair58-fix 报告的方法：比较合取项差集、内存目标的形状、sha3 参数、gas 项）。
2. 如果 r37f 现有路由在 3600s 内能证出，报告耗时和胜出的路由，到此为止。
3. 如果证不出，找出根因，设计**通用**修法并给出健全性论证（只允许可靠推理产生 UNSAT，抽象只能是过近似），然后实现、补单元测试，离线验证这两条义务，并对 `cloud-inputs/server/r37d-5377/` 下已证的慢义务做回归，答案必须不变或者从 unknown 变成 unsat。
4. 跑全量快测（目标 0 失败）。交付到分支 `cloud/pair6858`，报告写在 `cloud-inputs/reports/pair6858.md`。
