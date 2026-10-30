# 任务 N4 补充说明（10-30，服务器新数据）

分支 `cloud/inputs-n4b` = 你的最后提交 24e375d + 本目录 `cloud-inputs/n4b/`。请 `git merge origin/cloud/inputs-n4b`（只新增文件，不会冲突）后继续，原任务书 `N4-remaining-blocks-4.md` 仍然有效。

## 1. 先完成你中断前没跑完的
- Aave 7200 整节点（修法 16 + 20）、PoolManager 4418 整节点（修法 18 自适应）、PoolManager 16670 m=None 整节点、全量快测，报告里的"待补"。
- 会话已经中断过两次（N3 一次、N4 一次）。长任务请后台运行并带内存上限，结果每出一个就提交推送一次。

## 2. 服务器上 PoolManager 3G 新暴露的难块（第一轮快跑完，3649/3718 已尝试，3625 证出）
节点规格：`cloud-inputs/n4b/poolmanager-3g-nodes.json`（24 个实例，`probe_block_obligations.py` 输入）；诊断：`poolmanager-3g-diag.json`。按原因分类（3G = 修法 1–8，每节点 43200 s）：

| 块 | 实例 | 3G 上的结果 |
|---|---|---|
| 18089 | 4 | `x86 segment execution deadline exhausted`（12 h） |
| 19169 | 3 | `H2 c0_budget exhausted (solver=unknown)`（块内证出，H2 出边预算耗尽，~44500 s） |
| 23522 | 2 | 同上，H2（第一轮 300 s 后 deferred；第二轮因服务器整组重启没跑完） |
| 21213 | 2 | `x86: outcome guards do not cover the entry domain`：`x86_coverage` unknown（~27200 s） |
| 6084 | 2 | 预算耗尽；其中一个 `x86_maps_2_8` unknown（583 s） |
| 4418 | 2 | 预算耗尽（你已在做） |
| 16670 | 3 | `pair_4_84` unknown（N3 已修） |
| 22747、22918 | 5 | 进程池被内核 OOM 打断（3G 进程池整池报废），没有结论；22918 d39 是 x86 分段超时后 deferred |

请在你的最终代码上，对 18089、19169、21213、6084、22747、22918、23522 各做 1 h 分诊（或整节点，看内存），说明它们是否已被修法 9–21 覆盖；没覆盖的给出根因和通用修法。

## 3. 内存
- 服务器上 PoolManager 收尾阶段反复有节点在几分钟内涨到 15–24 GB，三次触发内核 OOM（10-25、10-27、10-29），每次 3G 进程池整池报废、所有在跑的节点一起丢失。你的 `NodePool` + 单节点内存预算正好对应这个问题；请在报告里给出建议的 `--node-memory-mb` 值，以及 worker 数与内存的配置建议（服务器：16 核 / 32 GB + 32 GB swap，和 8 核 / 16 GB + 40 GB swap）。
- 哪个节点在暴涨，3G 上无法定位；如果你的分诊能复现，请指出。
