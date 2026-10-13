# cloud-inputs（5377 收尾任务的输入，不进主线）

目标：Safe 合约块 5377 在 stack_depth=30、memory_size/fmp 符号的两个上下文证不出，是 CErc20/Safe 完整块级证书的最后缺口。

- 上下文 a：stack_constants ((14,3575))；上下文 b：((1,0),(2,0),(14,3575),(15,0),(16,0),(17,128),(28,759))。
- 冻结代码 = 本分支的父提交 develop-cutpoint（与服务器快照 snap-r35b 一致）。

## 目录
- `cap5377d30-local/`、`server/cap5377d30/`：snap-r35b 抓取结果。卡住的义务：a 的 `pair_58_13`、`pair_68_9`，b 的 `pair_58_12`（各约 2500–2800s unknown）。EVM 第 58/68 行是 correspondence 的 "all" 行。`answers*.txt` 是节点内全部义务的答案/耗时；`pair_58_8_*`、`pair_58_1_*` 是已证兄弟。
- `pair58/`：上一个诊断 agent 的半成品（额度中断，没写 REPORT）。`fix.diff` 是候选修法（对 snap-r35b）；`*.txt` 为形状/拆解笔记；`regress.py`/`regress.list` 回归脚本。
- `server/pair58-server/`：服务器跑完的结果。`f2_58_13_all.log` 显示打补丁后 `pair_58_13` proved 574s，`f2_68_9_all.log` 显示 `pair_68_9` proved 833s；`reg_patched.log` 和 `reg_base.log` 是补丁前后对同一批义务的回归对比。
- `b3b/`：P1–P6 提速移植的半成品（额度中断）。`r37c.patch` 是对 snap-r35b 的补丁，`unit*.log` 是测试日志。
- `server/r37c-5377/`：用 r37c（加了 P1–P6）跑两个上下文的结果。两个都仍是 inconclusive：a 卡在 `pair_63_10` unknown 2988s，b 卡在 `pair_68_8` unknown 3486s。`smt2-*/` 里是全部非 unsat 的义务 SMT2，`stage-*/` 是 opt 运行的分阶段计时，`base-*/` 是 base 运行的分阶段计时。
- `exec5377/REPORT.raw.txt`：P1–P6 的设计、实测和健全性论证；`par12930-REPORT.raw.txt` 是路由/调度分析。
- `tools/check_obligation.py`：在仓库根目录 `PYTHONPATH=.` 下，用生产 `_check` 跑捕获的 SMT2（每条义务 1800s）。
