# 任务 A：pair58 候选修法转正（任务名 pair58-fix）

先读 COMMON.md 和 cloud-inputs/README.md。

1. 读懂 `cloud-inputs/pair58/fix.diff` 和同目录的笔记（shape_*、diff_58_8_vs_13.txt、goal_merged.txt 等），写清楚三件事：
   - 根因：`pair_58_13`、`pair_68_9`、`pair_58_12` 为什么证不出，和已证的兄弟 `pair_58_8` 差在哪里；
   - 修法做了什么；
   - 修法的健全性论证。
2. 把修法正式实现到当前代码里（补丁是相对 snap-r35b 写的，snap-r35b 等于本分支的父提交），写法和周围代码一致，并补最小单元测试，包括修法命中和不命中各一例。
3. 回归：
   - 对比 `cloud-inputs/server/pair58-server/reg_patched.log` 和 `reg_base.log` 的逐条答案，列出所有答案发生变化的义务。重点是 unsat 变成别的答案，以及 sat 变成 unsat。后者必须逐条解释清楚，否则视为健全性问题。
4. 离线验证（云端 CPU 能跑多少就跑多少，每条最多 1800s）：用 `cloud-inputs/tools/check_obligation.py`，对修法前后的代码各跑一遍下面这些义务：
   - `cloud-inputs/cap5377d30-local/` 下的三条；
   - `cloud-inputs/server/r37c-5377/smt2-a/` 里的 `pair_63_10_*` 和 `smt2-b/` 里的 `pair_68_8_*`（如果存在）。
   报告每条的答案和耗时。
5. 按 COMMON.md 交付到分支 `cloud/pair58-fix`。
