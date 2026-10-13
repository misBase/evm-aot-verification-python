# 任务 B：P1–P6 提速转正（任务名 b3b-port）

先读 COMMON.md、cloud-inputs/README.md、cloud-inputs/exec5377/REPORT.raw.txt。

1. 以 `cloud-inputs/b3b/r37c.patch` 为起点，它是相对 snap-r35b（等于本分支父提交）的补丁，由上一个 agent 移植了 P1–P6，因额度中断未收尾。把它应用到当前代码，逐项核对实现与 REPORT 中的健全性论证是否一致：
   - P1：unknown 不剪枝，只有探针 UNSAT 才剪；
   - P2：只把模型当作 SAT 证书使用；
   - P3：只用子合取式做 UNSAT；
   - P4：映射只是提议；
   - P5：只调整路由顺序；
   - P6：只在 simplify 结果互补时判 UNSAT。
   有问题就修正。
2. 补齐单元测试。至少覆盖：
   - P1：增量 solver 与新建 solver 答案一致，包括 pop 回公共前缀的情形；
   - P3：去重后记录名和覆盖范围不变；
   - P6：命中、不命中各一例。
   参考 `cloud-inputs/b3b/unit*.log` 里已有的测试结果。
3. 汇总 `cloud-inputs/server/r37c-5377/` 的实测数据，做两张表：
   - stage-* 与 base-* 的分阶段耗时对比，包括 x86 段、coverage、correspondence、pair；
   - "all" 行的数量，以及路径集合是否一致（x86 171/178 条、EVM 86 条）。
   两个上下文最后仍是 inconclusive：a 卡在 `pair_63_10`，b 卡在 `pair_68_8`。请判断这两条是不是 "all" 行产生的 pair 义务，即 P4 没有给出映射；如果是，说明原因，以及这个问题是否可以通用地修掉。
4. 按 COMMON.md 交付到分支 `cloud/b3b-port`。
