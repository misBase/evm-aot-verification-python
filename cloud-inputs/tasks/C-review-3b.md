# 任务 C：批次 3B 合入前的独立健全性审查（任务名 review-3b）

先读 COMMON.md、cloud-inputs/README.md，以及两份前序报告 cloud-inputs/reports/b3b-port.md 和 pair58-fix.md。

审查对象：分支 `cloud/b3b-merged` 相对 `cloud/inputs-5377` 的全部代码改动（cloud-inputs/ 目录除外）。这就是候选快照 r37d，内容是 P1–P6 提速加上轻前提反驳修法。

要求：
1. **只关心正确性，尤其是健全性。** 逐处找出所有可能让 Z3 给出"错误 UNSAT"的情形，也就是本应不成立的证明被判为成立。重点查：
   - P1 PrefixSolver：作用域与栈的一致性；与 rlimit、timeout 的交互；异常和 reset 后的状态；多个执行器或 fork 之间是否共享了 solver；witness 与增量 solver 的交互。
   - P2：witness 作为 SAT 证书时，模型里残留的量词或 lambda、model_completion 是否引入错误。
   - P3：按分叉点去重后，记录名与覆盖范围的对应关系是否成立；evm_disjoint 的分组是否会把未证的对误标为已证。
   - P4/P4b：映射提议出错时是否一定只会让证明失败，不会让证明跳过检查。
   - P6 refuted_by_complement：simplify 后用 AST 相等判断互补是否可靠；在什么前提下调用；RECENT 窗口的影响。
   - 轻前提修法：缓存键（保留合取项 id 集合）在 id 回收时是否安全。之前出过 id 被回收导致缓存返回错误结果的 bug，修法是 `_put` 持有节点引用，参见 common/store_forwarding.py。还要查 `_retry_with_uf_unification` 里去掉"否定目标"后的含义，以及与 deadline、预算相关的边界。
2. 每个疑点都要用最小 Z3 例子或单元测试**实测**：确认是真问题就给出修复和回归测试；确认不是问题就写明理由。
3. 跑全量快测，确认没有回归（已知例外 msize_absint 除外）。
4. 交付到分支 `cloud/review-3b`，报告写在 `cloud-inputs/reports/review-3b.md`，结论按"必须修 / 建议修 / 无问题"分级。修复作为单独的提交。
