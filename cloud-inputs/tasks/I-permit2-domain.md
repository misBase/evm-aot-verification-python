# 任务 I：Permit2 pc=1327 的 model_domain_nonempty 检查返回 unknown（任务名 permit2-domain）

先读 COMMON.md（其中 msize_absint 的已知例外已经不存在，现在快测应当 0 失败）。基于分支 `cloud/inputs-permit2` 开工，它的代码等于冻结提交 caa01b1，Safe 和 ENS 已用这份代码拿到证书。

## 背景
- 用这份代码普查 Uniswap Permit2：`cloud-inputs/permit2/Permit2.{json,hex}`，hex 由修复了 CALLDATALOAD 的编译器重新编译。
- 节点 `BlockSpecialization(pc=1327, stack_depth=10, memory_size=None, free_memory_pointer=None, stack_constants=())` 报 `ValueError: oracle model and entry domain inconsistent or unknown`。这个节点有 61 条 EVM 路径、64 条 x86 路径。
- 报错来自 `verification/block_equivalence.py` 约 3511 行的 `_check("model_domain_nonempty", premise, records, expected="sat")`。它检查"入口前提 ∧ host_model_axioms ∧ div_quotient_axioms"是否可满足，作用是防止前提自相矛盾导致的空真证明。
- 抓到的公式在 `cloud-inputs/permit2/md1327.smt2`（带声明）。实测结果：
  - 生产路由 30s：unknown；
  - 默认 Solver 300s：unknown；
  - `SolverFor("QF_AUFBV")` 0.5s 就返回 unknown，疑似公式里有量词或 lambda。

## 要回答的问题
1. 这个公式到底是可满足（只是难解）还是不可满足（模型或公理互相矛盾）？构造一个满足它的模型（可以分段固定变量、去掉量词后求解、或用公理的语义直接构造），或者证明它不可满足并给出 unsat core。
2. 如果可满足：是哪一部分让求解器解不动（量词公理、乘法、数组 lambda、host UF 公理等）？给出**通用**的改进，让这项检查在合理时间内返回 sat。例如：检查时用给定 witness 构造模型后做 `model.eval` 验证（模型本身就是 SAT 证书），或者分层检查。必须附健全性论证：这项检查只能在真的给出模型时才算通过。
3. 如果不可满足：找出是哪条公理和入口条件冲突，判断这是建模错误还是真实的不可达，给出修复方案。
4. 写单元测试，跑全量快测（目标 0 失败）。交付到分支 `cloud/permit2-domain`，报告写在 `cloud-inputs/reports/permit2-domain.md`。
