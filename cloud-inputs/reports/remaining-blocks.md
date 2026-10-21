分支：`claude/inputs-n-remaining-blocks-rm2fog`（会话只允许推送 `claude/...` 分支，未使用任务书建议的 `cloud/remaining-blocks`）。基线 = `cloud/inputs-n`（d15c606，即任务 M 的 3F）。

# 任务 N：剩余块 —— 草稿（进行中）

本文件是中途草稿，结论表和数据会在后续提交中补全。

## 已完成

- 基线复现：3F 上全量快测 1747 passed / 3 skipped / 0 failed。
- **修法 1（乘积字泛化）**：Aave 11831 的 `evm_assumption_7` 是关于 256 位乘积字的恒真式，
  按乘积字整体泛化后 0.0s unsat；整节点 74.5s proved（原 209s inconclusive）。
- **修法 2（内存势函数的值域/单调公理）**：Permit2 1327 的 `pair_0_6` / `pair_0_7`
  不是 SSTORE 的 gas 等价问题，而是 x86 路径 6/7 本身不可行：LOG2 费用
  `8·len + 1125 + 扩展费` 的 64 位溢出检查，在已检查过的新内存尾 < 2^37 下不可能溢出。
  `x86_empty_6` 147.4s、`x86_empty_7` 127.9s proved（原 pair 5925s / 1943s unknown）。

## 进行中

- Aave 7200 x86 分段执行剖析；PoolManager 9089 分诊；其余节点排队分诊。
