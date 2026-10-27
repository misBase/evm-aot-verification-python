分支（任务 N3 / remaining-blocks-3）：`claude/n3-remaining-blocks-3-p77zn8`（会话只允许推送这个 `claude/...` 分支，未使用任务书建议的 `cloud/remaining-blocks-3`），基于 `cloud/inputs-n3`（ac0088f = N2 的 b7d4faa + 本任务输入）。

# 任务 N3：3G 冻结版上剩余的 inconclusive 块

（草稿：运行中的结果在完成后填入。）

## 1. 结论

| 合约 | 块 / 实例 | r5（3G，服务器） | 根因 | 修法 | 本机结果 |
|---|---|---|---|---|---|
| PoolManager | 16670 sym7296 | `pair_4_84` unknown（26002s） | SDIV 符号分支树：x86 每个分支各有一个 `holiman_udiv`，参数只在本分支守卫下与 EVM 的 `holiman_udiv(|a|,|b|)` 相等 | 9：按 UF 守卫分情形再合并（`guards` 路线）；10：合并循环的排序键记忆化 | goal 2 单独 1326.6s proved；整节点：运行中 |
| Aave | 6182 | `pair_63_2` unknown（792.9s，12h 预算末尾） | 对应关系提议在 3s 内 unknown，8 个 x86 行变成 "all"（每行 95 个 pair）；`pair_63_2` 单独可证但要 2883s（goal 6 由补跑的 potential 求解证出） | 11：对应关系提议的 blast 回退；12：补跑的 potential 求解按类记账、提前 | `pair_63_2` 单独 2121s / 2883s proved；无见证时 "all" 行 8 → 1；整节点：运行中 |
| Aave | 7200 | x86 分段 12h 超时 | 每个 DIV 命中把 8 个栈 limb 各自对整条 x86 内存链做一遍 `forward_selects`（新缓存），占 x86 分段 53% | 13：limb 转发共享缓存 | 首个 div 命中 1121s（剖析下）/ 405s（N2）→ 90.1s；整节点 12h：运行中 |
| PoolManager | 4418 | 两个实例 12h 预算耗尽；sym 的 `x86_maps_1_0` 13894s unknown | x86 876 条路径：每个内存访问的扩展费代码里 `words == 0` 分支（跳过平方）在后面汇合，执行器不合并 | 未修（方向见 §2.4） | x86 分段 2684s，90% 是 6105 次可达性检查 |

修法编号接任务 N / N2（1–8）。全部只改 Python 端，没有按合约或块号特化。

## 2. 逐块分析

### 2.1 PoolManager 16670（`pair_4_84` / `pair_2_74` goal 2）

（待补）

### 2.2 Aave 6182（`pair_63_2`）

（待补）

### 2.3 Aave 7200（x86 分段）

（待补）

### 2.4 PoolManager 4418（1h 分诊）

（待补）

## 3. 改动位置

（待补）

## 4. 健全性论证

（待补）

## 5. 测试结果

（待补）

## 6. 整节点与离线数据

（待补）

## 7. 未解决的问题

（待补）
