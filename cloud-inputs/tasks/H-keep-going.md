# 任务 H：诊断模式下出错后继续跑（任务名 keep-going）

先读 COMMON.md。基于分支 `cloud/b3b-final` 开工。

## 背景
节点证明的 pair 阶段（`verification/block_equivalence.py` 的 `_pair_phase` / `_check_rows` 一带）遇到第一条失败义务就抛出 `ValueError: outcome mismatch …`，整个节点随即终止。Safe 5377 的 depth=30 上下文共有 171 行 x86 路径，运行到第 58 行的 `pair_68_58` 时卡住，于是第 59–170 行**一次都没有被尝试过**，我们不知道后面还有没有别的硬义务。

## 要做的
1. 给诊断工具 `tools/probe_block_obligations.py` 增加一个开关，例如 `--keep-going` 或环境变量 `BLOCK_KEEP_GOING=1`。打开后，pair 阶段的失败义务会被记录下来，但不中断运行，其余行继续证明。
   - 节点最终状态仍然必须是失败或 inconclusive，绝不能因为"继续跑"而报告 proved。
   - 输出 JSON 里列出**全部**失败义务：名字、答案、耗时。
   - 默认关闭。生产路径（`tools/verify_block_lockstep.py` 以及块并行调度）的行为必须完全不变；用测试证明开关关闭时代码路径与原来一致。
   - 如果把这个开关做成 prover 的参数更自然，也可以，但生产调用点不能打开它。
2. 写单元测试：
   - 构造一个有两条失败义务的小场景，打开开关后两条都被报告，节点不是 proved；
   - 开关关闭时，在第一条失败处就停止。
3. 跑全量快测（目标 0 失败）。交付到分支 `cloud/keep-going`，报告写在 `cloud-inputs/reports/keep-going.md`，说明用法（命令行示例）。
