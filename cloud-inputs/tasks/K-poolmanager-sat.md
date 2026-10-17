# 任务 K：Uniswap V4 PoolManager 三个 SAT 结论定性（任务名 poolmanager-sat）

先读 COMMON.md。基于分支 `cloud/inputs-poolmanager` 开工，它的代码等于冻结提交 caa01b1，Safe 和 ENS 已用这份代码拿到证书。

## 背景
- 被验证的是 `cloud-inputs/poolmanager/PoolManager.{json,hex}`：solc 0.8.26，hex 由修复了 CALLDATALOAD 的编译器重新编译。
- 用证书参数做普查（`--gas-check full --timeout-ms 30000 --summaries --discover-first --constant-insensitive --max-parameter-values 32`），已经证出 816 个实例。下面这三个块给出了 **SAT**，也就是求解器找到了一个模型，而不是 unknown。普查快照见 `PoolManager-survey.partial.json`，节点列表见 `nodes_sat.json`。
  1. `pc=7132, stack_depth=16`（m/f 符号）：`outcome mismatch x86_maps_0_0: x86 path 0 implies conjunct 0 of evm path 1 (solver=sat)`，约 0s。
  2. `pc=7329, stack_depth=12`（m/f 符号）：同类报错，`x86_maps_0_0` 为 sat，耗时 560s。
  3. `pc=7024, stack_depth=19`：m/f 符号的实例和 m=768/f=768 的实例都报 `H2 c0_(0,0) / c0_(0,2) not closed into pc=15674 (solver=sat)`。
- SAT 有两种可能：(a) 真实不等价，即编译器 bug。另一个合约（DABE）里刚发现过一个，原因是 IR 的 `immediate_set` 缺了一个返回目标，导致 x86 侧报错退出。(b) 验证器方面的问题：对应关系的提议错了，但没有回退到别的映射；路径条件建模过窄或过宽；H2 目标实例的专门化参数与边的后状态不匹配，等等。

## 要做的
1. 用 `tools/probe_block_obligations.py`（加 `--formula-dir`）或直接调用 prover，复现这三个节点，抓下 SAT 的义务，取出**具体反例模型**。
2. 对每一个，把反例落到**具体执行**上：用模型里的 calldata、栈、存储等具体值，分别在 EVM 语义侧和 x86 符号执行侧（或尽量用具体值）走一遍这个块，看两边的结果（跳转目标、状态码、栈、存储、gas）是否真的不同。
3. 定性：
   - 如果是**真实不等价**：指出 x86 代码里哪几条指令与 EVM 语义不一致，对照 go-hpc-evm 的 codegen 或 IR 的 `immediate_set`，判断是编译器问题还是 IR 分析问题，给出最小复现方式。不要改 Go，只写清证据。
   - 如果是**验证器的问题**：找到根因，给出**通用**修复，附健全性论证，并补测试。
   - 对 7024 的 H2：说明边的后状态与目标实例 pc=15674 的入口关系在哪个分量上不一致，以及目标实例的选择是否正确。
4. 跑全量快测（目标 0 失败）。交付到分支 `cloud/poolmanager-sat`，报告写在 `cloud-inputs/reports/poolmanager-sat.md`。
