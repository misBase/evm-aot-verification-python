# 任务 M：Permit2 1327 / 8750 与 Aave 8248 的根因与通用修法（任务名 hard-blocks）

先读 COMMON.md。基于分支 `cloud/inputs-m` 开工。它的代码 = 任务 L 的产出（3C+3D+3E，即 `claude/unknown-blocks-37upmv`），与服务器上跑 Permit2 的快照 snap-3cde 逐文件一致（verification/common/state/x86_64/evm_ir/tools 的 git tree 完全相同）。任务 L 的报告在 `cloud-inputs/reports/unknown-blocks.md`，先读，避免重复已试过的路线。

## 背景
- hex 均由修复后的 go-hpc-evm 编译器生成（分支内写回缺陷 + SMOD 负号标志已修）。
  - Permit2：`cloud-inputs/r3c/fixtures/Permit2.{hex,json}`
  - Aave V3 Pool：`cloud-inputs/m/fixtures/Pool.{hex,json}`
- 全量运行参数：`--gas-check full --timeout-ms 30000 --first-pass-node-seconds 300 --node-seconds 21600 --max-depth 400 --max-instances 8192 --max-parameter-values 32 --summaries --discover-first --constant-insensitive`，环境 `BLOCK_SUMMARY_LEMMAS=1 PYTHONHASHSEED=0`。
- Permit2 全量已跑完：1150 个证明实例中 1145 个证出，下列 5 个 inconclusive。Aave 跑在 3C+3D（不含 3E）上，8248 在服务器上用本分支代码（含 3E）单独重证，结果仍是 inconclusive。**都不是 SAT**。

| 合约 | 块 | 实例 | 现象 | 材料 |
|---|---|---|---|---|
| Permit2 | 1327 | depth 10，m/f 符号 | 跑 11293s 后，`x86_maps_0_46` unknown（这一条 4025s） | `m/m-permit2-diag.json` |
| Permit2 | 1327 | depth 10，m=192，f=128 | 跑 13464s 后，`x86_maps_0_46` unknown（这一条 6352s） | 同上 |
| Permit2 | 8750 | depth 11 符号；depth 11 与 15 带常量 (0,0) | 局部定理已证出，**H2 出边闭合**用尽 21600s 的上下文预算：`H2 c0_budget exhausted` | 同上 |
| Aave | 8248 | depth 17，m=352，f 符号，14 个栈常量 | 7006s 后 `pair_0_1`（exit@8414 / exit@539522）unknown，这一条 5325s | `m/formulas/*.sexpr`（已导出公式）、`m/aave-8248-probe.json` |

- 节点规格：`m/m-permit2-nodes.json`、`m/m-aave-nodes.json`，可以直接作为 `tools/probe_block_obligations.py` 的输入。
- 任务 L 中 1327 当时卡在 `x86_maps_0_0/0_1`。现在卡在 `0_46`，但不代表 0..45 都证出了：maps 是按前缀分组处理的，不是逐条按顺序证。请自己确认 0_46 之外还有哪些没证出。
- 8750 的 H2 走 `verification/block_parallel.py: prove_instance → close_edge`。`probe_block_obligations.py` 只证局部定理，不跑 H2。复现 H2 需要先做发现（`discover`），再用 `_init_worker` + `prove_instance`。可以写一个小脚本，只挑这几个节点跑；发现阶段在 Permit2 上只需几分钟。

## 要做的
1. **逐个确认义务本身是否成立**：用模型、具体值或分情况试探。如果出现 SAT，按 PoolManager 那次的做法，用具体执行（Unicorn 等）确认是不是编译器问题，并立刻在报告第一段写明。
2. **1327 `x86_maps_0_46`**：找出这条合取项来自 EVM 路径的哪一个条件，以及 x86 侧对应的写法。先做同形比较，找出卡住的子项，给出通用修法。
3. **8750 H2**：找出哪个出边、哪个目标、哪个合取项把预算耗尽了（`close_edge` 的逐合取项记录）。是成立但难证，还是这个目标本来就不该匹配（应当被快速筛掉却没被筛掉）？给出通用修法，比如更早的目标筛选、合取项独立性、预算分配等。
4. **Aave 8248 `pair_0_1`**：在导出的公式上离线分析，判断是否成立，以及卡在哪类子项（内存视图、SHA3、除法、memgas、深层 ITE 等）。给出通用修法。
5. 每个修法都要满足：
   - 附健全性论证；
   - 在本任务的节点或公式上离线验证（给出修法前后的耗时）；
   - 对已证义务做回归（抽查已证块，或跑相关单元测试）；
   - 补单元测试；
   - 全量快测 0 失败。
   证不出的块，就写清已排除了什么、下一步该往哪个方向。
6. 交付：推送分支（任务书建议用 `cloud/hard-blocks`；如果会话只允许推送 `claude/...` 分支，就推送到那里，并在报告第一行写明分支名）。报告写在 `cloud-inputs/reports/hard-blocks.md`：结论表（每个块：义务是否成立、根因、修法、修法前后耗时）、改动位置、健全性论证、测试结果。
