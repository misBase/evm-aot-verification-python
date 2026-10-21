# 任务 N：Permit2 1327 剩余 pair、Aave 4 块、PoolManager 4 块的根因与通用修法（任务名 remaining-blocks）

先读 COMMON.md。基于分支 `cloud/inputs-n` 开工。它的代码就是任务 M 的产出 3F（`claude/m-hard-blocks-46hta8` fa22b52，即 3C+3D+3E+任务 M 的修法 1–4）。本地已确认在 3F 上全量快测 1747 passed / 0 failed。先读 `cloud-inputs/reports/unknown-blocks.md`（任务 L）和 `cloud-inputs/reports/hard-blocks.md`（任务 M），不要重复已试过的路线；任务 M 的诊断工具在 `cloud-inputs/m/tools/`。

## 背景
- 所有 hex 都由修复后的 go-hpc-evm 编译器生成：
  - Permit2：`cloud-inputs/r3c/fixtures/Permit2.*`
  - PoolManager（Uniswap v4）：`cloud-inputs/r3c/fixtures/PoolManager.*`
  - Aave V3 Pool：`cloud-inputs/m/fixtures/Pool.*`
- 全量参数与任务 M 相同。
- **目前三个合约都没有出现任何 SAT（反例）。** 下表全部是 unknown 或预算、超时耗尽。
- 各节点在哪个代码版本上失败：
  - Aave 全量跑在 3C+3D 上，不含 3E 和 3F；
  - Permit2、PoolManager 全量跑在 3C+3D+3E 上，不含 3F；
  - **请先在 3F 上复现**，部分节点可能已经被 3E 或 3F 解决。
- 节点规格可以直接作为 `probe_block_obligations.py` 的输入：`cloud-inputs/n/n-aave-nodes.json`、`cloud-inputs/n/n-poolmanager-nodes.json`；完整诊断在同目录的 `*-diag.json`。

| 优先级 | 合约 | 块 / 实例 | 失败位置 | 材料 |
|---|---|---|---|---|
| 1 | Permit2 | 1327，depth 10 符号 | 任务 M 之后，所有 `x86_maps` 都已证出。整节点卡在两条 all 行 pair 上：`pair_0_6`（5925s）、`pair_0_7`（1943s），结果 unknown，都是 `exit@1273 / terminal@75335`。场景是 x86 在 SSTORE 一类的 gas 检查上 OOG，EVM 正常退出；与 `x86_maps_0_46` 是同一个 gas 等价关系，方向相反 | `cloud-inputs/m/smt2/permit2_1327_pair_0_6.smt2`，任务 M 报告 §6.4、§8.5 |
| 1 | Permit2 | 1327，m=192 f=128 | 任务 M 没跑完整节点。请跑一次，确认是否有同类 pair | `cloud-inputs/m/m-permit2-nodes.json` |
| 2 | Aave | 11831，depth 12 m=96 f=128，带常量 | 209s 时 `evm_assumption_7` unknown（EVM 执行假设没证出） | n-aave |
| 2 | Aave | 6182，depth 14 符号，带常量 | `proof wall budget exhausted`（21621s） | n-aave |
| 2 | Aave | 7200，depth 13 m=96 f=128，带常量 | `x86 segment execution deadline exhausted`（21603s）：**x86 符号执行本身超时**，还没进入证明 | n-aave |
| 2 | Aave | 8248 | 任务 M 的修法 2 已经能离线证出 `pair_0_1`，但整节点在云端被 OOM 杀掉了。如果内存允许，就跑一次整节点；不允许就跳过 | `cloud-inputs/m/m-aave-nodes.json` |
| 3 | PoolManager | 4418（两个实例） | `pair workers outran the node deadline`（6h）。任务 L 中也是预算问题 | n-poolmanager |
| 3 | PoolManager | 9089，depth 2 符号 | `pair_34_25` unknown（3634s）。`x86_maps_7_0` / `8_0` 是 SAT，但这只是对应关系的提议错了，这一行之后会退回 all 行，**不是反例**。请确认这个判断 | n-poolmanager |
| 3 | PoolManager | 16670（三个实例） | `pair_2_74`（9856s）/ `pair_4_84`（15829s）unknown，或者 6h 预算用完 | n-poolmanager |
| 3 | PoolManager | 6084，m=864 f=768，带常量 | `proof wall budget exhausted` | n-poolmanager |

## 要做的
1. **先分诊，再深挖。** 对每个节点，先在 3F 上用短预算（例如 `--node-seconds 3600 --keep-going`）跑一遍，并保存 `--formula-dir`，按卡住的类别归类：
   - 内存视图、SHA3、除法、memgas、gas 等价、深层 ITE；
   - 预算分配问题；
   - 符号执行爆炸。

   然后按上表的优先级深挖，**优先找能覆盖多个块的共性根因**。时间不够时，按优先级取舍，并在报告里写清哪些块还没做。
2. **义务是否成立**：用模型、具体值或分情况来试探。如果出现 SAT，按 PoolManager 7329 那次的做法，用具体执行确认是不是编译器问题，并写在报告第一段。
3. **Aave 7200**：查清 x86 分段执行为什么超时，是哪个循环或哪种路径爆炸，以及它是否属于已有 summary（copy-loop、CALLDATALOAD、MUL、DIV、memgas）应当覆盖却没有覆盖的情形。修法要是通用的。
4. 对每个修法，要做到：
   - 写健全性论证；
   - 在本任务的节点或公式上离线验证，给出修法前后的耗时；
   - 对已证的义务做回归，包括任务 L、任务 M 的 SMT2（`cloud-inputs/m/smt2/`、`cloud-inputs/r3c/smt2/`）；
   - 补单元测试；
   - 全量快测 0 失败。
5. 内存：云端机器在 Aave 8248 整节点时曾被 OOM 杀掉。重节点请串行跑，必要时减小 `BLOCK_PAIR_WORKERS`。
6. 交付：
   - 推送分支：任务书建议用 `cloud/remaining-blocks`；如果会话只允许推送 `claude/...` 分支，就推到那里，并在报告第一行写明分支名。
   - 报告写在 `cloud-inputs/reports/remaining-blocks.md`，包括：
     - 结论表：每个块的义务是否成立、根因、修法、修法前后耗时；
     - 改动位置；
     - 健全性论证；
     - 测试结果；
     - 未完成的块及原因。
   - 中途可以先推送草稿。
