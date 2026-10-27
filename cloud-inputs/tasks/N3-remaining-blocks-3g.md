# 任务 N3：3G 冻结版上剩余的 inconclusive 块（任务名 remaining-blocks-3）

先读 COMMON.md，再完整读 `cloud-inputs/reports/remaining-blocks.md`（任务 N / N2 的报告，§2.3–2.5、§9 与本任务直接相关）。本分支 `cloud/inputs-n3` = N2 的结果分支 b7d4faa（下称 **3G** = 3F + 修法 1–8）+ 本任务输入。

## 背景：3G 在冻结版机器码上的全量运行（r5）
机器码：`cloud-inputs/n2/fixtures/`（冻结版，sha256 见 `cloud-inputs/n2/FROZEN_SHA256SUMS`）。运行参数：`--gas-check full --timeout-ms 30000 --first-pass-node-seconds 300 --node-seconds 43200 --max-depth 400 --max-instances 8192 --max-parameter-values 32 --summaries --discover-first --constant-insensitive`，`BLOCK_SUMMARY_LEMMAS=1 PYTHONHASHSEED=0`。
- **Permit2：VERIFIED**（1150/1150；1327 两个重节点 9518 s / 9171 s 证出）。
- **Aave（Pool）**：1281/1283 证出。
  - 6182（m=None）：12 h 预算用完 inconclusive，`outcome mismatch pair_63_2: terminal@6182 / terminal@382963 (solver=unknown)`，该义务 792.9 s。
  - 7200（m=96, fmp=128）：12 h 后 `TimeoutError: x86 segment execution deadline exhausted`，已拆成上下文实例重跑（结果未出）。报告 §2.3 / §6.3：修法 3–7 后 summary 不再被拒，但每条路径都重复付 summary 代价。
- **PoolManager**：进行中（1908/3718）。已确定 inconclusive：
  - 4418 ×2（m=None）：预算耗尽；其中一个 `x86_maps_1_0` unknown（13894 s）。报告 §2.4：877 条 x86 路径。
  - 16670（m=None）：`pair_4_84: terminal@16670 / terminal@689761 (solver=unknown)`，26002 s。报告 §2.5：SDIV 符号守卫下的 UF 参数合并，"先按守卫分情形再合并"已离线验证可证，但**没有进生产**。
- 节点规格（`probe_block_obligations.py` 输入）与诊断：`cloud-inputs/n3/aave-r5-nodes.json` / `-diag.json`、`cloud-inputs/n3/poolmanager-r5-nodes.json` / `-diag.json`（其中一个 status=split、原因 BrokenProcessPool 的条目是服务器 OOM 造成的，不是证明失败，可忽略）。

## 要做的（按优先级）
1. **16670 `pair_4_84`**：把"按 SDIV 符号守卫分情形再合并"做成生产里的通用机制，在冻结版 PoolManager 上跑 16670 整节点（`probe_block_obligations.py --timeout-ms 30000 --node-seconds 21600`，串行），确认 `pair_4_84` 证出；有别的义务卡住就继续定位。
2. **Aave 6182 `pair_63_2`**（新问题）：按任务 N 的方法定位（导出路径、前缀扫描、形状比较），给出通用修法并在整节点上验证。
3. **Aave 7200 x86 分段**：定位"每条路径重复付 summary 代价"的瓶颈，给出通用的加速（例如同一命中状态的证书复用），保持证书结构与健全性不变；在整节点上测到能否在 12 h 内跑完。
4. **PoolManager 4418**：1 h 分诊，说明瓶颈（路径数 / `x86_maps_1_0` 这类义务）以及可行方向；能修就修。
5. 每个修法：健全性论证；`cloud-inputs/m/smt2`、`cloud-inputs/n/smt2`、`cloud-inputs/r3c/smt2` 回归；全量快测 0 失败。

## 注意
- 所有证明结果和耗时都必须在 `cloud-inputs/n2/fixtures/` 上取得。
- 任何改动（包括纯提速）都会改变代码身份，已有 r5 结果不能复用、所有合约都要在新代码上重跑；所以请把修法集中在一个分支上，不要拆成多个版本。
- 只做通用机制，不按合约或块号特化。

## 交付
- 推送分支：建议 `cloud/remaining-blocks-3`；只允许推 `claude/...` 时推到那里，并在报告第一行写明分支名。**每完成一项先推一次。**
- 报告：`cloud-inputs/reports/remaining-blocks-3.md`，包括每块的结论、改动位置（文件:行）、健全性论证、测试结果、整节点耗时、未解决的问题。
