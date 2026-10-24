# 任务 N2：完成任务 N（remaining-blocks）的收尾，并在冻结版编译器产物上复核（任务名 remaining-blocks-2）

先读 COMMON.md。基于分支 `cloud/inputs-n2` 开工。它就是任务 N 的分支 `claude/inputs-n-remaining-blocks-rm2fog`（6bbad7f）加上本任务的输入。任务 N 的云端会话在 10-21 推出报告初稿之后中断了，报告 `cloud-inputs/reports/remaining-blocks.md` 中几节还写着"待最终运行"，请先完整阅读这份报告。

## 背景（任务 N 之后发生的事）
- go-hpc-evm 的编译器修复已经**冻结**，冻结版重新编译出的机器码放在 `cloud-inputs/n2/fixtures/`（Permit2、Pool=Aave、PoolManager；IR 不变）。各文件的 sha256 见 `cloud-inputs/n2/FROZEN_SHA256SUMS`。和任务 N 用的 hex 不同，所以 x86 路径编号会变。
- 冻结版机器码已经在 3F（fa22b52，不含任务 N 的修法）上做过全量运行（r4）：
  - **Permit2：1150 个实例中 1148 个证出，只剩块 1327 的两个实例 inconclusive。**两个都卡在 `pair_0_3: exit@1273 / terminal@73543 (solver=unknown)`，耗时分别约 4025 s 和 4433 s。这就是任务 N 报告 §2.2 的 `pair_0_6`，换了机器码，路径编号随之变化。节点规格和 r4 原因见 `cloud-inputs/n2/permit2-1327-nodes.json`。块 8750 在 3F 上已全部证出。
  - PoolManager（还在跑）目前确定 inconclusive 的有：4418 ×2（预算耗尽）、9089（预算耗尽）。见 `cloud-inputs/n2/poolmanager-r4-inconclusive-nodes.json`。
  - Aave 的服务器停机，还没有 r4 数据。

## 机器码版本说明（重要）
任务 L/M/N 用的 hex（`cloud-inputs/r3c/fixtures`、`cloud-inputs/m/fixtures`）是编译器**第一次修复（24 处统一写回）**的产物。现在冻结的是最终版：精确预留寄存器 + 编译期断言，精简了 DIV/MOD 的写回，修复了 BLOBHASH。两版的 x86 指令、路径编号和公式形状都不同。修法本身是验证器侧的通用改动，与机器码无关；但**本任务里所有的证明结果和耗时都必须在 `cloud-inputs/n2/fixtures/` 上取得**。SMT2 回归（m/n/r3c 下）只用来检查修法有没有破坏已证义务，不作为冻结版上的证据。

## 要做的（按优先级）
1. **全量快测**：`poetry run pytest tests/unit -q -m "not slow" -p no:cacheprovider`，目标 0 失败。若有失败，先修，或说明原因。本地机器多进程并行时，有些测试对负载敏感（报告 §5 提过 mcopy-high-word），请单独重跑确认。
2. **Permit2 1327（最高优先级，决定 Permit2 能不能拿到证书）**：在**冻结版** `cloud-inputs/n2/fixtures/Permit2` 上，用本分支代码（任务 N 的修法 1–7）跑两个节点的**整节点**证明：`probe_block_obligations.py --timeout-ms 30000 --node-seconds 21600`，串行，`BLOCK_SUMMARY_LEMMAS=1 PYTHONHASHSEED=0`。
   - 确认 `pair_0_3` 一类义务（x86 在 LOG2 费用溢出检查上走的那条路径）能被修法 2 消掉，例如变成空行；
   - 确认整节点证出。
   - 如果还有别的义务卡住，按任务 N 的方法定位，并给出通用修法。
3. **把报告里"待最终运行"的各节补完**：Aave 7200 的 x86 分段（修法 3–7 之后）、PoolManager 16670 / 6084 的整节点。**必须用冻结版机器码**（cloud-inputs/n2/fixtures/）。任务 N 在旧机器码（r3c/m 下的 hex，是第一版"24 处统一写回"编译器的产物）上测得的结论和耗时，只能作参考，不能当作冻结版上的结果。
4. **PoolManager 4418、9089**：两者都是预算耗尽类。在冻结版机器码上跑 1 小时分诊，看修法 1–7 之后有没有改善。如果仍然只是预算问题，写清楚瓶颈在哪，例如路径数或是哪一类义务。
5. 每个修法都要附健全性论证，并在已证义务的 SMT2 上做回归，`cloud-inputs/m/smt2`、`cloud-inputs/n/smt2`、`cloud-inputs/r3c/smt2` 都要跑。

## 交付
- 推送分支：建议用 `cloud/remaining-blocks-2`；如果只允许推 `claude/...` 分支，就推到那里，并在报告第一行写明分支名。**每完成一项就先推一次**，避免会话中断时丢失进度。
- 在 `cloud-inputs/reports/remaining-blocks.md` 中补全"待最终运行"各节，并新增一节"冻结版机器码复核"，内容包括：全量快测结果、1327 整节点结果，以及其余各项的结果与耗时。
