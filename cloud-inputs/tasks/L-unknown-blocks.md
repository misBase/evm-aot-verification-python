# 任务 L：Permit2 / PoolManager 剩余 unknown 块的根因与通用修法（任务名 unknown-blocks）

先读 COMMON.md。基于分支 `cloud/inputs-r3c` 开工。它的代码 = 冻结提交 caa01b1 + 3C（常函数见证、1 字节 SHA3、发现期开关）+ 3D（节点间清缓存），与服务器上正在运行的快照 snap-3cd 逐文件一致。

## 背景
- 被验证的 hex 由**修复后的 go-hpc-evm 编译器**生成：修了分支内写回缺陷和 SMOD 负号标志。文件在 `cloud-inputs/r3c/fixtures/`，IR 与原 fixture 相同。修复后 PoolManager 原有的 SAT 已全部消失；ENS 在新编译器下拿到了证书。
- 下列块在单独预筛中，2 小时预算、`--keep-going` 都没证出。节点见 `cloud-inputs/r3c/nodes.txt`，预筛输出见 `out-pm.json`、`out-p2.json`。**都不是 SAT**：

| 合约 | 块 | 实例 | 现象 | 材料 |
|---|---|---|---|---|
| Permit2 | 1327 | depth 10，m/f 符号 | `x86_maps_0_0`、`x86_maps_0_1` 各约 2400s unknown | `smt2/x86_maps_0_{0,1}_*.smt2`、`route_traces/` |
| Permit2 | 1327 | depth 10，m=192，f=128 | 88s 报 `entry predicate empty or unknown` | 需自行复现 |
| Permit2 | 4837 | depth 9，m/f 符号 | `x86_maps_12_0`、`x86_maps_14_0` 各约 2500s unknown | `smt2/x86_maps_1{2,4}_0_*.smt2`、`route_traces/` |
| Permit2 | 4837 | depth 9，m=384，f=256 | 0s 报 `entry predicate empty or unknown` | 需自行复现 |
| PoolManager | 5802 | depth 14，m/f 符号 | `model_domain_nonempty` 30s unknown，3C 的常函数见证没能覆盖 | `smt2/model_domain_nonempty_e765d561caaa.smt2` |

- 路线剖析：用 `tools/route_trace.py` 在 caa01b1+3C 上，每条最多 1800s。在 1327 和 4837 上**所有路线都失败**，没有一条能证出。
  - 1327 的时间主要耗在 blast、potential、exact、bvabs、unify。
  - 4837 的时间主要耗在 unify：其中 `unsat_core` 探针 563 次 unknown，`_refute_by_cases` 约 280 次 miss。
  - 汇总可以用 `tools/route_summary.py cloud-inputs/r3c/route_traces --per-obligation` 查看。
- 复现方式：`PYTHONPATH=. poetry run python tools/probe_block_obligations.py cloud-inputs/r3c/fixtures/Permit2 <nodes.json> --output out.json --timeout-ms 30000 --node-seconds 3600 --keep-going --formula-dir /tmp/f`（PoolManager 同理）。

## 要做的
1. **"entry predicate empty or unknown"**（1327、4837 的具体实例）：找到抛出的位置，以及对应的检查（期望 sat 的入口非空检查）。判断它是确实不可满足（入口关系与具体参数矛盾，也就是发现阶段登记了一个不可能的实例），还是求解器不完备导致的 unknown；如果是后者，查明为什么 3C 的常函数见证没有生效。
2. **5802 `model_domain_nonempty`**：同样判断是可满足还是不可满足。可满足就构造并验证模型，找出现有见证路由失败的原因，再给出通用的补充。
3. **1327、4837 的 x86_maps**：先确认义务本身是否成立。用模型或具体值试探：如果找到反例，就要按照 PoolManager 那次的做法，用具体执行确认是不是编译器问题。如果成立，按项目的方法论先做同形比较，找出两侧写法的差异或卡住的子项，给出通用修法（规范化、组合证明、分情况、弱化等），并附健全性论证。
4. 每个修法都要在本任务给出的 SMT2 上离线验证，并对已证义务做回归（至少抽查若干已证块的 SMT2，或跑相关单元测试）；补单元测试；跑全量快测（目标 0 失败）。
5. 交付：推送分支（任务书建议用 `cloud/unknown-blocks`；如果会话只允许推送 `claude/...` 分支，就推送到那里，并在报告第一行写明分支名）。报告写在 `cloud-inputs/reports/unknown-blocks.md`：结论表（每个块：根因、修法、修法前后耗时）、改动位置、健全性论证、测试结果。
