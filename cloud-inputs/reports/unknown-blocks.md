分支：`claude/unknown-blocks-37upmv`（会话只允许推送 `claude/...` 分支，未使用任务书建议的 `cloud/unknown-blocks`）。基线 = `cloud/inputs-r3c`（60d55f9）。

# 任务 L：Permit2 / PoolManager 剩余 unknown 块 —— 根因与通用修法

## 1. 结论

五个现象全部定位到根因，都不是 SAT，也都不是编译器问题。四处通用修法全部只改 Python 端，没有按合约或块号特化：

| 合约 | 块 / 实例 | 失败义务 | 根因 | 修法 | 修法前 | 修法后（本机） |
|---|---|---|---|---|---|---|
| Permit2 | 1327 d10，m=192 f=128 | `entry_nonempty` | **环境问题，不是空入口**。入口前提可满足，新进程里 0.019s 就是 sat。所有 msize 为具体值的实例，入口前提 `simplify` 后**完全相同**（`(m&31)==0`、`m<=…` 都化成 true），alpha 摘要也一样。服务器上这一条 67s 超时，结果被 proof_cache 记成 `{"unknown":30000}` | SAT 期望的检查不再信任缓存里的 unknown（修法 A） | 67s unknown，节点 88s 就中止 | entry 0.019s sat；整节点见 §5 |
| Permit2 | 4837 d9，m=384 f=256 | `entry_nonempty` | 同上：0s 的 unknown 只可能来自缓存命中。它正好排在 1327 m=192 之后，命中的是同一条记录 | 修法 A | 0s unknown | **整节点 proved，256s** |
| PoolManager | 5802 d14 | `model_domain_nonempty` | **可满足**。3C 的常函数见证只限制"带数组参数的 UF"，而这里没有这类 UF：`sha3_bytes_58` 的参数是位向量，即经 R15 偏移视图 `λa.M[a-R15]` 读出的字节拼接。lambda 藏在位向量参数里，Z3 照样不完备 | 见证改为三档：数组参数 UF → 参数含绑定子的 UF → 全部 UF（修法 B） | 30s unknown | 0.28s sat（已验证模型） |
| Permit2 | 4837 d9 符号 | `x86_maps_12_0`、`x86_maps_14_0` | **义务成立**。EVM 侧是 256 位 `SHL`（`Concat(z3..z0) << Concat(s3..s0)`），x86 侧是按 limb 移位：`(x_k<<r)\|(x_{k-1}>>(-r mod 64))`，limb 下标由区间比较决定。256 位桶形移位器和 64 位的逐位对比，位爆破跑不动；把 s 代入具体值后，两边都是常量移位，每个值约 0.1s | 新路线 `shift`：对移位量常量逐值分情况（修法 C） | 2635s / 2441s unknown，节点 6100s inconclusive | 23.9s / 13.7s proved；**整节点 proved，259s** |
| Permit2 | 1327 d10 符号 | `x86_maps_0_0`、`x86_maps_0_1` | **义务成立**。两侧各有一条三层嵌套的 `sha3_slice` 链（keccak 写回内存再 keccak）。逐层合并参数都能在 <1s 内证出，合并后 blast 路线 73s 证出。卡点在 unify 路线的调度：① 按大小排序时，跨层的 pair（L1 对 L2 等）排在 L3 前面，每个都要耗满 30s 才失败；② 合并完成后，还要把约 35 个永远合不上的 host-gas 参数 pair 试完，才会做后续尝试，路线份额（约 445s）就此耗尽 | unify 先试嵌套层数相同的 pair；每次合并内存参数后，用 quick 预算立即试一次 opaque/blasted 查询，成功就停止合并（修法 D） | 2462s / 2291s unknown，节点 7269s inconclusive | **812s / 840s proved**；整节点见 §5 |

补充：1327 符号实例在 x86 侧还有第二个 L3 `sha3_slice`，它只出现在两条 host-gas 上界公理（`ULE(host_gas_*(…), 22100)`）里。这两条是别的路径带进来的"死公理"，与目标无关；它和 EVM L3 的相等性证不出（120s FAILED），这不影响结论。

## 2. 改动位置

全部在 `verification/block_equivalence.py`：

- **修法 A：SAT 期望的检查不信任缓存的 unknown**
  - `solve_query(..., trust_unknown=True)`：L81–L96。`trust_unknown=False` 时，缓存里的 `{"unknown": N}` 不再直接返回，而是重新求解；缓存里已判定的 sat/unsat 照常使用。
  - `_check` 在 `expected == "sat"` 时以 `trust_unknown=False` 调用：L3161–L3162。
  - 诊断工具 `tools/entry_cache_probe.py`（新增）：输出某个节点的 entry 查询在服务器缓存里的记录，以及新进程求解的结果，可用来直接确认根因（见 §7）。
- **修法 B：常函数见证分档**
  - `_binder_argument_ufs`：L143；`_all_ufs`：L176；`_witness_tiers`：L196；`sat_by_constant_array_ufs`：L212（逐档尝试，预算均分）。
  - `_check` 给见证的总预算从 `_QUICK_EXACT_MS` 提高到 `3 * _QUICK_EXACT_MS`，三档平分后，每档仍有原来一档的 3s：L3154。
- **修法 C：移位量分情况 `shift_split`**
  - `_SHIFT_MAX_CASES = 64`、`_scalar_constants`、`_shift_amount_constants`、`_small_conjuncts`、`_refuted`、`_shift_bounds`、`shift_split`：L1605–L1749。
  - 路线表加入 `("shift", False)`，位于 `("quick", True)` 之后、`blast` 之前：L3025、L3028。
  - 路线分支 L3109–L3119：不适用时立即返回；适用时取剩余时间的一半。另在 L3139 加了一行：只有 `shift` 路线报 sat 时才停止（这里的 sat 是 F 的真模型；其他路线的 sat 可能来自抽象，仍照旧往下试）。
- **修法 D：unify 调度**
  - `_uf_nesting`：L2391；`unify_uf_arguments` 的排序键改为 `(层差>0, 大小)`，新增 `on_merge` 回调：L2408–L2469。
  - `_after_unification`（从 `_retry_with_uf_unification` 抽出原有的 opaque 尝试，并新增 blasted 尝试）：L3571；`_retry_with_uf_unification` 中，内存（lambda）参数每合并一次就探测一次：L3616–L3645。
- 测试：`tests/unit/test_block_unknown_blocks.py`（新增，17 条）。

## 3. 健全性论证

- **A**：只决定缓存里的 unknown 要不要重新求解。答案仍由 Z3 给出，或取缓存中已判定的 sat/unsat。unknown 本来就不证明任何东西，所以这项改动既不会产生 UNSAT，也不会产生 SAT。受影响的只有 SAT 期望的检查（`entry_nonempty`、`model_domain_nonempty`、block_program 的 `init/model_domain_nonempty`），而且只多花求解时间。
- **B**：代换引理对任意一组 UF 都成立。设 F' = F[f_i := c_i]，c_i 是新常量。若 M' ⊨ F'，令 f_i 解释为恒取 M'(c_i) 的常函数，M' 扩展后就满足 F，因为 F 中每次 f_i 的应用都取值 M'(c_i)，F' 正是这样构造的。前提条件是 f_i 不能被当作值引用（`Map`/`as-array`）：`_array_argument_ufs` 遇到这种情况返回 None，`_witness_tiers` 随即返回 []，不做任何尝试。只有 `model.eval(F', model_completion=True)` 字面为 True 才报 sat；F' 为 UNSAT 时报 unknown，因为 F 可能需要非常函数。这一点很关键：见证若误报 sat，就会把空的模型域当成非空，后面所有义务都会空洞地成立。所以 sat 必须由模型求值保证，这里确实如此。
- **C**：对每个出现在符号移位量里的常量 v，只用 F 的顶层小型纯位向量合取项 L 求界。L ⊆ F，所以 `L ∧ v<lo` 与 `L ∧ v>hi` 的反驳（记为引理）说明 F ⊨ lo ≤ v ≤ hi。二分查找的中间步骤只用来挑选界，非 UNSAT 一律当作"不是界"，界只会变宽，不会错误地变窄。lo=hi 的常量固定下来（F ≡ F ∧ v=lo）；值最少且不超过 64 个的常量逐值展开：F ≡ ∨_c (F ∧ v=c ∧ 固定项)。F ∧ v=c ∧ … 的模型恰好是 F[v:=c, …] 的模型再补上这些取值（等量代换，代换后 v 不再出现）。因此每个 F[…] 都 UNSAT（各自是一条 case 引理）⇔ F UNSAT。若某个情况 SAT，它的模型就是 F 的模型，报 sat；unknown 或超时则返回 None，什么也不证明。lo>hi 时 L 本身不可满足，两条界引理即可反驳 F。
- **D**：调整顺序只改变尝试次序。`on_merge` 提前停止，只是少做一些重写：已做的每次合并都有 `_prove_equal` 的反驳引理，F ⊨ F'。`_after_unification` 的 blasted 目标是 `simplify(F', blast_select_store=True)`，Z3 的化简保持等价，与现有的 `blast` 路线相同。它反驳的是 F'，引理链与原有的 opaque 尝试一致。
- 不存在"提议"类信息出错就导致误证的通道：分情况的变量、界、合并顺序都只是提议，所有结论都落到被反驳的查询上。

## 4. 测试结果

- 新增 `tests/unit/test_block_unknown_blocks.py`，17 条，逐个按节点 ID 单独运行，全部 1 passed，确认都被收集到。单独运行时曾发现 `test_shift_split_empty_bounds_refute` 依赖其他测试填充 `_DECLS`，已改为在模块级填充。
  - 修法 A：用伪造的超时污染缓存，复现服务器现象；再证明 alpha 等价的另一个实例的 `entry_nonempty` 现在是 sat；同时确认已判定的缓存答案仍被信任。
  - 修法 B：lambda 位于位向量参数中时能被限制；分档顺序正确；UNSAT 或需要非常函数时不报 sat；5802 的 SMT2 能证出。
  - 修法 C：limb 移位与 256 位 SHL 的合成义务（63 个 case，所有引理从文本重解均为 unsat）；构造真反例时报 sat，`_check` 记录为 sat，不算证出；界过大时不展开；空界时反驳；4837 14_0 的 SMT2。
  - 修法 D：三层链中同层 pair 先试（已确认旧的按大小排序会先试跨层 pair，测试能区分新旧行为）；`on_merge` 能停止合并；内存合并后用 quick 预算探测；纯位向量合并不触发探测。
- 全量快测 `pytest tests/unit -m "not slow" -p no:cacheprovider`：**1732 passed, 3 skipped, 0 failed**（基线为 1715 passed + 新增 17 条）。
- `test_block_uf_unification.py` 中两条 `slow` 用例（Safe 9733 / 11803）缺数据文件 `tests/data/block_obligations/*.smt2`，报 `file access error`。在基线 60d55f9 上也一样失败，与本次改动无关。

## 5. 离线验证数据（本机：4 核，z3 4.15.4，每查询 30s）

单条义务用 `cloud-inputs/r3c/smt2/` 中的 SMT2，按生产 `_check` 运行，每条预算 1800s，与 route_trace 一致：

| 义务 | 修法前（route_trace） | 修法后 | 获胜路线 |
|---|---|---|---|
| 5802 `model_domain_nonempty` | 30s unknown | 0.28s sat | 见证第 2 档（= 全部 UF：`host_gas_sload`、`sha3_bytes_58`、`sha3_bytes_64`） |
| 4837 `x86_maps_12_0` | 1317.6s unknown（预筛 2635s） | 23.9s proved（`shift_split` 本身 5.9s，引理 68 条） | shift |
| 4837 `x86_maps_14_0` | 预筛 2441s unknown | 13.7s proved（goal 拆为 2 部分，各由 shift 证出） | shift |
| 1327 `x86_maps_0_0` | 1454.6s unknown（预筛 2462s） | 812.1s proved | unify*（296s） |
| 1327 `x86_maps_0_1` | 1393.1s unknown（预筛 2291s） | 839.6s proved | unify*（455s） |

1327 的诊断过程：先手工逐层合并 `sha3_slice` 的参数（L1 0.3s、L2 0.5s、EVM-L3 对 x86-L3 0.3s），合并后的公式由生产 `_check` 在 72.7s 内证出，获胜路线是 blast*。由此确认义务成立，问题出在调度。

整节点（`tools/probe_block_obligations.py`，`--timeout-ms 30000 --node-seconds 7200 --keep-going`，串行，无 proof cache）：

| 节点 | 修法前（服务器预筛） | 修法后（本机） |
|---|---|---|
| Permit2 4837 d9 符号 | 6100s inconclusive（2 条 unknown） | **proved 259s**（EVM 3 条路径 / x86 31 条路径，379 个查询） |
| Permit2 4837 d9 m=384 f=256 | 0s，entry unknown | **proved 256s** |
| Permit2 1327 d10 符号 | 7269s inconclusive（2 条 unknown） | 7222s inconclusive，**0 条失败**，只是串行跑完节点预算（EVM 61 条路径 / x86 70 条路径，1895 个查询） |
| Permit2 1327 d10 m=192 f=128 | 88s，entry unknown | entry 已通过；7207s inconclusive，`x86_maps_0_0` 1476s unknown（见 §8） |
| PoolManager 5802 d14 | 98s，`model_domain_nonempty` unknown | 7258s inconclusive，**0 条失败**，只是串行跑完节点预算（EVM 55 条路径 / x86 23 条路径，1279 个查询，1060 个 terminal 已证） |

## 6. 已证义务的回归

- 4837 两个节点的全部 379 个查询都通过了。其中其他行原来就是证出的，可算作 `shift` 路线和 unify 调度改动下的回归样本。
- 全量快测 0 失败（1732 passed）。这些单元测试覆盖了 unify、路线顺序、pin、alias、potential、见证等已有路径。
- 未能回归的部分：其他合约（Safe / CErc20 等）已证块的 SMT2 不在仓库里，`tests/data/block_obligations` 也不存在。建议服务器在全量验证中重点看这两类节点的耗时：一是 unify 获胜的节点（Safe 5377、CErc20 4236），排序和每次内存合并后的 quick 探测可能改变它们的耗时；二是含符号移位的节点。

## 7. 在服务器上确认修法 A 的根因

```bash
BLOCK_PROOF_CACHE=<服务器缓存路径> PYTHONPATH=. poetry run python tools/entry_cache_probe.py \
    1327:10:192:128 4837:9:384:256
```

如果输出 `cached: {'unknown': 30000} fresh: sat`，即可确认。注意：所有 msize 为具体值的节点共用这一条记录。修法 A 之后，这条记录对 SAT 期望的检查不再生效，无需手动清理缓存。至于 1327 m=192 那次为什么花了 67s 并超时，可能是机器负载（上一个节点的 pair worker 仍在运行），也可能是 sqlite 锁等待加上更早的一条缓存记录。本机无法复现，因为新进程里只要 0.019s。

## 8. 未解决的问题

1. **Permit2 1327 m=192 f=128 的 `x86_maps_0_0`**（具体实例）仍是 1476s unknown。入口问题已修好，节点进入了 pair 阶段。这一条的公式与符号实例的不同：msize 和 fmp 是具体值，内存视图和 gas 项都会变化。我没有抓到它的 SMT2，因为 probe 只在节点结束时才写 `--formula-dir`，重跑一次又要 2 小时，所以无法断定它是同一个调度问题（预算不够），还是另有卡点。建议服务器用 `--formula-dir` 重跑这个节点，再用 `cloud-inputs/r3c/tools/route_trace.py` 剖析。
2. **整节点预算**：1327 符号实例和 5802 在本机都是串行跑（`BLOCK_PAIR_WORKERS=1`），没有任何义务失败，只是用完了 7200s 的节点预算。服务器上若用 pair worker 并行，应能跑完；否则这两个节点和 PoolManager 4418 属于同一类问题（预算，而非 unknown）。需要服务器做全量验证来确认。
3. **对其他合约的耗时影响**：unify 排序、每次内存合并后的 quick 探测，以及新加的 `shift` 路线，都可能改变其他合约已证块的耗时。健全性不受影响，但可能变快或变慢。本机没有它们的 SMT2，无法回归（见 §6）。
4. **1327 的 unify 仍然偏慢**（获胜前约 300–450s）：在 L3 合并之前，同层的 host-gas 参数 pair（约 15s/个，都会失败）排在前面。如果服务器上仍然紧张，下一步可以考虑剪掉死的 host-gas 上界公理（只出现在 `ULE(host_gas_*(…), 上界)` 中、别处不用的应用；去掉一个合取项是弱化，对 UNSAT 是健全的）。这样那批 pair 就不会出现。这一步本次没有做。
5. 修法 A 的根因（缓存里有超时记录）是推断出来的：0s 的 unknown 只能来自缓存，而所有具体 msize 的入口查询完全相同，这一点本机已复现。服务器上可用 §7 的命令直接确认。
