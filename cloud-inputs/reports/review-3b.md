# 任务 C：批次 3B 合入前的独立健全性审查（review-3b）

审查对象：`cloud/b3b-merged`（be4dfc7，候选 r37d）相对 `cloud/inputs-5377`（a84f7d4）的全部代码改动，不含 `cloud-inputs/`。范围是 10 个文件，+702/−40 行：P1–P6 提速，加上轻前提反驳修法。

交付分支：`cloud/review-3b`，基于 be4dfc7，共 3 个提交：

1. `883b97a` fix：`_prove_equal` 的缓存条目持有 AST 引用（**必须修**，附回归测试）；
2. `0093f7d` test：其余疑点的随机化实测（确认无问题）；
3. 本报告。

## 结论

| 级别 | 项 | 说明 |
|---|---|---|
| **必须修（已修）** | 轻前提修法：`_prove_equal` 的引理缓存，键和合取项集合都是 AST id | 缓存的生命周期比产生这些 id 的公式长。轻前提路线存进缓存的只有 id，它的证明是 simplify 之后的新式子，不持有原来的 x、y 和合取项。这些项被回收后，Z3 会把它们的 id 分配给新项，于是一个无关的 (x′, y′, premise′) 可能命中旧条目，`_prove_equal` 就会返回"premise′ ⊨ x′ = y′"的假证明。后果是错误合并，进而产生错误 UNSAT。已用最小例子确定性复现（见 §1） |
| 建议修（未改） | correspondence 的 PrefixSolver 走 `_bounded_check`，墙钟上限是预算的 10 倍 | 原来的墙钟 timeout 等于预算。现在 rlimit 先到时没有影响；rlimit 没到时，单行最多可能超出节点 deadline 约 9×3s。只影响时间，不影响健全性 |
| 建议修（未改） | `_retry_with_uf_unification` 里轻前提查询用的是整条单查询预算（30s），不是 `_LIGHT_MS` | 没命中时 opaque 路线前最多多花一个单查询预算。只影响时间 |
| 无问题 | P1 PrefixSolver、P2 witness 作 SAT 证书、P3 evm_disjoint 分组、P4/P4b 映射提议、P5 coverage 先走 mul、P6 互补预检，以及轻前提修法的其他部分（去掉否定目标、deadline、预算边界） | 逐项论证和实测见 §2 |

全量快测（本分支）：1607 passed、35 failed、2 skipped。35 条失败全部是已知例外 `test_msize_absint`。审查前的候选版本在全量运行中还多 1 条 `test_offset_view_step_lemma_...` 失败；这条是 3s 墙钟预算下的偶发失败，在基线上也能复现，与本次改动无关（见 §3）。

## 1. 必须修：`_prove_equal` 缓存的 id 回收

### 问题

`verification/block_equivalence.py:1842` `_prove_equal(premise, x, y, …, cache)`：

- 缓存是 `BlockEquivalenceProver._lemma_cache`，在节点的整个生命周期里存活；pair worker 里则跨同一节点的全部义务存活（`_worker_prover`）。
- 键是 `sorted((x.get_id(), y.get_id()))`，条目是 `(合取项 id 集合, proofs)`。
- 复用条件是 `used <= 当前前提的合取项 id`。

AST id 只有在对应的 AST 存活时才唯一，Z3 会回收已释放 AST 的 id，并按 LIFO 顺序重新分配。当时的三个写入点：

| 路线 | 条目持有的引用 | 风险 |
|---|---|---|
| 轻前提（本批新增，`:1869`） | `proofs[0]` 是 `simplify(And(*light, goal))`，一个改写过的新式子，不持有 x、y，也不持有原来的合取项 | **能复现** |
| unsat_core（旧代码） | `And(*(hide(c)…), hide(differ))`：hide 为恒等时持有它们；hide 替换过 UF 应用时不持有 | 同样的隐患 |
| case tree 的成功条目（旧代码） | 查询是 hide 过的整式 | 同样的隐患 |

pair worker 里的情况更直接：每条义务都从 SMT2 重新解析，用完即释放（`_check_serialized`）。所以修复前，worker 里跨义务的缓存命中全部依赖 id 回收后恰好对上：命中可能是真的，也可能是假的。

### 复现

见 `tests/unit/test_block_lemma_cache_ids.py::test_prove_equal_cache_survives_id_recycling[light]`：

1. 第一轮：x = a+11，y = b+22，前提为 `(x == y) ∧ (p*q == w)`。轻前提路线证出 x = y，缓存条目为 `{(14, 16): [({17}, [(False, t)])]}`。
2. 第一轮的所有项都释放。
3. 第二轮按同样的分配顺序构造 x2 = a+33，y2 = b+44，前提为 `(x2 == z) ∧ (p*q == w)`。此时 `premise2 ∧ x2 ≠ y2` 为 **SAT**。
4. 修复前：x2、y2 和 `x2 == z` 拿到了被回收的 14、16、17，`_prove_equal` 返回 `[(False, 0.003)]`，也就是 x2 = y2 的假证明。记录里的查询文本是第一轮的（本身确实 UNSAT），所以**事后复查记录也看不出问题**。
5. 修复后：返回 None。

生产里发生的概率：worker 风格的 soak 实验（每次从 SMT2 解析、用完释放、共享缓存，3 个种子共 1200 次 `_prove_equal`，每个证明都用 solver 复核）在修复前后都**没有**出现假命中。这种分配模式下 id 恰好没对上，所以触发概率不高，但不为零。它属于"错误 UNSAT"方向，而且无法从记录中发现，因此定为必须修。另外，修复后 soak 里真正的缓存命中反而更多（证明数 191/184/202，修复前 172/146/178），因为兄弟义务里相同的项现在能 hash-cons 到同一个存活 AST 上。

### 修复（`883b97a`，`verification/block_equivalence.py:1842-1889`）

缓存条目改成三元组 `(id 集合, proofs, alive)`，做法与 `common/store_forwarding.py` 的 `_put` 相同：

- 轻前提的成功条目：`alive = (x, y, *保留的合取项)`；
- unsat_core 的成功条目：`alive = (x, y, *core 合取项)`；
- case tree 的成功条目：`alive = (x, y, *全部合取项)`；
- 失败条目：`alive = ()`。失败条目误命中只会返回 None（miss），不影响健全性，没必要持有引用。

健全性论证：条目存活期间 x、y 也存活，所以键里的 id 只能指向同一对 (x, y)；集合里的每个 id 也只能指向同一个合取项。`used ⊆ conjuncts(P′)` 因此就是语义上的"P′ 包含条目当时用到的全部合取项"，于是 P′ ⊨ ∧used，而 ∧used ∧ x≠y 已被反驳。内存开销：每个成功条目多持有若干已有 AST 的引用，生命周期限于一个节点（或一个 worker 的一个节点）。

测试（`tests/unit/test_block_lemma_cache_ids.py`，6 条，都已按节点 ID 单独跑过）：

- `test_prove_equal_cache_survives_id_recycling[light|core|core_uf]`：复现场景，修复后必须返回 None；
- `test_prove_equal_cache_entries_keep_their_ids_alive[light|core|cases]`：不变式检查，每个成功条目的键和 id 集合都 ⊆ 它持有的 AST 的 id。

变异测试：

- 退回 be4dfc7 的 `_prove_equal`：4 条失败，其中 `[light]` 复现场景返回 `[(False, …)]`；
- 只把轻前提条目的 alive 改成 `()`：复现场景 `[light]` 失败。

`tests/unit/test_block_light_premise.py` 的一处解包从二元组改成三元组，逻辑不变。

## 2. 逐项审查（确认无问题）

实测都在 `tests/unit/test_block_review_3b.py`（6 条，随机化，以不限时的 solver 作为基准）。另有一次性脚本放在会话 scratch 目录，不提交。

### P1 PrefixSolver（`x86_64/cfg_state.py:55-99`、`:197-211`；`x86_64/cfg_executor.py:119,181`；`block_equivalence.py:2884,2898`）

- **作用域与栈一致**：check 前比对 `num_scopes() == len(stack)`，同步过程中出现任何异常都 reset（b3b-port 加的加固）。逐行检查：
  - pop 和 `del stack[...]` 之间出异常：被 try 捕获，reset；
  - push 和 append 之间出异常：被 try 捕获，reset；
  - append 和 add 之间出异常：少一条断言只会弱化（SAT 方向），而且同样被捕获，reset；
  - `solver.check()` 本身被取消、超时或中断：作用域不变，与栈一致。
- **rlimit 和 timeout**：实测 rlimit 按每次 check 计（相对值）。200 次各 1ms 预算的 check 之后，`[u==1, u==2]` 用 1ms 预算仍然判出 unsat。rlimit 或 timeout 用尽只会返回 unknown，而 unknown 不剪枝。`_bounded_check` 设置的参数会一直留在 solver 上，但每次 check 前都会重新设置。
- **取消后的正确性**：`test_prefix_solver_never_wrong_unsat_with_budgets_that_cancel_checks` 用 120 步 DFS 式序列，预算在 1–50ms（rlimit）之间随机取，sat、unsat、unknown 三种结果都出现了。每个 unsat 都用不限时的新 solver 复核，每个 sat 模型都核对它满足全部合取项，并检查作用域数始终等于路径长度。另外用脚本跑了 4 个种子 × 300 步：约 860 个 unsat 全部复核通过，约 230 次取消，0 个错误。
- **witness**：`self._witness = prefix_solver.solver.model()`，只在 sat 时取。实测模型在之后的 pop 和 push 之后仍然可以正确 eval。witness 只用在三处：可达性的"跳过 solver、保留路径"（保留方向）、P2（SAT 证书）、P4（提议）。都不会产生 UNSAT。
- **共享**：每个 `X86SymbolicExecutor` 有自己的 PrefixSolver（`cfg_executor.py:119`），summary 重放会新建执行器，correspondence 每次调用也新建一个。pair pool 用的是 `spawn` 进程，不共享 Z3 状态。没有线程会共用执行器（`equivalence_storage` 的 ThreadPool 属于旧的 paths 流水线，不经过这里）。
- **id 比较**：`stack` 持有这些 AST，调用方也持有当前的 `conjuncts`，所以前缀比较时的 id 不会被回收。

### P2 witness 作为 SAT 证书（`verification/block_summaries.py:924-937`）

- **方向**：`entry` 的期望结果是 sat，判为 sat 的后果是"继续验证 summary"，而 summary 的全部效果义务（UNSAT）照常求解。判错（假 sat）也只会走 summary 的完整验证，不会跳过 `dead_hit` 的 UNSAT 证明，更不会把哪个 UNSAT 判错。所以 P2 本身不可能产生错误 UNSAT。
- **eval 本身**：`test_model_eval_is_never_literally_true_for_unsat_premises` 覆盖了 Exists、ForAll、lambda 上的 select、模型里没有的数组（completion）、外延等式、除以零和模零、同一个未赋值符号出现两次等情况，没有一个 UNSAT 式子被 eval 成字面 True。无法化简的量词会原样保留（例如 `ForAll(e_y, e_y == 1)`），于是算作 miss。model_completion 会改写模型，但改写后仍是同一个全赋值；实测多次 eval 结果一致。

### P3 evm_disjoint 分组（`block_equivalence.py:2195-2225`、`:2847-2877`）

- **子合取**：`test_disjoint_groups_formulas_are_sub_conjunctions_on_random_trees` 生成 40 棵随机 DFS 树。断言如下：
  - 每一对恰好落在一个组里；
  - 组公式的合取项（按 id）⊆ 组内每一对的 `premise ∧ e_i ∧ e_k`；
  - 组公式 UNSAT 时，组内每一对都 UNSAT；
  - 实测中确实出现了多对共享的组和被反驳的组。
- **分组键**：`(前缀 id 元组, a_L.id, b_L.id)`。`paths` 在函数内持有全部条件，id 不会被回收。键相同就说明前缀和两条边是同一组 AST，所以第一对构造出的公式对组内每一对都是子合取。
- **记录名与覆盖范围**：串行和 worker 两种 `_check_all` 都是先 `records.append(record)` 再 yield，所以 `trial[-1]` 就是当前组的记录。回退时用的是独立的 `sub` 列表。
  - 判定是否已证，依据的是 yield 出来的 `proved`，不是记录。万一记录对错了组，`complete` 只会因为 answer 或 lemma 不符而失败，不会多出证明。
  - 只要有一对证不出，就返回 `()`，而且不写任何记录：records 只在循环全部通过后才 extend。
- **前缀对**：组公式就是 `full(i, k)`（hash-cons 后 `.eq` 成立），证不出就直接按 overlap 处理，与 base 一致。

### P4 / P4b 映射提议（`block_equivalence.py:2879-2905`；`loop_induction.py:356-358,538,557`）

- witness 命中和增量 solver 的结果都只决定 `correspondence[j]`。之后的义务清单由 `obligation_manifest` 和 `pair_obligation_names` 从结果推出：
  - 整数映射需要 `x86_maps_j_k`（arity 来自 EVM 条件本身）、`pair_s_j` 和全部 `evm_disjoint`；
  - None 需要 `x86_empty_j`；
  - "all" 需要整行 pair。
- `complete` 要求 `names == required`，并且全部 proved。提议错了只会让某条义务证不出（`_pair_phase` 会降级重证），没有任何分支能跳过义务。
- `SegmentPath.witness` 设了 `compare=False`，`paths_digest` 也不包含它，所以不影响任何缓存键。

### P5 coverage 先走 mul（`block_equivalence.py:3419-3432`）

- `_retry_over_nonlinear_mul(coverage, "unknown")` 的 split 为 False，lemmas 恒为 `()`，所以丢掉第三个返回值不会漏掉任何待检引理。
- 只有返回 "unsat" 才采用：抽象加上 `mul_truncation_axioms`（对 bvmul 成立）只会增加模型。
- `functions` 按（位宽, 元数）为每次调用新建 UF，不涉及 id。

### P6 互补预检（`x86_64/summaries/base.py:13-41`；`memgas.py:262`；`block_summaries.py:851-856`）

- `.eq` 是 hash-cons 之后的结构相等。两次 simplify 用的是同一组默认参数（仓库里没有 `set_param`）。simplify 保持等价，所以 goal ≡ ¬c。
- `test_complement_refutation_agrees_with_the_solver_on_random_terms` 用 150 个随机项，覆盖 udiv/urem（含除以零）、移位和 ite。每次命中都用 solver 复核 `cs ∧ goal` UNSAT，全部通过。
- **调用前提**：
  - memgas 预检的是 `path ∧ ¬goal`，是实际查询 `assumptions ∧ path ∧ ¬goal` 的子合取；
  - `_solve` 只在 `expected == "unsat"` 且公式是 And 时使用；
  - generic 模式的 lemma 语句也经过 `_solve`，而判 UNSAT 对语句本身成立，所以存进 proof_cache 的 statement 证明仍然有效。
- **RECENT 窗口（16）**：只决定在哪些合取项里找互补项，影响命中率，与健全性无关。

### 轻前提修法的其余部分

- **`_refute_over_light_premise`**：去掉合取项只会弱化公式。`test_light_premise_proofs_are_sound_on_random_conjunctions` 用 120 组随机合取式，包含乘积、UF 应用和取反项，goal 取 `True`（与 `_retry_with_uf_unification` 一样）。每次命中都核对整式确实 UNSAT，且保留集合 ⊆ 原合取项。
- **`_prove_equal` 只对 goal 做 hide**：`FreshConst` 在当前上下文中是全新的，所以任何 light ∧ differ 的模型令 k := t 后，都是 light ∧ hide(differ) 的模型。UNSAT 能传回。
- **`_retry_with_uf_unification` 去掉"否定目标"之后（`:3104-3115`）**：
  - 如果被去掉的是 ¬goal（它带有参数的 UF 应用，比如 host 结果或乘法抽象的 UF），剩下的反驳说明 unify 之后的前提本身 UNSAT，原义务因此空真成立。UNSAT 仍然可靠。
  - 记录里是 `opaque_array_uf_light`，前面的 unify 引理也都带上了，`Obligation.proved` 要求全部引理都是 unsat。
  - 即使这个函数用在期望 sat 的义务上，"unsat" 也只会让结果与期望不符，不会被当成证明。
- **deadline 和预算边界**：
  - `_prove_equal`：`light_ms = min(budget, 2000, 剩余 deadline)`，≤0 直接返回 None。注意 Z3 的 timeout=0 表示不限时，所以这个检查必须有。
  - `_retry_with_uf_unification`：light 的预算在 `started` 时刻按 deadline 截断；之后的 opaque 查询按 deadline 重新截断，并要求 `budget > 0`。
  - 没有任何路径会把 timeout=0 传给 Z3。

## 3. 测试结果

命令：`PYTHONPATH=. poetry run pytest tests/unit -q -m "not slow" -p no:cacheprovider -n 3 -rf`（3 进程并行）。没有加 `-x`，因为加了会停在第一个 msize_absint 已知失败上。

- **审查前（be4dfc7，候选 r37d）**：1594 passed、36 failed、2 skipped，593s。其中 35 条是 `test_msize_absint`（已知例外，`ModuleNotFoundError: prov_common`），另 1 条是 `test_block_uf_unification.py::test_offset_view_step_lemma_proves_the_rewrite_without_per_read_queries`。
- **审查后（本分支 0093f7d）**：**1607 passed、35 failed、2 skipped**，555s。35 条失败全部是 `test_msize_absint`（已知例外），除此之外没有失败。比审查前多出的 13 条 passed 是新增的 12 条测试，加上这次没有失败的 `test_offset_view_step_lemma_...`。
- **`test_offset_view_step_lemma_...` 是偶发失败**：测试自己的 `answer()` 用 3s 墙钟 timeout 直接求解，结果是 `unknown == unsat`。在本机单独重跑：
  - 基线 a84f7d4：4 次中 1 次失败；
  - be4dfc7：1 次，失败；
  - 本分支：5 次中 1 次失败；在上面的全量并行运行中通过。
  
  失败与代码版本无关，是 3s 墙钟预算处在临界点上。b3b-port 的报告里也记录过同样的现象。
- **新测试**：都按节点 ID 单独跑过（`-v`），都被收集到，没有同名覆盖：
  - `test_block_lemma_cache_ids.py` 6 条；
  - `test_block_review_3b.py` 6 条；
  - `test_block_light_premise.py` 7 条（未改逻辑）。

## 4. 离线验证数据

本次是审查任务，没有重跑 5377 的义务。修复只改变 `_prove_equal` 缓存的命中条件：修复前靠 id 回收"碰巧命中"的条目，现在只在 AST 真正相同时才命中；修复前合法的命中（项存活、id 相同）不受影响。worker 风格 soak（§1）显示修复后真正的命中更多。这可能让 pair worker 里兄弟义务的耗时略有变化，需要服务器全量重跑 r37d+本修复来确认 5377 两个上下文的结果。

## 5. 未解决的问题和建议

1. **建议**：correspondence 的 `prefix.check(..., budget, "correspondence")` 改用独立的墙钟 timeout（等于 budget），不要沿用可达性的 10 倍安全系数，以免在临近节点 deadline 时多跑一行。
2. **建议**：`_retry_with_uf_unification` 的轻前提查询可以和 `_prove_equal` 一样封顶在 `_LIGHT_MS`（或者设一个单独的上限），减少没命中时的开销。pair58-fix 报告提到过 pair_52_16、pair_67_9 因探针而变慢。
3. **观察**：仓库里还有其他以 `get_id()` 为键、生命周期比较长的缓存，例如 `state_digest` 的 `expression_cache`（键是 `(id(ctx), id)`），不在本次 diff 内。粗看都是单次遍历内使用、项都存活，没有发现问题，但没有逐一审查。
4. **需要服务器验证**：5377 a、b 两个上下文在本分支上的全量结果。
