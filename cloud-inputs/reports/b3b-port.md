# 任务 B：P1–P6 提速转正（b3b-port）

分支 `cloud/b3b-port`，基于 `cloud/inputs-5377`（a84f7d4，父提交 = develop-cutpoint = snap-r35b）。

## 结论

1. `cloud-inputs/b3b/r37c.patch` 能干净地应用到当前代码。逐项核对 P1–P6 的实现与 `exec5377/REPORT.raw.txt` 中的健全性论证，**P2–P6 与论证一致，无需改逻辑**。
2. **P1 有一处需要修正**（已修）：`PrefixSolver` 的不变式是"第 k 个 push 作用域里恰好只有 `stack[k]`"。原实现在 `push → add → append` 之间如果抛异常（KeyboardInterrupt、Z3 异常），solver 里可能多出一条后续查询并不包含的断言，下一次 check 得到的 UNSAT 就不再是"这条路径条件 UNSAT"。这只在异常路径上发生，概率很低，但它属于"错误 UNSAT"方向，所以必须修：
   - 同步过程中任何异常都 `reset()` solver；
   - 每次 check 前核对 `num_scopes() == len(stack)`，不一致就 reset。
3. P2 的注释原写"eval 对无量词公式精确"，但 premise 里可能有 lambda 和量词。我实测了 Z3 的 model eval：它只是在一个全赋值下做等价改写，无法归约的量词会原样留下（不会变成 `True`），只有结果字面为 `True` 才采用。所以实现本身没问题，只把注释改成了准确的论证。
4. 单元测试补齐：P1 / P3 / P6 按任务要求各补了用例，共 6 个新测试，`test_block_speedups.py` 现在共 16 个，全部通过。P1 的修复做了变异测试：去掉修复后，新测试会失败。
5. r37c 实测（`server/r37c-5377/`）：
   - 到达 pair 阶段的时间，a 从 2527s 降到 365s（6.9×），b 从 2338s 降到 372s（6.3×）。
   - "all" 行从 44 / 36 降到 0 / 0。
   - EVM 路径集合完全一致（86 条）。
   - x86 路径集合**不完全一致**：opt 两个上下文都是同一组 171 条；base 的 a 是 178 条、b 是 172 条，两者只有 155 条相同。说明见第 3 节。
6. 两个上下文最后卡住的 `pair_63_10`（a）和 `pair_68_8`（b）**都不是 "all" 行产生的义务**：
   - 它们是 P4 给出映射的行（a 的第 10 行映射到 EVM 63，b 的第 8 行映射到 EVM 68）。对应的 `x86_maps_j_*` 都已证明，这就是该行唯一的 pair 义务。
   - 卡住的原因是 terminal pair 本身难证，和 correspondence 无关：同一个 `pair_63_10` 在 b 里 1139s 就证出来了，`pair_68_8` 在 a 里 1429s 证出来了。
   - 所以不存在需要通用修复的"P4 没给出映射"问题。剩下的缺口属于任务 A（pair58 的 light-premise 修法）的范围：离线重跑时，r37c 加上 A 的修法后 `pair_63_10` 801s、`pair_68_8` 976s 均证出，不加则两条都是 unknown（见第 4 节）。

## 1. 改动位置

在 r37c.patch 原样应用的基础上，额外做了以下改动：

| 文件:行 | 内容 |
|---|---|
| `x86_64/cfg_state.py:55-99` | `PrefixSolver`：新增 `reset()`；check 前核对作用域数；同步期间出现异常就 reset 后再抛出（**本任务修正**） |
| `verification/block_summaries.py:928-937` | P2 注释改成准确的论证（逻辑不变） |
| `tests/unit/test_block_speedups.py` | 新增 6 个测试（见第 5 节） |

r37c.patch 自带的改动（已核对）：

| 项 | 文件:行 |
|---|---|
| P1 | `x86_64/cfg_state.py:55`（PrefixSolver）、`:171-211`（is_possible 的增量分支）；`x86_64/cfg_executor.py:119,181` |
| P2 | `verification/block_summaries.py:898,928-937`；`x86_64/cfg_executor.py:756,848`；`x86_64/summaries/base.py`（`X86SummaryRuntime.apply` 签名） |
| P3 | `verification/block_equivalence.py:2136`（`_ordered_conjuncts`）、`:2141`（`disjoint_groups`）、`:2791-2817`（`_correspondence` 去重和回退） |
| P4 | `verification/block_equivalence.py:2818-2852`；`verification/loop_induction.py:358,538,557`（`SegmentPath.witness`） |
| P5 | `verification/block_equivalence.py:3355-3365`（`check_paths` 的 coverage） |
| P6 | `x86_64/summaries/base.py:15-41`（`refuted_by_complement`）；`x86_64/summaries/memgas.py:262`；`verification/block_summaries.py:852-856` |
| 测试 | `tests/unit/test_block_correspondence.py`（unknown 改为对 `PrefixSolver.check` 打桩） |

## 2. 健全性论证（逐项核对结果）

**总的后备保证。** 块定理只由 `BlockTheorem.complete` 判定，判定依据是一份清单：清单从路径结果推出，不从查询记录推出。另外 `x86_coverage` 会独立证明 `premise → ∨ x_j`。所以：

- 执行器错误地剪掉一条可行路径，只会让 coverage 失败，不会产生错误证明；
- correspondence 给错映射，只会让 `x86_maps` 或 `x86_empty` 失败。

下面逐项说明，每一项本身也满足要求。

### P1 增量可达性：unknown 不剪，只有 UNSAT 才剪 ✔（已加固）

- 查询时 solver 的断言集合 = `conjuncts`。pop 会撤掉该作用域的断言，以及从它推出的学习子句。因此精确查询 UNSAT ⇒ 路径条件 UNSAT。
- `result == unknown` 时，只在新建的 solver 上跑现有的 bvmul→UF 探针。抽象只会增加模型，所以探针 UNSAT ⇒ 原式 UNSAT。探针得到 SAT 或 unknown 时，`return True`，保留路径。
- 和非增量分支相比只是先后顺序不同：精确 SAT 时探针不可能 UNSAT，精确 UNSAT 时两条分支都剪。所以两者的剪枝集合只在预算内 unknown 的情况下可能不同，而且两边都是可靠的 UNSAT。
- witness 取自 sat 时的 `solver.model()`。Z3 的 model 对象独立于之后的 pop，仅用于后续"跳过 solver"（保留方向）和提议。
- **修正**：见结论第 2 条。异常安全加上作用域数核对之后，"断言集合 = conjuncts"在任何执行路径下都成立。`stack` 持有这些 AST 的引用，保证 AST id 不会被复用。
- 确定性：rlimit 预算不变，并且 Z3 的 rlimit 是相对于当前计数的增量；查询顺序由执行器决定。增量 solver 的强弱依赖历史，但历史本身是确定的。

### P2 entry 用路径模型回答：模型只作为 SAT 证书 ✔

- 只在 `expected == "sat"` 的 entry 检查上使用，而且只有 `witness.eval(premise, model_completion=True)` 字面为 `True` 时才采用。
- 这等于给出了 premise 的一个满足赋值。model_completion 会给未出现的符号补默认值，所以它是一个全赋值。
- 实测（脚本见附录）：`ForAll y. x>y` 在 x=5 下 eval 后仍是量词，不会变成 True；lambda 的 select 和外延等式能正确化简。也就是说，不会出现"假的 True"。
- miss（不满足或 eval 不出来）时走原来的 `check("entry", premise, "sat")`；generic 模式不走这条。

### P3 evm_disjoint 去重：只用子合取式证 UNSAT ✔

- 路径条件是 `And(按执行顺序排列的合取项)`。对 (i, k)，设首个分歧位置为 L，则 `premise ∧ prefix_L ∧ a_L ∧ b_L` 的每个合取项都是 `premise ∧ e_i ∧ e_k` 的合取项（`prefix_L` 两边逐项 `.eq`）。
- 互补情形只用 `a ∧ b`，也是子合取。子合取 UNSAT ⇒ 原式 UNSAT。
- 如果一条路径是另一条的前缀，保留原式。组证不出时，对组内每一对用原式重证；只要有一对证不出，就按 overlap 返回 `()`（与 base 相同）。
- 记录：每个组只调一次 `_check`，`_check` 恰好追加一条记录，所以 `trial[-1]` 就是这个组的记录（`_proved_trials` 也是这种用法）。然后对组里每一对用 `replace(record, name=...)` 生成一条记录，并按清单顺序 extend。
- `complete` 只看名字、答案和 lemma；`slim` 也说明了"No consumer reads the text"。这与现有的 `x86_maps_group_n → x86_maps_j_k` 做法相同。
- 并行（BLOCK_PAIR_WORKERS>1）下 `_check_all` 保持输入顺序，回退时嵌套的 `_check_all` 在失败时由外层 finally 回收进程池。

### P4 映射：只是提议 ✔

- 执行器 witness 和增量 solver 的结果都只决定 `correspondence[j]`。
- 整数映射要求 `x86_maps_j_k`（每个合取项）+ `pair_s_j` + 全部 `evm_disjoint` 都证明；`None` 要求 `x86_empty_j`；"all" 要求整行 pair。这些都由 `pair_obligation_names` 和 `_pairs_covered` 检查。
- 提议错了，只会让对应义务失败（`_pair_phase` 会把该行降级为 "all" 后重证），不会产生证明。
- correspondence 的增量 solver 改用 rlimit 预算（`_bounded_check`）。这只影响提议质量，与健全性无关。

### P5 coverage 先走 mul：只调整路由顺序 ✔

- `_retry_over_nonlinear_mul(coverage, "unknown")` 就是 `_check` 级联里已有的 ("mul", False) 路线：abstraction 加上 `mul_truncation_axioms`（对 bvmul 成立），只会增加模型。
- 只有 `answer == "unsat"` 时才记为证明，记录里的公式是抽象后的公式（与 `_check` 的 mul 路线一致）。miss 时原样进入 `_check`。
- budget ≤ 0 时直接返回 unknown，再由 `_check` 抛出 ProofBudgetExceeded。

### P6 互补预检：只在 simplify 结果互补时判 UNSAT ✔

- `simplify` 保持等价。`simplify(goal)` 为 false ⇒ goal 不可满足；`simplify(goal).eq(simplify(Not(c)))` ⇒ goal ≡ ¬c，于是 c ∧ goal ≡ false。c 是 premise 的顶层合取项（嵌套的 And 已展开，取最后 16 个）。
- 三个使用点：
  - `memgas._require_implied`：要证 `assumptions ∧ path ∧ ¬goal` UNSAT，预检的是 `path ∧ ¬goal`，是它的子合取；
  - `VerifiedSummaryRuntime._solve`：`expected=="unsat"` 且公式为 `And(c1..cn)`，取 `premise = And(c1..cn-1)`、`goal = cn`；
  - generic 模式的 `_discharge` 也经过 `_solve`。
- 每处都是"判为 UNSAT ⇒ 原式 UNSAT"；返回 False 时，原来的查询一字不改。

## 3. r37c 实测汇总（`cloud-inputs/server/r37c-5377/`）

opt = r37c（snap-r35b + P1–P6），`stage-*`；base = snap-r35b，`base-*`。base 在 `_pair_phase` 入口停止（STAGE_STOP）。

配置：`BLOCK_PAIR_WORKERS=3`、`--timeout-ms 30000`、`--node-seconds 10800`、`PYTHONHASHSEED=0`，全新 cache。

### 表 1 分阶段耗时（墙钟 s，括号内为 CPU s）

| 阶段 | a: base | a: opt | a 倍数 | b: base | b: opt | b 倍数 |
|---|---|---|---|---|---|---|
| EVM 段 | 0.8 | 0.7 | – | 0.7 | 0.7 | – |
| x86 段 | 1517.5 (1514.9) | 293.9 (293.7) | 5.2× | 1456.6 (1449.2) | 293.4 (293.1) | 5.0× |
| 　其中可达性检查：次数 / 墙钟 / 剪枝 | 2235 / 859.4 / 814 | 2099 / 161.1 / 756 | 5.3× | 2122 / 842.4 / 766 | 2097 / 161.3 / 756 | 5.2× |
| check_paths 合计 | 446.3 (444.3) | 15.9 (15.9) | 28× | 398.1 (396.2) | 22.4 (22.4) | 18× |
| 　x86_coverage | 439.5 | 14.3 | 31× | 395.6 | 21.0 | 19× |
| 　evm_coverage | 6.0 | 1.6 | – | 2.5 | 1.4 | – |
| _correspondence | 528.5 (520.9) | 20.9 (20.4) | 25× | 448.9 (437.6) | 23.7 (23.0) | 19× |
| **到达 pair 阶段** | **2527.2** | **364.8** | **6.9×** | **2337.7** | **372.4** | **6.3×** |
| _pair_phase | 未跑 | 7741.4 (主进程 CPU 1991.7)，以异常结束 | – | 未跑 | 7362.8 (主进程 CPU 2069.3)，以异常结束 | – |
| 节点结论 | – | inconclusive：`pair_63_10` unknown 2988s | | – | inconclusive：`pair_68_8` unknown 3486s | |

说明：

- 可达性次数和剪枝数是各执行器（含 summary 重放）的合计。
- x86 段中可达性以外的部分（summary apply 等），a 从 658s 降到 133s，b 从 614s 降到 132s。
- pair 阶段主进程 CPU 远低于墙钟，因为 pair 义务在 3 个 worker 进程里跑。

### 表 2 correspondence 行数与路径集合

| | a: base | a: opt | b: base | b: opt |
|---|---|---|---|---|
| x86 路径 | 178 | 171 | 172 | 171 |
| EVM 路径 | 86 | 86 | 86 | 86 |
| correspondence 行：mapped / empty / **all** | 133 / 1 / **44** | 170 / 1 / **0** | 134 / 2 / **36** | 170 / 1 / **0** |
| "all" 行带来的 pair 义务数（all × 86） | 3784 | 0 | 3096 | 0 |
| 实际捕获的 pair_* 义务 | – | 19 | – | 17 |

路径集合比对用规范结构哈希（`canon_hash`，对 AC 参数顺序不敏感，并掩掉进程相关编号）：

- **EVM**：四次运行的 86 条完全相同。
- **x86，opt 与 base**：
  - a：共同 159 条，仅 opt 有 12 条，仅 base 有 19 条；
  - b：共同 165 条，仅 opt 有 6 条，仅 base 有 7 条。
  - 差异都落在相同的 (kind, location) 上：exit@176058 和若干 terminal@28xxxx。b 的 base 多一条 terminal@288039。
- **跨上下文**：
  - opt 的 a 与 b 是**同一组 171 个哈希**，同时说明 opt 在两个上下文上逐条一致；
  - base 的 a(178) 与 b(172) 只有 155 条相同。
  - 四次运行的并集：155 条四次都有；169/171 条 opt 哈希在至少一次 base 中出现；只有 2 条是 opt 独有的。

**解读**（推断，手头只有哈希，没有条件本身，无法逐条做 Xor 等价检查）：

- base 的 x86 路径分解在两个上下文之间并不稳定。可达性用的是确定性 rlimit，但 summary 的 entry（30s `solve_query`）和 memgas exit-guard（`_require_implied` 的墙钟 timeout）是墙钟预算。负载一高，这些检查超时，就退回 raw 执行，于是同一位置被切成不同的路径。
- P2/P6 把这两类检查换成了精确证书（模型或语法互补），所以 opt 不再受这个噪声影响，两个上下文的分解完全相同。
- base 多出来的路径还有一部分来自 unknown 未剪的不可行路径：剪枝 a 814 对 756，但 base 的检查次数也更多。
- 无论哪种情况，健全性都由各自运行里的 `x86_coverage` 兜底（两边都证明了），不依赖两次运行的路径集合一致。exec5377 报告里"路径集合相同"那条结论是在 r34h 上、单一负载条件下得出的，在 r37c 的这两次运行里**不成立**。不过差异在 base 一侧本身就有（a 与 b 之间），不是 P1–P6 引入的不健全。

### 卡住的义务是不是 "all" 行？——不是

- `smt2-a/answers.txt`：x86 第 10 行有 `x86_maps_10_{7,8,16,24,25,32,40,48}` 全部 unsat（其余合取项由 prefix discharge 证明，不经过 `_check`，所以没有捕获），pair 义务只有 `pair_63_10` 一条。已尝试的每个 x86 行都恰好只有一条 pair 义务（a 19 条，覆盖行 0–19，其中第 18 行为 empty；b 17 条，覆盖行 0–17，其中第 16 行为 empty），没有任何一行出现多个 `pair_i_j`。节点在第一条失败的义务处就以 `outcome mismatch` 终止，所以更靠后的行没有被尝试。
- stage trace 中 `_correspondence` 的输出是 `all: 0, empty: 1, mapped: 170`，所以第 10 行（a）和第 8 行（b）是 P4 给出的整数映射，而且映射已经被 x86_maps 确认。
- 卡住是因为 terminal pair 本身难证，而且耗时方差很大：
  - `pair_63_10`：a 中 unknown 2988s；b 中 unsat 1139s；snap-r35b b（`cap5377d30-local/answers-b.txt`）中 unsat 937s。
  - `pair_68_8`：b 中 unknown 3486s；a 中 unsat 1429s；snap-r35b b 中 unsat 643s。
  - 在 snap-r35b 里卡住的是 `pair_58_13` 和 `pair_68_9`（路径编号随路径集合变化），r37c-a 中 EVM 58、68 两行对应的 `pair_58_12`（508s）和 `pair_68_8`（1429s）都证出来了（行号随路径集合变化，按 EVM 编号对应，属推断）。
- 结论：P4 已经消除了 "all" 行，correspondence 不存在可以通用修复的问题。剩下的是个别 pair 义务的求解难度，这属于任务 A：`pair58/fix.diff` 的 `_refute_over_light_premise` 去掉了 gas 相关的重合取项，服务器上 `pair_58_13` 574s、`pair_68_9` 833s 证出。建议在 r37c 上叠加任务 A 的修法，再跑两个上下文。

## 4. 离线验证数据

用 `cloud-inputs/tools/check_obligation.py`（生产 `_check`，每条查询 30s，每个义务 1800s）在本地重跑 r37c 两个上下文里卡住的 SMT2：

- 环境：4 核 Linux；4 个任务同时跑，每个占一个核；
- 两份代码：本分支的代码副本（"r37c"），以及在它上面再打 `cloud-inputs/pair58/fix.diff`（任务 A 的 light-premise 修法，3 个 hunk 都能干净应用，只有行号偏移）的副本（"r37c+A"）。

| 义务 | 服务器 r37c（3 worker 节点内） | 本地 r37c | 本地 r37c+A |
|---|---|---|---|
| a `pair_63_10_f768074e3e1a` | unknown 2988s | unknown 1457s（3 个 lemma；所有路由都试过后放弃） | **proved 801s**（7 个 lemma） |
| b `pair_68_8_ade8b21d7787` | unknown 3486s | unknown 1436s（3 个 lemma） | **proved 976s**（7 个 lemma） |

结论：

- 卡住的原因不是 P1–P6。不加 A 的修法，本地同样证不出；加上之后两条都在 1000s 内证出。
- 所以 5377 剩下的缺口就是 pair 义务的求解难度，任务 A 的修法正好对症。
- 下一步：在服务器上用 r37c+A（等于本分支加上任务 A 的分支）全量重跑 5377 的 a、b 两个上下文。
- 本地只验证了这两条义务。同一节点其他 pair 义务在 r37c+A 下是否有回归，需要看任务 A 的回归数据（`reg_patched.log` 对 `reg_base.log`）和服务器全量结果。

## 5. 测试结果

### 全量快测

命令：`PYTHONPATH=. poetry run pytest tests/unit -q -m "not slow" -p no:cacheprovider -n 4`（Linux，4 核）。没加 `-x`，因为加了会停在第一个 msize_absint 已知失败上，后面的测试就跑不到了。

- **结果：1587 passed、36 failed、2 skipped，用时 452s。**
- **35 个是已知例外**：全部是 `tests/unit/test_msize_absint.py::*`，原因是 `ModuleNotFoundError: No module named 'prov_common'`（依赖被忽略的 `tmp/prov_common.py`）。这与 `b3b/unit.log`（snap-r37c，35 failed）一致。
- **另外 1 个**：`tests/unit/test_block_uf_unification.py::test_offset_view_step_lemma_proves_the_rewrite_without_per_read_queries`。
  - 失败形式：`assert unknown == unsat`，即测试内部的 solver 查询在 4 进程并行负载下超时；
  - 单独按节点 ID 重跑：本分支 passed（3.3s），基线 a84f7d4 也 passed（3.2s）；
  - 这个测试不经过 P1–P6 的代码，判定为负载引起的偶发失败。

### 新测试

按节点 ID 单独跑过（`-v`），16 个都被收集到，全部 passed，没有同名覆盖。`tests/unit/test_block_correspondence.py` 的 10 个也全部通过。

| 测试 | 覆盖 |
|---|---|
| `test_prefix_solver_matches_fresh_solver_across_pops` | P1：手写序列，包括 pop 回公共前缀、回到空前缀 |
| `test_prefix_solver_matches_fresh_solver_on_random_dfs`（新） | P1：150 次随机 DFS 式查询，每次与新建 solver 的答案一致；断言 pop 深度覆盖 0–3 |
| `test_prefix_unknown_pruned_only_by_probe_unsat`（新） | P1：精确结果为 unknown 时，只有探针 UNSAT 才剪；探针抽象 SAT 或没有 bvmul 时都保留路径 |
| `test_prefix_solver_recovers_from_failure_mid_sync`（新） | P1 修正：add 中途抛异常后不残留断言；被外部多 push 一层时，check 前能检测出来 |
| `test_is_possible_with_prefix_solver_agrees_and_keeps_witness`、`test_prefix_unknown_keeps_path_unless_probe_refutes` | P1 |
| `test_summary_entry_answered_by_path_witness`、`test_summary_entry_solved_when_witness_misses` | P2 |
| `test_disjoint_groups_cover_every_pair_once_and_weaken_it`、`test_correspondence_records_and_mapping` | P3、P4 |
| `test_disjoint_dedup_keeps_names_and_coverage`（新） | P3：记录名与清单的 `evm_disjoint_*` 一致，顺序相同且全部 proved；组查询数少于对数；每条记录的公式是它所属组的子合取式 |
| `test_disjoint_group_failure_falls_back_to_full_pair_queries`（新） | P3：分歧边本身不互斥时，组查询失败后改用整对原式证明 |
| `test_disjoint_overlap_gives_full_product`（新） | P3：EVM 路径真有重叠时返回 `()`，并且不留下任何记录 |
| `test_coverage_refuted_over_mul_abstraction_first` | P5 |
| `test_complement_refutation_hit_and_miss`（新增 2 个断言） | P6：命中（互补、simplify 为 false、嵌套 And）；不命中（只是蕴含而非语法互补、在窗口外、与路径一致） |
| `test_summary_solve_skips_solver_on_complement` | P6 |

变异测试：去掉 P1 修正（作用域数核对和异常时 reset）之后，`test_prefix_solver_recovers_from_failure_mid_sync` 失败。

## 6. 未解决的问题

1. 5377 的两个上下文仍然证不完。瓶颈在 pair 阶段的个别 terminal pair（单条 1000–3500s，且方差大），需要叠加任务 A 的修法后在服务器上全量重跑。
2. x86 路径集合在 base 与 opt 之间不完全一致（见第 3 节）。要确认差异只来自墙钟预算导致的 summary 回退，需要在服务器上导出两边的条件本身（不只是哈希），对哈希不同的 12+19 / 6+7 条逐条做等价或包含检查。
3. P1 的增量 solver 让可达性结果依赖查询历史。历史是确定的，但这意味着执行器遍历顺序一变（例如改了 DFS 策略），剪枝集合就可能变化。这只影响路径数，不影响健全性（coverage 兜底）。
4. `formula.sexpr()` 生成的记录文本（exec5377 中 profile 为 53s）仍然没有改成惰性生成。

## 附录：本地脚本

（不提交，位于会话 scratch 目录。）

- `cmp_paths.py`：比较 stage 与 base 的路径哈希集合；
- `cmp_ctx.py`：做跨上下文和四次运行并集的比对；
- `evalq.py`：Z3 model eval 对量词和 lambda 的行为实测；
- `mutate.py`：对 P1 修复做变异测试。
