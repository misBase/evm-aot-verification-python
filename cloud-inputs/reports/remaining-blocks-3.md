分支（任务 N3 / remaining-blocks-3）：`claude/n3-remaining-blocks-3-p77zn8`（会话只允许推送这个 `claude/...` 分支，未使用任务书建议的 `cloud/remaining-blocks-3`），基于 `cloud/inputs-n3`（ac0088f = N2 的 b7d4faa + 本任务输入）。

# 任务 N3：3G 冻结版上剩余的 inconclusive 块

所有结果都在 `cloud-inputs/n2/fixtures/`（冻结版，`sha256sum -c` 核对 Permit2 / Pool / PoolManager 一致）上取得。本机 4 核 / 15GB（cgroup 限制），z3 4.15.4，capstone 5.0.6，每查询 30s，`BLOCK_SUMMARY_LEMMAS=1 PYTHONHASHSEED=0`。整节点用 `cloud-inputs/n3/tools/run_probe.sh`（= N2 的 `run_probe.sh`，即原样的 `tools/probe_block_obligations.py` 外加逐 `_check` 计时日志），串行（无 `BLOCK_PAIR_WORKERS`）。各次运行的代码版本见 §6 表中的提交号。

## 1. 结论

| 合约 | 块 / 实例 | r5（3G，服务器） | 根因 | 修法 | 本机结果 |
|---|---|---|---|---|---|
| PoolManager | 16670 sym7296 | `pair_4_84` unknown（26002s） | SDIV 符号分支树：x86 每个分支各有一个 `holiman_udiv`，参数只在本分支守卫下与 EVM 的 `holiman_udiv(|a|,|b|)` 相等，无条件的参数合并全部失败；另外节点内被提升的 unify 路线占去一半预算，守卫情形的快速查询受进程状态影响 | 9（守卫分情形）、10（排序键记忆化）、16（被提升路线的份额上限）、18（新 Context 中的快速情形查询 + 早期 `guardsq` 路线） | goal 2 生产 `_check` **36.2s proved**（修法 18 之后；之前 1326.6s）；m=768 的 `pair_2_74` goal 2 5.4–923.6s（N2 节点内 10664.8s unknown）；整节点见 §6 |
| Aave | 6182 | `pair_63_2` unknown（792.9s，12h 预算末尾） | 对应关系提议在 30s 内 unknown → 多个 x86 行成为 "all"（每行 95 个 pair；`pair_63_2` 单独 2121–2883s 可证）；其后是义务数（49 行 × 150–200 个 `x86_maps`，每个 30–90s，`normalize_word_arith` 占大头），以及少数很难的 maps（`x86_maps_2_7` 单独 2854s，靠补跑的 potential 求解） | 11（对应关系 blast 回退）、12（补跑求解按类提前）、14（normalize 记忆化）、17（stuck group 阶段在有产出时延长） | pair 阶段**没有 "all" 行**（`pair_63_2` 不再出现）；每行剩余的单独 maps 202 → 19；整节点见 §6 |
| Aave | 7200 | x86 分段 12h 超时 | 每个 DIV 命中把 8 个栈 limb 各自用新缓存对整条 x86 内存链做 `forward_selects`（占 x86 分段 53%）；其次每个命中的 `entry` SAT 约 40s | 13（limb 转发共享缓存）、15（entry 模型复用） | DIV 重复命中 570–630s → **41–47s**；`entry` 需要求解的命中 32/55 → 4/51；整节点受本机内存限制（§6） |
| PoolManager | 4418 | 两个实例 12h 预算耗尽；sym 的 `x86_maps_1_0` 13894s unknown | x86 876 条路径：内存扩展费代码里 `words == 0` 的分支在后面汇合，执行器不合并；x86 分段 90% 是可达性检查 | 未修（方向见 §2.4） | 用新对应关系重建的 `x86_maps_1_0` **0.1s proved**；1h 分诊见 §2.4 |

修法编号接任务 N / N2（1–8）。全部只改 Python 端，没有按合约或块号特化。没有出现任何 SAT（反例），也没有发现编译器问题。

## 2. 逐块分析

### 2.1 PoolManager 16670（`pair_4_84` / `pair_2_74` goal 2）

- 数据：`cloud-inputs/n3/dumps`（未提交，只放诊断）中按 dump_paths 导出的 sym7296 `pair_4_84`；goal 2 存为 `cloud-inputs/n3/smt2/pm16670_sym7296_pair_4_84_goal_2_of_7.smt2`。m=768 的 goal 2 沿用 `cloud-inputs/n2/smt2/pm16670/pair_2_74_goal_2_of_7.smt2`。两者结构相同：`holiman_udiv` 6 个应用、`host_gas_sstore` 65 个、`sha3_bytes_64` 9 个、`host_gas_sload` 9 个；最小的守卫都是 `sign(a) == sign(b)`（114 / 110 字符）。
- **剖析 1（修法 10）**：`unify_uf_arguments` 在 240s 里 73% 的时间（175s）花在 `sexpr()` 上——每轮都对所有候选参数对按 `len(sexpr())` 重新排序，大参数（内存数组）每轮重新打印。记忆化后同样 240s 合并数 6 → 24。`unify_across`（`_unify_node`）用同一排序键。
- **剖析 2（修法 9）**：按最小守卫分两情形，每个情形内做 `unify_uf_arguments` 然后直接查询：sym7296 情形 True 304s unsat（64 条合并引理，5 个失败对 46s）、情形 False 42s unsat；N2 的 m=768 实验是 622s / 601s（修法 10 之前）。
- 生产 `_check`（`cloud-inputs/n3/tools/regress_traced.py`）：
  - 第一版每个情形走 `_unify_and_split`（乘法抽象 + 合并探针 + sweep）：m=768 510.6s proved；sym7296 情形 0 用完它的一半份额（834s）仍 unknown，嵌套拆分只剩 10s。
  - 定稿：每个情形走 `_unify_case`（直接合并 + 一次直接查询 + `_after_unification` 的 opaque/blasted 尝试），守卫路线在适用时拿剩余预算的一半（同 `alias`）。**sym7296 goal 2 1326.6s proved**（守卫路线 702.7s），m=768 923.6s proved（守卫路线 761.3s）。
  - 节点内（4a30af6 之前）：16670 的前 15 个 SDIV 行（69–83）goal 2 都很快（0.1–12s，部分由 unify 证出），于是 `_winners_first` 把 unify 提升到最前，**提升的路线拿剩余预算的一半**（约 7300s），守卫路线排在后面。修法 16：被提升的路线最多拿它在本类中最长一次证明的 8 倍（至少 4 个查询超时）。
  - 补充观察：在**新进程**里直接对 m=768 goal 2（原式、skolemize 之后、`pin_split` 之后都一样）调用 `_retry_over_guard_cases`，两个情形都被 3s 的快速精确查询 unsat，整条路线 3.0–4.6s。生产 `_check` 中同一路线却在情形 0 走到合并（761s）。差别不在公式，而在此前各路线留下的进程状态（AST 创建顺序影响 simplify 的结果形状与求解器的运气）。所以守卫路线的耗时有很大的波动：快则几秒，慢则数百秒；本节的耗时数字都应按此理解。在 90de4cd 上用生产 `_check` 再跑一次 m=768 goal 2：前面各路线 129.5s 都 unknown，守卫路线 **5.4s** unsat（上次 761.3s）。4a30af6 的整节点中，`pair_4_84` goal 2 在守卫路线里走到合并并失败（快速查询没中），随后进了 unify 路线。
  - 修法 18：情形的快速查询没中时，把公式 `translate` 到一个**新的 z3 Context**（精确拷贝）再分情形、再查一次（`_fresh_context_unsat`）；并在 `quick` 之后加一条只做这些快速查询的 `guardsq` 路线。生产 `_check` 上 sym7296 goal 2：**36.2s proved**（`lia` 23.8s 后 `guardsq` 3.4s）。

### 2.2 Aave 6182（`pair_63_2`）

- 前两次导出（`dump_paths.py`）的对应关系不同：第一次行 2 → 93；第二次 x86 行 2、4、6、8、10、12、16、20 都是 "all"（和服务器一致：`pair_63_2` = EVM 63 × "all" 行 2）。原因：`_correspondence` 先用执行器的见证模型，没有时用 3s 的增量查询；对这些行 `premise ∧ x_j` **直接 3s 和 30s 都 unknown**，`simplify(·, blast_select_store=True)` 后 **SAT 3–8s**，模型恰好命中一条 EVM 路径（行 2 → 93、行 3 → 92、行 4 → 88），与相邻行的模式一致（行 j 与 j+1 对应相邻的 EVM 路径）。
- `pair_63_2` 本身成立：生产 `_check` 单独 2121s / 2883s proved。7 个 goal 中 goal 6 用了 2773s：所有路线 unknown，最后由 `_check` 末尾"补跑被截断的 potential 求解"证出（potential 路线自己的求解上限是 4 个查询超时）。服务器上这个义务只拿到 12h 预算末尾的 792.9s。
- 修法 11（对应关系提议的 blast 回退）后，在无见证（最坏情况）的离线 `_correspondence` 中 40 行需要回退，39 行 0.5–8.5s 得到模型，只有行 2 一次 30.3s unknown（之前一次 6.1s）；于是加了一次 4 倍预算的重试。整节点运行中 pair 阶段**没有 "all" 行**（行 2 → 93）。
- 新的瓶颈：行 0 → EVM 0（202 个合取项）的 `x86_maps_0_k` 每个约 90s（修法 14 之前）。`x86_maps_0_85` 的路线分解：`lia` 17.2s、`quick+norm` 3.3s、`blast+norm` 0.5s **证出**，其余约 105s 全在 `normalize_word_arith`（2037 条改写引理）。剖析：`_offset_view_select` 7571 次调用（每次沿内存 Store 链走到底）占大头，其次是每条引理的 `Not(old == new).sexpr()`。修法 14 记忆化后，同一义务的 normalize 74.6s → 34.9s，兄弟义务（第二次）65.1s → 16.2s。
- 修法 17：`discharge_maps_by_prefix` 按 EVM 合取项分组（多行共享的合取项一组），卡住的组由 `_prove_stuck_groups` 用一次弱化查询证明；该阶段原来上限 10 个查询超时（300s），6182 中 32 个组用完后其余成员（约 9000 个）都走自己的路线。现在只要已试的组至少一半证出，就延长到剩余预算的 1/4。90de4cd 的整节点中 90 个组全部 unsat（每个 4–22s），每行剩余的单独 maps 从 202 降到 19（行 0、1：19 个，832s / 716s）。
- 试过但没有采用：把一行剩余的 19 个合取项合成一个行组查询 `premise ∧ x_j ∧ ¬(c_1 ∧ … ∧ c_19)`（同样是弱化，可靠）。生产 `_check` 580s 内没有结果，比 19 个单独义务（约 760s）还难，所以撤回（工具 `row_group.py`）。
- 剩下的难点：`x86_maps_2_7`（行 2 → EVM 93 的第 7 个合取项：一个 28KB 的否定式，和 x86 路径中 94 个提到 `stack_12_z0` 的大合取项一起，看起来是按 `stack_12_z0` 查表的最高位 / 对数类计算）。单独运行（`cloud-inputs/n3/smt2/aave6182_x86_maps_2_7.smt2`）：`lia` 50s、`potential+norm` 263.7s、`bvabs` 124.9s、`exact+norm` 60.5s、两条 unify 各约 990s 都 unknown，最后由**补跑的 potential 求解**证出，共 **2854.3s proved**（491 条 normalize 引理）。所以它成立，只是贵；修法 12 让同类兄弟（其他行对应的同形合取项）在 potential 路线挂起后立刻补跑。
- 修法 12（补跑的 potential 求解按类记账）：同一类（如所有 `pair_*_goal_6_of_7`）中只要补跑赢过一次，后面的兄弟义务在 potential 路线挂起后立刻以剩余预算的一半补跑，而不是等所有其他路线（`pair_63_2` goal 6 的 2350s）跑完。

### 2.3 Aave 7200（x86 分段）

- cProfile（`x86_profile.py` 原样，`--seconds 4500`，修法 9–10 时的代码）：4935s 中 **2607s（53%）在 `apply_div_summary → _forwarded_limb → forward_selects → resolve_select_over_store`**，只有 2 次 DIV 命中（73355 次 `resolve_select_over_store`、3000 万次 `linearize_address`）。`_forwarded_limb` 对 8 个栈 limb 各调用一次 `forward_selects(load)`，每次新缓存，每次都把整条 x86 内存 Store 链（含所有存入值）重写一遍。其余：可达性 911s、`_solve` 中把查询打印成证书文本 321s、copy-loop 前提蕴含中的 `forward_selects`（每命中一个缓存）340s、DIV lemma 134s。
- 修法 13：`forward_selects_shared`——进程级的同一个缓存（`forward_selects` 对每个结点是纯函数，缓存保活所有键结点，结果与新缓存相同）。整节点（`node_profile.py`）：第一次 `div@0x6e22d`（含 lemma 证明）405s（N2 r3）→ **90.1s**；重复命中 `div@0x6fc70` / `div@0x70b93` 570–630s → **41–47s**（几乎全是 `entry` SAT 40–46s）；第二条路径到达这组命中的时间 6559s → 3968s。
- 之后每条路径一轮 summary 约 900s（之前约 2600s）：`copy_loop@0x6ee68` 每次约 365s（`entry` 35s、`copy_domain` 59s、前提蕴含 ~50s、归纳 ~66s），7 个 memgas 每个约 55s（`entry` ~40s + exit guard ~20s），2 个 div 每个约 45s。
- 修法 15（entry 模型复用）：命中的 `entry` 解出的模型（在原前提上求值为字面 true）保存在运行时；下一个命中先用它（以及执行器的见证）求值自己的前提；执行器在命中之后，若当前见证已不满足路径条件，就采用这个模型作为路径见证（可达性检查用之前仍会求值确认）。
- 修法 15 生效：b8b429d 的运行中 55 次命中有 32 次要解 `entry`；4db8738 的运行中 51 次命中只有 4 次。同一时刻的进度：3958s 执行 715 个基本块（之前 3645s 执行 599 个）。
- 两次整节点运行都在 7.4–7.7GB RSS 时被 cgroup OOM 杀掉（7253s、5435s），当时同机还有 6182（3.6–5.4GB）与 16670（1.7GB）。N2 的运行也到 7–8GB。x86 分段的内存随执行的状态增长，本机要单独跑才有可能跑完 12h（§6、§8）。

### 2.4 PoolManager 4418（1h 分诊）

- x86 分段（`x86_profile.py`，修法 9–10 时的代码，3600s）：**2684s 跑完，876 条路径**；6105 次可达性检查共 2418s（**90%**），剪掉 1660 个分支；summary 只有 118s（memgas 每个约 0.3s）。
- 分叉位置（反汇编 0x2cc21–0x2db31、0x2da36–0x2da8a）：每个符号长度内存访问的扩展费代码 `size+32` 溢出检查（`jb` → 错误桩）、`words = (size+31)>>5`、`test rbx,rbx; je L`（`words == 0` 跳过平方）、`mul rbx; jb` 溢出（错误桩）、`L:` memgas summary（及其 exit guard 拆分）。`words == 0` 的两个分支在 `L` 汇合，执行器不合并，所以活路径数按访问点翻倍（约 40 条活路径穿过每个 memgas 点），每个错误桩又各自成为终止路径（如 `terminal@0x2d3a2` 60 条）。EVM 端同样的扩展费不分叉（63 条路径）。
- 新对应关系（`dump_paths.py`，pair 阶段 5550s）：877 行中 763 行直接映射、60 行空、54 行 "all"；`propose_from_siblings` 之后 **0 个 "all" 行**。服务器上卡住的 `x86_maps_1_0`（行 1 → EVM 1，exit@190690）按此重建后生产 `_check` **0.1s proved**（服务器 13894s unknown，当时的对应关系与本次不同）。
- 结论：**预算 / 路径数类**；单个义务不是障碍。可行方向（本任务未实现）：(a) 把 memgas summary 的模板向前扩到 `test; je; mul; jb` 这段（`words == 0` 时平方本来就是 0，跳过只是优化），整段无分支；(b) 执行器对无副作用的短菱形做状态合并（寄存器 / 标志用 ite 合并）。两者都能把 876 条路径降到约 63 条量级。1h 整节点分诊（新代码，`--keep-going`）见 §6。

## 3. 改动位置

（行号为最终提交时 `verification/block_equivalence.py` 中的位置。）

- `verification/block_equivalence.py`
  - 修法 9：`uf_guards`（:2381）、`assume_guard`（:2427）、`_GUARD_MAX_DEPTH`（:2825）、路线表中的 `("guards", False)`（:3372、:3374）、路线分派（:3479，适用时一半剩余预算）、`_unify_case`（:4155）、`_retry_over_guard_cases`（:4175）。
  - 修法 10：`_text_size`（:2279），用于 `unify_uf_arguments`、`unify_across`、`sweep_equalities`、`unify_potential_arguments`、`unify_identities`、`_small_conjuncts` 的排序键与大小判断。
  - 修法 11：`_correspondence` 中 unknown 行的 blast 回退（:3798，4 倍重试一次）、`_blasted_model`（:3823）。
  - 修法 12：`_check` 中挂起 potential 求解的提前补跑（:3505）与末尾补跑，`_resume_potential`（:3545）。
  - 修法 14：`_rewrite_candidate`（:1051）、`_inequality_text`（:1065），用于 `normalize_word_arith` 与 `_join_and_decide`。
  - 修法 16：`_check` 中被提升路线的 `route_end`（:3402），各路线分派中原来的 `node_deadline` 份额改为 `route_end`；本类最长证明时间记在 `stats[(route, norm, "longest")]`（:3498）。
  - 修法 17：`_prove_stuck_groups` 的 `extend_until`（:3583），`_pair_phase` 中传入剩余预算的 1/4（:4263）。
  - 修法 18：`_fresh_context_unsat`（:2437），`_retry_over_guard_cases` 的 `quick_only` 与情形快速查询的新 Context 重试，路线 `("guardsq", False)`（:3371、:3374，分派 :3476）。
- `common/store_forwarding.py`：修法 13 `forward_selects_shared`（:228）、`_SHARED_FORWARD_LIMIT`（:102）、`clear_memo` 一并清空（:92）。
- `x86_64/summaries/div.py`：修法 13 `_forwarded_limb` 用共享缓存（:318）。
- `verification/block_summaries.py`：修法 15 `_sat_model`（:549）、`sat_model` / `entry_model`（:605）、`_solve` 记录模型（:897）、`apply` 中 entry 先试模型（:974）。
- `x86_64/cfg_executor.py`：修法 15 `_adopt_entry_model`（:859），两处调用（:758、:850）。
- 测试：`tests/unit/test_block_remaining_blocks_3.py`（新增）；`tests/unit/test_block_route_order.py`：`test_promoted_route_gets_half_of_what_is_left` 预置一个长的历史证明（修法 16 的上限不起作用时仍是一半），新增 `test_promoted_route_with_cheap_wins_gets_its_cap`；`tests/unit/test_block_correspondence.py::test_empty_probe_only_for_unknown_rows_without_sibling_proposal` 同时把 `_blasted_model` 强制为 unknown（修法 11 会把它的 unknown 行真的解出来）；`tests/unit/test_block_remaining_blocks.py::test_summary_entry_falls_back_to_the_blasted_query` 的 mock 从 `solve_query` 改到 `_sat_model`（期望 SAT 的查询现在经 `_sat_model` 以保留模型，测试本意"第一次 unknown 后走 blast 回退"不变）。
- 工具：`cloud-inputs/n3/tools/`（§7）。节点文件：`cloud-inputs/n3/nodes/`。

## 4. 健全性论证

- **修法 9（守卫分情形）**：`uf_guards` 只**选**守卫（一个 ite 条件，无绑定变量，其分支含多次出现的 UF 应用；按化简后的形式分组，组内各写法等价）。`assume_guard(F, raws, v)` = `L ∧ simplify(F[r := v])`，L = raws[0] 或其否定：在 L 下每个 r 的值就是 v（各写法等价），所以替换是等价变换，simplify 也是。两个情形 v = True / False 覆盖 F 的全部模型，所以 F unsat 当且仅当两个情形都 unsat。每个情形内的合并（`unify_uf_arguments`）是原有的弱化：每次合并都由被反驳的 `P ∧ x ≠ y` 支持，F ⊨ F'，只有 unsat 能传回。`_after_unification` 同原有论证（不透明化只增加模型；blast 是等价改写）。任何一个情形没有被反驳，路线就返回 unknown，不留任何结论。证书：记录的 lemmas 是每个情形的全部被反驳查询（`guard_<深度>_<情形>_*`）。守卫选错只会白花时间。
- **修法 10**：`_text_size(t) == len(t.sexpr())`，记忆化（`_memoized` 保活 t，id 不复用），值相同，所以顺序与每次合并都不变。只影响耗时。
- **修法 11**：对应关系只是**提议**（`_correspondence` 的原有约定）：每一行仍由自己的 `x86_maps_j_k` + `pair_s_j`（或 `x86_empty_j`，或 "all" 行的全部 `pair_i_j`）证明，失败就降级。blast 是 Z3 的等价改写，模型在同一组常量上，读出的提议与原式模型读出的同类；unsat 只提议"空行"，`x86_empty_j` 仍需 `_check` 证明。
- **修法 12**：补跑的是同一个查询（`_retry_over_potential` 留下的 target，其等价/弱化论证不变），lemmas 与原来末尾补跑完全相同；只改变补跑发生的时刻和预算。`("resume", False)` 只记在统计里，不进路线表。
- **修法 13**：`forward_selects` 对每个结点是纯函数（结果只取决于结点），共享缓存保活所有键结点（`_ALIVE`），id 不会被复用，所以结果与新缓存逐结点相同（测试 `test_shared_forwarding_equals_fresh_forwarding`）。缓存满 200 万条整体清空，`clear_memo` 也清空。只影响耗时（以及内存）。
- **修法 14**：`_word_rewrite(t)` 与 `simplify` 都是 t 的纯函数；`Not(old == new).sexpr()` 是 (old, new) 的纯函数；记忆化（保活参数）返回相同的值。每个改写照旧要 `_identity_proof` 证明。实测同一义务的输出公式相同、引理文本相同（唯一差别是 `_normalize_lambdas` 生成的新绑定变量名，本来就每次不同）。
- **修法 15**：模型 M 只有在使前提**字面求值为 true**（`model_completion=True`）时才当作 entry 的 SAT 证据——与原有的执行器见证完全相同的判据，量词等无法化简的项留成符号，不算命中。`sat_model` 只在 `_solve` 期望 SAT 且答案 SAT、且模型在原公式上求值为 true 时保存。执行器的路径见证只用来跳过求解器调用：`is_possible` 每次用它之前都对整条路径条件求值确认，不满足就照常求解；剪枝仍然只看显式 unsat。entry 的作用本来就只是区分空命中（修法 3 的论证）；它的 SAT 证据现在可以来自上一个命中的模型，但判据不变。
- **修法 16**：只改被提升路线的时间份额（上限为它在本类中最长一次证明的 8 倍，至少 4 个查询超时）；没有证出就照常落到后面的路线。只影响耗时。
- **修法 17**：组查询 `premise ∧ P ∧ ¬c`（P 是各成员 x86 路径的公共前缀）是每个成员 `premise ∧ x_j ∧ ¬c` 的弱化，与原有论证相同；只改了这个阶段的时长（有产出时延长到剩余预算的 1/4）。只影响耗时。
- **修法 18**：`formula.translate(Context())` 是同一公式在另一个 Context 中的精确拷贝，`assume_guard` 的论证不变（在那个 Context 中构造同样的两个情形）；那里的 unsat 就是这个情形 unsat。`guardsq` 只是同一路线的快速部分，提前运行。
- 没有"提议出错就会误证"的通道：守卫、对应关系、补跑顺序、模型都只是候选或加速；每个结论最终都落到被反驳的查询，或落到对所有解释都成立的恒等式上。

## 5. 测试结果

- **全量快测**（`poetry run pytest tests/unit -q -m "not slow" -p no:cacheprovider`，串行，与 2 个整节点并行，代码 90de4cd）：**1801 passed, 3 skipped, 0 failed**（1210s）。日志 `cloud-inputs/n3/results/fast-tests-90de4cd.log`。
- 之前一次（代码 6522a8d 之后、两处测试更新之前）：1795 passed, 3 failed。三条失败：
  - `test_block_route_order.py::test_promoted_route_gets_half_of_what_is_left`：断言的是修法 16 之前的规则（被提升的路线总拿一半）。改为预置一个长的历史证明（上限不起作用，仍是一半），另加一条 `test_promoted_route_with_cheap_wins_gets_its_cap`（廉价历史 → 4 个查询超时）。
  - `test_block_correspondence.py::test_empty_probe_only_for_unknown_rows_without_sibling_proposal`：测试把某些行的增量查询强制为 unknown，用来检验"空行探测只给没有兄弟提议的 unknown 行"；修法 11 的 blast 回退把这两行真的解出来了（行 3 → EVM 0、行 4 → EVM 2，都正确）。测试同时把 `_blasted_model` 强制为 unknown，本意不变；回退本身另有测试。
  - `test_block_uf_unification.py::test_alias_split_keeps_satisfiable_pairs_open`：负载敏感（N2 §9.1 已记录），单独运行通过；在最终全量中通过。
- `tests/unit/test_block_remaining_blocks_3.py`：25 条快测（另有 1 条 `slow`：16670 goal 2 的守卫路线），函数名互不相同；逐个按节点 ID 单独运行的结果见下。另在 `test_block_route_order.py` 新增 1 条。
- 相关已有测试（`-k "summar or executor or cfg or copy or memgas or div or remaining"`）：453 passed, 2 skipped（872.9s）；normalize 相关（`-k "normali or word or offset_view or remaining or identity"`）：119 passed。

### 5.1 SMT2 回归（`cloud-inputs/n/tools/regress.py`，生产 `_check`，每文件新 prover，上限 1800s，与 2–3 个整节点并行；代码 389fdc7，即修法 9–13）

| 来源 | 义务 | N2（修法 1–8） | 本次 |
|---|---|---|---|
| r3c | 5802 `model_domain_nonempty`（预期 sat） | 0.3s sat | 0.3s sat |
| r3c | 4837 `x86_maps_12_0` | 18.4s | 17.9s |
| r3c | 4837 `x86_maps_14_0` | 14.2s | 13.2s |
| r3c | 1327 `x86_maps_0_0` | 76.6s | 69.6s |
| r3c | 1327 `x86_maps_0_1` | 45.8s | 40.2s |
| m | 1327 `x86_maps_0_46` | 77.8s | 65.5s |
| m | 1327 m192 `x86_maps_0_46` | 85.2s | 84.5s |
| m | 1327 `pair_0_6` | 172.4s | 165.1s |
| m | Aave 8248 `pair_0_1` | 1236.5s | 1159.6s |
| n | Aave 11831 `evm_assumption_7`（只走 `_check`） | 1029.9s unknown | 1030.3s unknown |
| n | 1327 `x86_empty_6` | 167.9s | 148.8s |
| n | 1327 `x86_empty_7` | 153.0s | 140.9s |
| n2 | 冻结版 1327 `x86_empty_3` | 142.5s | 138.3s |
| n2 | 16670 m=768 `pair_2_74` goal 2 | 10664.8s unknown（节点内） | **923.6s proved** |
| n3 | 16670 sym7296 `pair_4_84` goal 2 | 26002s unknown（服务器节点内） | **1326.6s proved** |
| n3 | 6182 `pair_63_2` | 792.9s unknown（服务器节点内） | **2121s / 2883s proved** |
| n3 | 4418 `x86_maps_1_0`（本次对应关系重建） | 13894s unknown（服务器） | **0.1s proved** |

11831 `evm_assumption_7` 的 unknown 与 N2 相同（N2 §9.3：只走 `_check` 时取决于计时；生产中走 `check_paths` 的乘积字泛化，0.0s 证出）。其余没有退化。

## 6. 整节点

（待补）

## 7. 诊断工具（`cloud-inputs/n3/tools/`，仅用于诊断）

- `run_probe.sh`：整节点（同 N2，输出到 `cloud-inputs/n3/runs/`）。
- `node_profile.py`：整节点 + x86 分段剖析（`x86_profile.py` 的日志），跑完 `prove()` 并写 probe 格式的 JSON。
- `regress_traced.py`：生产 `_check`，记录各路线方法的耗时、每个 goal 部分的耗时与引理种类、路线统计。
- `split_profile.py`、`unify_overhead.py`：守卫分情形的逐次 `_prove_equal` 记录；`unify_uf_arguments` 的 cProfile。
- `correspondence.py`：在 dump 目录上跑生产 `_correspondence`（无见证）。
- `prefix_scan.py`、`path_diff.py`：联合路径查询的前缀扫描；两条路径条件的逐合取项差异。

## 8. 未解决的问题

（待补）
