分支（任务 N4 / remaining-blocks-4）：`claude/n4-remaining-blocks-4-3cx7qs`（会话只允许推送这个 `claude/...` 分支，未使用任务书建议的 `cloud/remaining-blocks-4`），基于 `cloud/inputs-n4`（7b1e121 = N3 的 4db8738 + 本任务输入）。

# 任务 N4：收尾 N3，并解决剩余难块与内存问题

所有证明结果和耗时都在 `cloud-inputs/n2/fixtures/`（冻结版，`sha256sum -c` 核对 Permit2 / Pool / PoolManager 一致）上取得。本机 4 核 / 15GB（无 swap），z3 4.15.4，capstone 5.0.6，每查询 30s，`BLOCK_SUMMARY_LEMMAS=1 PYTHONHASHSEED=0`。整节点用 `cloud-inputs/n4/tools/run_probe.sh`（= N3 的 `run_probe.sh`，即 `tools/probe_block_obligations.py` 外加逐 `_check` 计时日志，输出到 `cloud-inputs/n4/runs/`），每节点一个进程，节点预算 43200s，并用本任务新加的 `--node-memory-mb` 给每个节点设内存预算。**本机同时跑了 3–6 个进程（4 核），所有耗时都偏保守。**

修法编号接 N3（9–15），本任务为 16–20。全部只改 Python 端，没有按合约或块号特化。没有出现任何 SAT（反例），也没有发现编译器问题。

## 1. 结论

| 项 | 结果 |
|---|---|
| 1. 收尾 N3 | `remaining-blocks-3.md` §5（全量快测，1 个测试与修法 11 不一致，已修）、§6（服务器整节点探针）、§8 已补 |
| 2. 节点级可观测性与内存隔离 | 每个节点记录 pid、开始/结束时间、RSS（开始/峰值/结束），worker 状态文件实时给出"哪个 worker 在跑哪个节点、多大"；节点内存预算：超了只把这个节点记为 inconclusive；新进程池里一个 worker 死掉（段错误、OOM、超硬上限）只让它自己的节点失败并重启该 worker，不再整池报废 |
| 3. Aave 7200 内存 | 定位到两个无界增长源：summary 命中证书里的整条查询文本（每命中约 30MB 且随路径变长，修法 16）和修法 13 的进程级转发缓存（2M 条上限从来达不到，持有大部分 Z3 内存，修法 20）。整节点：（待补） |
| 4. Aave 6182 | `x86_maps_2_7` 单独对所有路线都 unknown（单独 blast+norm 3600s 仍 unknown；服务器上 6.6h 是因为各路线拿的是剩余 9h 预算的份额）；修法 17 按行把剩余合取项作为一个蕴含证明。**整节点 5166s proved**（服务器 r5：12h 预算耗尽 inconclusive），35 个行组全部一次证出（每组 46–92s），行 2 的组（含 2_7）61s |
| 5. PoolManager 4418 | 修法 18（执行器精确合并短的只改寄存器/标志的菱形）：x86 分段 878 → **360 条路径**（出口 72 → 18），可达性检查 6080 → 2563 次，分段 3733s → 1606s；整节点：（待补） |
| 另 | 修法 19：`unify_across` 连续 10 个查询超时没有合并就停（16670 两个实例在服务器上各花 ~10800s 只得到 2 条引理）；16670 整节点：（待补） |

## 2. 逐项

### 2.1 收尾 N3

见 `remaining-blocks-3.md`。全量快测在 N3 最终代码上 1795 passed / 1 failed：`test_empty_probe_only_for_unknown_rows_without_sibling_proposal` 把两行的增量查询 mock 成 unknown，修法 11 之后这两行先走 blast 回退直接 SAT，所以对应关系变了；把 `_blasted_model` 一并 mock 成 unknown 后通过（测试原意不变）。服务器探针（`cloud-inputs/n4/n3-server-probes/`）写进了 §6。

### 2.2 节点级可观测性与内存隔离（`common/node_monitor.py`，`verification/block_parallel.py`）

- **观测**：`NodeMonitor` 包住一个节点的证明（`prove_instance`、`probe_node`）。后台线程每秒采样本进程 RSS（`/proc/self/statm`），节点结果里写入 `pid`、`started_at`、`finished_at`、`start_rss_mb`、`peak_rss_mb`、`end_rss_mb`、`memory_budget_mb`、`memory_exceeded`；`_record` 把它们写进每个实例的 diagnostics（因此进入 partial / 最终报告）。每 10s 重写一次 worker 状态文件 `worker-<pid>.json`（节点、开始时间、当前/峰值 RSS），父进程每轮（≤60s）把正在跑的 worker 状态放进 `result.running`，`verify_block_lockstep` 的 progress（`.partial.json`）里有 `running` 字段。内存暴涨时可以直接看出是哪个 worker、哪个节点。
- **内存预算**（`--node-memory-mb`，`verify_block_lockstep` 与 `probe_block_obligations` 都有；默认不设）：第一次采样超过预算时置进程级中止标志并中断 Z3（`main_ctx().interrupt()`，之后每秒重复）。`solve_query`、`_solver`、`solve_pure_bv` 和 x86 执行器每一步开头调用 `check_abort()`，抛 `NodeMemoryExceeded`；`prove_instance` 捕获它，只把这个节点记为 inconclusive（原因"node memory budget exceeded: RSS … > budget …"），并且不做全预算重试（更长的预算只会长得更大）。节点结束后清空节点缓存、`malloc_trim`，若常驻内存仍超过预算的 3/4，结果里带 `recycle`，进程池在交回结果后换掉这个 worker。若节点在 300s 宽限期内没有退出、或 RSS 超过 1.5 倍预算，worker 以退出码 86 自行退出（由进程池处理）。
- **进程池隔离**：`ProcessPoolExecutor` 中任何一个 worker 死掉，整个池被标记为 broken，所有正在跑的节点一起失败，下一次 `submit` 直接抛异常让整个运行退出（服务器上 PoolManager 全量运行的 `libz3.so` 段错误就是这样）。新的 `NodePool` 给每个 worker 一条管道，用 `multiprocessing.connection.wait` 同时等结果和进程 sentinel：worker 没交结果就退出时只有它的任务得到 `WorkerDied`（带退出码/信号和最后一次状态文件），并立即补一个新 worker；其他节点不受影响。退出码 86 或 SIGKILL（内核 OOM killer）算内存失败：该节点记为 inconclusive，不重试。
- 测试（`tests/unit/test_block_node_isolation.py`，8 条）：监控记录 pid/时间/峰值；`NodeMemoryExceeded` 不是 `Exception` 的子类；超预算后下一次求解抛出、节点结束后标志清除；被中断的查询不进 proof cache；进程池中一个 worker `os._exit(86)`、一个段错误，另一个任务照常完成，池宽度恢复；recycle 换 worker；`prove_instance` 对超预算节点的结果；内存被杀的节点不重试、diagnostics 里有 pid 和峰值。

### 2.3 Aave 7200 的内存增长

诊断工具 `cloud-inputs/n4/tools/mem_probe.py`：跑整节点，每 120s 打印 RSS、Z3 自己的分配量（`Z3_get_estimated_alloc_size`）、各进程级缓存的大小、summary 证书的个数和其中全部义务文本的字符数、执行器状态数，以及每类步骤（可达性检查、summary 应用、其余执行）留下的 Z3 净分配；超过 `--cap-gb` 自行退出，保护容器。只跑 x86 分段（`--x86-only`）。

| 运行（x86 分段，同一时刻附近） | RSS | Z3 分配 | 证书文本 | 转发缓存条目 |
|---|---|---|---|---|
| 基线（N3 代码），1932s | 4.15G | 1.28G | 45 个证书 **13.06 亿字符** | 30716 |
| 修法 16，2530s | 3.34G | 1.58G | 0（只有指纹） | 30716 |
| 修法 16 + 缓存上限 2 万（实验），1335s | **1.75G** | **0.24G** | 0 | ≤20000 |
| 修法 16，1206s（对照） | 3.09G | 1.51G | 0 | 22636 |

- **证书文本（修法 16）**：每个 summary 命中的义务记录里存的是 `formula.sexpr()`，查询带着这条路径的整个 x86 内存，基线里每命中约 4.5MB、30 分钟后约 30MB 且随路径变长，整个节点内一直累积（服务器 9h 46.7GB 中的大头）。没有任何消费者读这段文本：证书按名字、答案和引理判定，`block_parallel.slim` 交给父进程前本来就换成 `sha256:` 指纹。修法 16 在创建时就只存同样的指纹（`summary_text`；`BLOCK_KEEP_SUMMARY_TEXT=1` 保留原文用于诊断），所以交给父进程的证书与之前完全相同。
- **Z3 内存**：去掉文本后 Z3 分配仍持续增长，68% 的净分配记在可达性检查名下。实验排除了增量可达性求解器（每 25 次检查 reset 一次，增长不变）和执行器状态（DFS 下几乎没有挂起的状态）。把修法 13 的进程级转发缓存上限从 200 万条降到 2 万条，同样进度下 Z3 分配 1.51G → 0.24G、RSS 3.09G → 1.75G，进度相同（38 个 vs ~37 个命中）。原因：缓存条目保活它们的结点，x86 分段上这些结点是迄今所有路径被转发过的 store 链及其转发后的副本；200 万条的上限在一个节点里永远达不到，于是旧路径的链全部留着。
- **修法 20**：`forward_selects_shared` 不再自己清空；DIV summary 每次命中开头调用 `shared_forward_scope()`，缓存超过 25000 条（7200 一次 DIV 命中约增加 2.2 万条）时才整体清空。一个命中内 8 个 limb 的转发始终共享（修法 13 的主要收益），相邻几个命中之间也共享，直到上限。
- 整节点（修法 16+20，`n4-7200-a`，节点预算 43200s、内存预算 10000MB）：（待补）

### 2.4 Aave 6182 的预算

- **`x86_maps_2_7` 为什么要 6.6h**：用本机导出（`dump_paths.py`，对应关系与服务器相同：行 2 → EVM 93）重建的 `x86_maps_2_7` 跑生产 `_check`（`regress_traced.py`，上限 3600s）：所有路线都 unknown——lia 51s、quick+norm 3s、blast+norm 33s（查询超时）、potential+norm 317s、bvabs 97s、exact+norm 60s、mul 2×31s、unify / unify+norm 各 ~985s、补跑的 potential 941s。单独再给 blast+norm 一次 3600s 的求解仍是 unknown。`_check` 里每条路线拿的是**剩余节点预算的份额**（alias/guards 1/2、potential 1/3、其余平分），服务器上这条义务开始时节点还剩约 9h，所以它在各路线里耗了 6.6h 才由某一条（大份额的）路线证出。同一行里其余合取项单独都只要 15–22s（间隔 16 的那些 110–500s）。
- **按组证明（修法 17）**：前缀阶段之后，每个保留行 j（对应 EVM 路径 s）剩下的合取项 K 作为一个蕴含证明：`premise ∧ x_j ∧ ¬(∧_{k∈K} c_k)`。行 2 剩下 114 个合取项（含第 7 个）的组 **107s 证出**（blast+norm 37s），复跑一次（负载更重）112 个、238s 证出。对照：同一行全部 200 个合取项的组 300s 内 blast+norm / blast 都 unknown，第 7 个单独也一样——组里先反驳的兄弟析取项给了求解器第 7 个需要的事实（学到的子句）；这是经验观察，不是保证，所以失败时按下面的规则二分，留下的照常单独证明。行 0：119 个 128s，行 3：109 个 91s，行 4（含 4_7 等慢合取项）：104 个 119s；服务器上逐条分别是 1759s、1371s、3043s。
- 规则：组失败（sat / unknown / 超时）就对半分，最多分 3 层、最小 4 个；每次尝试上限 8 个查询超时（第一组还要为 lia 路线付 50–60s，之后 `_winners_first` 把 blast+norm 提前）；整个阶段用剩余预算的 1/3；剩下的义务走原来的逐条路径。每个成员的记录是组查询（改名为 `x86_maps_j_k`）及其引理，可以单独核对：组查询的文本里就是 `¬(… c_k …)`。
- **整节点**（`n4-6182-a`，提交 7a96003 的代码）：**proved，5166.0s**（墙钟 5383s），10087 个查询、0 失败，峰值 RSS 2.93GB（预算 5000MB）。x86 分段 + 覆盖 ~860s（`x86_coverage` 319s），前缀阶段 ~800s，35 个行组全部第一次就证出（46–92s，没有二分），另有 2 个行剩不到 4 个、逐条证明（`x86_maps_35_7` 115s、`x86_maps_41_0` 65s），`pair_93_2` 177.6s，`_unify_node` 29.9s。

### 2.5 PoolManager 4418

- 分叉（N3 §2.4）：每个符号长度的内存访问在 memgas summary 之前有两段只改寄存器的短菱形——`toWordSize` 的溢出钳位（`cmp rsi,rbx; jb BU64`，两边汇合于 memgas 入口前）和 `SafeMul(words, 32)` 的 `test rbx,rbx; je L`（跳过乘法；另一边 `mul rbx; jb ERR; mov rbx,rax`），执行器不合并，活路径数按访问点翻倍。
- **修法 18**（方向 (b)，`X86SymbolicExecutor._merge_diamond`）：一次条件分支产生两个可达后继时，先静态找两边沿静态后继各 4 个块以内最早共同到达的地址 J，再把两边按主循环完全相同的方式（`_advance`：执行、分叉时的可达性剪枝、CFG 边、终止状态记录）向前执行到 J（每边至多 8 个状态）；离开这片区域、到达 cutpoint、深度上限的状态原样交回工作表。若两边各恰好一个状态到达 J，且除寄存器/标志外状态的每个叶子都相同（`_state_leaves`：Z3 项按 AST id，含 assumptions、内存、gas、指针标签、标志约束），路径条件是 P ∧ T_a 与 P ∧ T_b 且 T_a ∧ T_b 不可满足，就合并为一个状态：路径条件 P ∧ (T_a ∨ T_b)，不同的寄存器/标志为 ite(T_a, a, b)。- **适用范围（两次收窄）**：
  1. 只在节点证明自己的 x86 分段（`BlockEquivalenceProver.prove` → `run_x86_segment(merge_diamonds=…)`）启用；summary 与归纳的原始代码重放（div / memgas 引理、复制循环归纳等）保持一条原始路径一条记录，因为它们的证书和检查按原始路径构造（第一版对所有 `run_x86_segment` 都开启，快测里 4 个引理路径数断言和 1 个复制归纳变异测试随之变化）。
  2. **自适应**：一次执行已有 200 条路径（终止 + 截断 + 待执行）之后才开始合并（`X86SymbolicExecutor._merging`；`BLOCK_MERGE_DIAMONDS=<N>` / `off`）。始终合并时，PoolManager 16670 m=768 的 x86 从 83 条变 73 条，每行都带合并点，SDIV 内存目标的 pair 明显变慢（`pair_2_65` 1.5h 仍未完成，服务器上同类 pair 140–520s；单独跑它的 goal 2，守卫路线因为 UF 参数里变成了 `ite(T, −a, a)` 而选不到守卫），6182 的复跑在前缀阶段之后 40 分钟没有进展（`cloud-inputs/n4/runs/*-mergeall-stopped.log`）：合并改变了状态的形状（寄存器是 ite、路径条件里有 Or），而各条路线是在原来的形状上调好的。200 高于那些不合并就能证出的分段（16670：83 / 109，6182：49），远低于 4418 的 878，所以这些节点与修法前完全相同，只有路径爆炸的分段改变形状。
- x86 分段（`mem_probe.py --x86-only`，sym 实例）：开启合并 **360 条路径**（342 终止 + 18 出口），合并 150 次，可达性检查 2563 次（1400s），分段 1606s（负载 6 个进程）；同一份代码、相近负载下关闭合并（`BLOCK_MERGE_DIAMONDS=0`）：878 条路径（806 终止 + 72 出口），可达性检查 6080 次（3394s，剪掉 1596 个），分段 3733s（N3 当时是 876 条、6105 次、2684s）。即路径 −59%（出口路径 72 → 18），可达性检查 −58%，分段 −57%。剩下的 342 条终止路径是各访问点的错误出口（溢出 / OOG 桩），它们彼此内存不同，不能合并。
- 整节点（`n4-4418-sym`）：（待补）

- **修法 21（与修法 18 的交互）**：合并后 6182 的 x86 路径从 49 条变成 46 条，`_correspondence` 的规模估计 `n·m ≤ n(n−1)/2 + 2m`（95·46 = 4370 ≤ 4557）于是退回全积，又会带回 `pair_63_2` 这类错配 pair（N3：单独 2121–2883s）。这个估计把 EVM 两两不交按每对一个查询计，但 `disjoint_groups` 是按分歧组反驳的（约 n 个），而修法 17 之后每个映射行约两个查询（行组 + pair）。修法 21 改为 `n·m ≤ 分歧组数 + 2m`。只决定走对应关系还是全积，两者的证书判定不变。

### 2.6 修法 19：`unify_across` 的停滞上限

服务器上 16670 两个实例的 `_unify_node` 各用 10816s / 10818s（节点预算的 1/4 份额全部用完），只得到 2 条引理，占节点时间的 85% / 55%。`unify_across` 现在在连续 10 个查询超时（300s）没有新的合并时停止；没合并的 pair 照常走自己的路线（包括它自己的 unify 路线），所以只影响耗时。整节点 16670 m=768（`n4-16670-m768`）：（待补）

### 2.7 修法 22–26（10-30 补充）

- **修法 22**（`_retry_over_lia`）：lia 路线的 limb 拼接引理（`split_limb_joins`，每个 1s 查询，最多 4 轮）不看路线截止时间，在 6182 的宽行组上一次调用 50–60s，不管分到的份额多小。现在每个拼接查询前检查 `self.deadline`，到点即返回 unknown（只影响耗时）。
- **修法 23**（x86 可达性 / summary 入口的 Z3 内存上限，`x86_64/cfg_state.py`）：PoolManager 22747（3G 进程池被 OOM 整池打断的节点之一）在 DIV summary 之后的一次可达性检查里 5s 内 +1.5GB，随后 10s 内再 +2.3GB；之后 summary 命中的入口 SAT 检查也一样。Z3 的求解器参数 `max_memory` 在增量求解器（`PrefixSolver`，每个合取项一个 push）上被忽略，`interrupt()` 在 bit-blast 里几十秒后才生效，所以改用 Z3 的进程级 `memory_max_size`，只在检查期间设置（`z3_memory_cap()`：当前 Z3 已分配量 + 1024MB，嵌套时取更小者，退出时恢复）。超出时 Z3 抛 "out of memory"（或非增量求解器返回 unknown，原因 "out of memory"），之后 Z3 照常可用（实验：同一求解器 reset 后、新求解器、旧的项都正常）。用在：`is_possible` 整个检查（见证求值、增量求解、blast 回退）、`_bounded_check`、summary 命中入口的 `_sat_model` 与其 blast 重试。内存超限 = unknown：可达性检查保留路径（并 reset 增量求解器），入口检查算未决（`apply` 原本就这样处理 unknown）。22747 复跑：x86 分段峰值 ≤1.85GB（之前几秒内 +2GB），进入 pair 阶段。**已知局限**：同一个 512 位除法查询若拆成每个合取项一个 push 作用域，Z3 要到 ~30s / +2.7GB 才报超限（smt 内核的某些部分很晚才检查上限），所以上限是"大致"的，节点内存预算仍是兜底。
- **修法 24**（`_correspondence` 的 blast 回退）：4418（自适应合并后 497 行 x86）在 `_correspondence` 的 blast 回退（修法 11）里花了 ~3400s：每个 unknown 行 30s + 120s 重试。现在 unknown 行先放到第一遍之后；一行如果同类型同位置的兄弟行已经映射，就留给 `propose_from_siblings`（与修法前对回退后仍 unknown 的行的处理相同），只有没有已映射兄弟的行才做 blast 回退。对应关系只是提议，不影响证书判定。
- **修法 25**（路径覆盖按前缀树证明，`coverage_by_prefix_tree`）：见 §2.8 21213。
- **修法 26**（单个证明查询的 Z3 内存上限）：`solve_query` 与 `solve_pure_bv` 在 `z3_memory_cap(QUERY_MEMORY_MB)` 下求解（`BLOCK_QUERY_MEMORY_MB`，默认 4096）。触顶的查询是 unknown，并且**不写进 proof cache**（它不是"这个预算下超时"）；义务照常走其余路线。22747 的 pair 阶段在 `solve_query` 里几秒内涨了数 GB（栈采样 `tri-22747.stacks`）。

## 3. 改动位置

- `common/node_monitor.py`（新）：`NodeMemoryExceeded`、`check_abort`、`rss_bytes`、`release_memory`、`NodeMonitor`、`read_status`。
- `verification/block_parallel.py`：`load_worker` 读取 `node_memory_mb` / `status_dir`；`forget_summary_failures`、`prove_instance`（监控外壳）/ `_prove_instance`；`WorkerDied`、`_pool_worker`、`NodePool`；`_prove_all` 改用 `NodePool`、处理 `WorkerDied`、不重试内存失败、`result.running`；`_OBSERVED`、`_record`。
- `verification/block_program.py`：`BlockProgramResult.running`。
- `tools/verify_block_lockstep.py`：`--node-memory-mb`、`--status-dir`，progress 带 `running`。`tools/probe_block_obligations.py`：`probe_node` 的监控与 `--node-memory-mb`。
- `verification/block_equivalence.py`：`check_abort` 接入 `_solver`、`solve_query`（求解后再查一次，被中断的 unknown 不进 proof cache）、`solve_pure_bv`；修法 17 `_ROW_GROUP_*`、`_pair_phase` 中调用、`_prove_row_groups`、`_group_trial`；修法 19 `unify_across(stall_seconds=)` 与 `_unify_node` 的调用。
- `x86_64/cfg_executor.py`：`check_abort` 接入 `execute_state`；修法 18 `merge_diamonds` 参数、`_merging`、`_advance`（主循环的单步，提出来复用）、`_diamond_join`、`_merge_diamond`、模块级 `_state_leaves`、`_exclusive`、`_merged`、`_DIAMOND_BLOCKS` / `_DIAMOND_STEPS`。
- `verification/loop_induction.py`：`run_x86_segment(merge_diamonds=None)` 参数；`verification/block_equivalence.py` 的 `prove` 以 `_MERGE_DIAMONDS`（`BLOCK_MERGE_DIAMONDS`，默认 200）传入。
- `verification/block_equivalence.py`：修法 21 `_correspondence` 开头的规模估计（先算 `disjoint_groups`）。
- `verification/block_summaries.py`：修法 16 `summary_text`，用于所有 summary 命中义务的记录。
- `common/store_forwarding.py`：修法 20 `_SHARED_FORWARD_LIMIT = 25_000`、`forward_selects_shared` 不再自清、`shared_forward_scope`；`x86_64/summaries/div.py`：`apply_div_summary` 开头开一个作用域。
- 测试：`tests/unit/test_block_node_isolation.py`（新，8 条）、`tests/unit/test_block_remaining_blocks_4.py`（新，修法 16–20）、`tests/unit/test_block_correspondence.py`（§2.1）。
- 工具：`cloud-inputs/n4/tools/`（§7）。

## 4. 健全性论证

- **节点内存预算 / 进程池（第 2 项）**：只会让证明停下来。中止标志只在求解器调用和执行器步进处抛 `NodeMemoryExceeded`，它是 `BaseException` 的子类，所以途中任何 `except Exception`（summary 回退、"试一下这个改写"之类）都接不住它，不会把它变成某个答案；节点被报告为 inconclusive，不产生定理。被中断的 Z3 调用返回 unknown，`solve_query` / `solve_pure_bv` 求解后再查一次标志，所以这个 unknown 不会写进 proof cache；进程内 summary 切片证明的失败缓存在超预算节点之后清空（`forget_summary_failures`，纯缓存，只会重新证明）。`WorkerDied` 的节点同样只是失败/未证；被换掉的 worker 不带任何状态进入新节点。证书的判定没有任何改变。
- **修法 16**：只改义务记录里的文本字段，换成的指纹与 `slim()` 交给父进程的完全一样（测试 `test_hit_certificate_keeps_names_and_answers_and_slim_keeps_the_fingerprint`）；名字、答案、预期、引理都不变，证书完整性判定（`SummaryHitCertificate.complete`、`Obligation.proved`）不读文本。
- **修法 17**：成员义务 `premise ∧ x_j ∧ ¬c_k` 的每个模型都满足组查询 `premise ∧ x_j ∧ ¬(∧_{k∈K} c_k)`（¬c_k 蕴含合取的否定），所以组查询是每个成员的弱化：组 UNSAT ⟹ 每个成员 UNSAT，与修法前已有的 `_prove_stuck_groups`（前缀组）同一论证。组的记录（改名后）就是被反驳的组查询加上反驳它的引理，`_check` 对它的路线与任何义务相同；组 sat / unknown / 超时不产生任何记录，成员留给自己的义务。合取项的下标用的是 `_check_rows` 命名 `x86_maps_j_k` 时同一个 `_conjuncts` 顺序（测试中特意检查了反向顺序下真假成员的归属）。
- **修法 18**：合并只在两个状态位于同一地址、除寄存器和标志外每个叶子都相同、路径条件为 P ∧ T_a 与 P ∧ T_b 且 T_a ∧ T_b 不可满足时进行（T_a、T_b 的第一个约束是同一分支的两边：语法上互补，或 simplify 为 false，或 200ms 内被求解器反驳；否则不合并）。合并后路径条件 P ∧ (T_a ∨ T_b)、寄存器 ite(T_a, a, b)：任一模型若满足 T_a，合并状态在这个模型下就是 a；若满足 T_b（此时 T_a 必假），就是 b——所以合并状态的执行集合恰好是 a 与 b 的并集，不增不减，覆盖和有限执行都不变。见证模型取某一边的（它满足那一边的路径条件，因而满足合并后的），使用前照常求值确认。两边状态是用主循环同样的单步函数执行的；没到 J 或不满足条件的状态原样交回。测试：合并后的 rcx 在全部输入上等于程序语义（求解器验证），路径条件覆盖全部输入；一边写内存的菱形不合并。
- **修法 21**：对应关系只是提议（原有约定，见 `_correspondence` / `_pair_phase`）；走全积还是走对应关系由一个规模估计决定，两条路的定理都由 `BlockTheorem.complete` 按各自的清单判定，估计值只影响耗时。
- **修法 19**：只是更早停止一个预处理；`unify_across` 返回的每条引理和改写与之前一样由被反驳的查询支持，没合并的 pair 原样留下（测试：停滞为 0 时不做任何改写）。
- **修法 20**：`forward_selects` 对每个结点是纯函数，缓存保活所有键结点（id 不会复用），只在作用域边界整体清空——清空后结果与新缓存相同（测试：作用域内大小不受限，跨作用域超过上限即清空，清空后结果不变）。只影响耗时和内存。

## 5. 测试结果

（待补：全量快测）

- 新测试按节点 ID 单独跑过：`tests/unit/test_block_node_isolation.py` 8 条，`tests/unit/test_block_remaining_blocks_4.py`（待补）条。
- `tests/integration/test_block_parallel.py` 7 passed（新进程池）；`tests/integration/test_block_constant_insensitive.py` 中 `test_muti_block_verifies_with_fewer_proofs`（`slow`，空闲机器 ~11 min）在 5–6 个进程的负载下 H2 预算耗尽，**基线提交 7b1e121 在同样负载下也失败**（两个节点 H2 预算耗尽），属于负载问题；空闲时复跑：（待补）。

## 6. 离线验证数据（`cloud-inputs/n4/runs/`）

（待补：整节点汇总表）

## 7. 诊断工具（`cloud-inputs/n4/tools/`，仅用于诊断）

- `run_probe.sh`：整节点（同 N3，输出到 `cloud-inputs/n4/runs/`，后台运行，pid 写到 `TAG.pid`）；`rss_log.sh`：每 5 分钟记录一次整节点进程的 RSS / 峰值（`TAG.rss`）。
- `mem_probe.py` / `run_mem.sh`：§2.3 的内存采样（`--x86-only`、`--reset-prefix N`、`--forward-limit N` 两个实验开关，x86 分段结束时打印路径数、合并次数、可达性检查）。
- `row_group.py`：在 dump 目录上对某些行做前缀阶段 + 组证明（`--split` 另外逐条计时）。
- `single_vs_group.py`：单个合取项 vs 行组的 normalize 与 blast 求解对照。
- `regress.py`：同 `cloud-inputs/n/tools/regress.py`，名字含 `_entry_` 的（summary 命中入口）也按预期 SAT。

## 8. 未解决的问题

（待补）
