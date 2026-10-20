分支：`claude/m-hard-blocks-46hta8`（会话只允许推送 `claude/...` 分支，未使用任务书建议的 `cloud/hard-blocks`）。基线 = `cloud/inputs-m`（3cfa00e）。

# 任务 M：Permit2 1327 / 8750 与 Aave 8248 —— 根因与通用修法

## 1. 结论

**没有任何 SAT。** 任务列出的义务全部成立：1327 `x86_maps_0_46`（两个实例）和 Aave `pair_0_1` 已在本机证出（UNSAT），8750 的 H2 出边已逐条闭合（见 §2.3）。没有出现反例，所以不需要做具体执行，也没有编译器问题。

| 合约 | 块 / 实例 | 义务 | 成立？ | 根因 | 修法 | 修法前 | 修法后（本机） |
|---|---|---|---|---|---|---|---|
| Permit2 | 1327 d10 符号 | `x86_maps_0_46` | 成立（UNSAT） | EVM 合取项 46 是 **SSTORE 的 gas 检查**（三层 keccak 槽位上的 `host_gas_sstore`、`host_gas_sload`，再减去各次内存扩展费）。x86 侧对应 x86 路径的第 32 个合取项。x86 的哈希输入在 `sha3_slice` 的 lambda **内部**经 R15 偏移视图 `λa. M[a−R15]` 读内存（在 `R15+o` 处 store，在 `R15+o+i` 处读）；EVM 读的是 `M[o+i]`。`normalize_word_arith` 本来就有把偏移视图改写成 EVM 偏移的规则，但它的各轮改写**从不进入 binder**，所以两侧的哈希参数始终没有碰面，所有路线都 unknown | **修法 1：lambda 体规范化**（`_normalize_lambdas`） | 服务器 4025s unknown；本机 route_trace 1800s unknown（所有路线失败） | **96.6s proved**（`blast*` 本身 0.36s） |
| Permit2 | 1327 d10 m=192 f=128 | `x86_maps_0_46` | 成立 | 同上 | 修法 1 | 服务器 6352s unknown | **85.8s proved**（`blast*` 0.41s） |
| Aave Pool | 8248 d17 m=352 | `pair_0_1`（exit@8414 / exit@539522） | 成立 | 块内一次 DELEGATECALL。EVM 路径 0 = 调用失败（转到 8414 的 revert），x86 路径 1 = 调用成功。两侧调用的是同一个 UF `evm_delegate_call_8406`，7 个参数中 2 个语法相同，其余 4 个（gas、in_offset、in_size、内存数组）是**同一个值的不同写法**：x86 把和的低字节单独求和（`Concat(s[63:8], s[7:0]')`），内存经 R15 视图。逐对规范化后，这 4 对都是**恒等式**（不需要任何前提）。但现有路线都证不出：整式规范化会先用路径条件判定 ite 守卫，结果把 EVM 的 gas 字变成了字节拆分形式（`low8 == Extract(7,0,S)`，17 个加数，60s 也是 unknown），两侧依然对不上；`_prove_equal` 在带前提的查询上每对用掉 128s，仍是 unknown | **修法 2：恒等参数合并**（`unify_identities`，节点级和 unify 路线各用一次） | 服务器 5325s unknown；本机 route_trace 1801s unknown | **71–79s proved**（合并 68–79s，合并后的 `_check` 0.1–0.2s） |
| Permit2 | 8750 d11 符号（上下文 (5,3940)） | H2 出边闭合 | 成立（已闭合的出边全部 UNSAT，没有失败的部分） | **不是筛选问题，也不是不成立。** 12 条出边（EVM 路径 0/1 各自对 6 条 x86 路径），每条要证约 22 个合取项。昂贵的合取项在多条出边之间是**同一个项**：`memory_0`、`return_data_source_1/2` 每 2 条出边共用一个，`memory_size_0`、`memory_gas_0/1`、`gas_0` 每 6 条共用一个；这些出边的 base 只差分支字面量（STATICCALL 成败、CALLDATACOPY 长度落在哪个区间）。原代码按出边逐条重证。另外 H2 部分的路线类名带着出边下标（`H2_c0_0_5_t1_memory`），所以前一条出边上赢的路线，到下一条出边不会先试。最慢的是 "CALLDATACOPY 长度在 calldata 内" 那两条出边上的 `memory_0`（单条 2273s，只有最后的直接查询能证出） | **修法 3：共用合取项按公共 base 只证一次**（`shared_bases` + `close_edge(shared=...)`）；**修法 4：路线类去掉出边下标** | 旧代码前 3 条出边 555.6 / 577.8 / 2901.1s（合计已 4034s；12 条出边串行，加上服务器 3 实例并行，耗尽 21600s） | **12/12 出边闭合，合计 4910.6s**（§6.3） |
| Permit2 | 8750 d11 (0,0) / d15 (0,0) | H2 | 未在本机单独跑 | 结构与 d11 符号相同（同一块、同样的 STATICCALL / CALLDATACOPY 分支） | 修法 3、4 同样适用 | 服务器 c0_budget exhausted | 待服务器全量验证 |

补充说明：

- 1327 符号实例中，前缀 pass 没有消掉的 maps，除了 `0_46` 还有：第 0 行和第 4 行各 63 条（0..5、9..50、56..60、81..85、106..110），第 38 行 15 条，第 39 行 10 条，第 40 行 5 条，以及 42、43、54、59 行各 1–2 条。服务器上这些是按 0_0、0_1、…… 的顺序逐条跑的，`0_46` 是第一条失败的，**它后面的都没有尝试过**。修法 1 之后，整节点结果见 §6.4。
- 1327 m=192 f=128 实例：前缀 pass 没消掉的有 347 条（第 0、3、41、42、43 行各约 60 条）。
- 任务 L 的 1327 `x86_maps_0_0` / `0_1`（812s / 840s）在修法 1 之后是 **82.4s / 58.5s**：lambda 规范化同样让三层 `sha3_slice` 碰面了。
- 1327 符号实例整节点（本机串行，21600s）：**所有 `x86_maps` 都通过了**。节点预算耗在两条服务器从未跑到的 all 行 pair 上：`pair_0_6` / `pair_0_7`，x86 在 SSTORE 一类的 gas 检查上 OOG，EVM 正常退出。两条都是 unknown，不是 SAT。这是新暴露出来、尚未解决的问题，见 §6.4、§8。

## 2. 逐块分析

### 2.1 Permit2 1327 `x86_maps_0_46`

- **来源**：块 1327 = `CALLER MSTORE … SHA3 … SHA3 … SHA3 … SLOAD AND SSTORE … LOG2`（三层嵌套映射，`allowance[owner][token][spender]`）。EVM 路径 0 的合取项 46 是 `ULE(SSTORE 费用, gas_remaining − 247 − 各次内存扩展费 − host_gas_sload(L3) …)`。费用里有 `host_gas_sstore(sha3_slice(L3…), …)`，L3 的 lambda 体里有 L2，L2 的 lambda 体里有 L1。x86 侧对应 x86 路径 0 的合取项 32（同样的 gas 检查，写成 65 位借位形式）。
- **同形比较**（`l2diff`：逐层找出 `sha3_slice` 参数中最小的不同叶子）：在 unify 已经合并 L1、L2 的公式上，x86 实际使用的那条链（L2b，60594 字节）和 EVM 的 L2 相比，有 130 个不同叶子，全部是 `M` 对 `λa. M[a−R15]`、`p` 对 `R15+p`、`p+k` 对 `R15+p+k`。也就是说，**同一份内存只是坐标系不同**。
- **为什么路线全部失败**：`_offset_view_select`（normalize 的改写规则）能把 `Select(λ视图上的 store 链, R15+c)` 改写成 `Select(去掉偏移的链, c)`，但 `normalize_word_arith` 的遍历遇到量词就停（`not is_app(t)`）。哈希的输入恰好在 `sha3_slice(λi. …)` 的 lambda 体里，所以永远没有被改写。unify 只能配对顶层（binder 外）的 UF 应用，于是只剩 L3 对 L3，而 L3 的相等又依赖内层的 L2、L1。
- 顺带确认：x86 侧有**两条** L3 链。有 `host_gas_sstore` 的真实 gas 检查（x86 合取项 1/11/19/27）用的是 L3b；只出现在 host-gas 上界公理里的是 L3a。任务 L 说的"死公理"链，在这条义务里不是死的。
- **验证**：先做 lambda 规范化，再做 normalize、blast，查询 0.3–0.4s 就是 unsat（不做 canon 的版本也是 0.4s）。生产 `_check` 走的是 `blast*` 路线。

### 2.2 Aave 8248 `pair_0_1`

- **来源**：块 8248 构造 calldata（11 次 MSTORE，从 fmp=`mload(0x40)` 起），执行 `GAS DELEGATECALL ISZERO DUP ISZERO JUMPI 8421`。EVM 路径 0 = 返回 0，落到 8414（`RETURNDATACOPY … REVERT`）。x86 路径 1 = 调用成功，退出到 539522（8421）。两边的出口不同，所以 `pair_0_1` 的目标是 `Or()`：联合路径必须不可满足。
- **同形比较**（`aave_args` / `congr` / `joint_norm`）：`evm_delegate_call_8406` 的 7 个参数中，arg1（地址常量）、arg5（out size 0xc0）语法相同；arg2 和 arg4 在各自一侧是同一个项。差别全在写法上：
  - x86 地址：`0x1e + Concat(Extract(63,8, 0xe4+fmp), 0xe4 + fmp[7:0])`，EVM 地址：`0x102 + fmp`；
  - 内存参数：两侧都是 416 个 store、同一顺序、同一个 base，只是地址和值的写法不同；
  - gas 参数：x86 = `Concat(0, S[63:8], 低字节单独求和)`，EVM = `Concat(0, S)`。
- 逐对 `normalize_word_arith(x == y)`：arg0 11.2s，arg2 50.0s，arg3 64.6s，arg6 38.4s，结果**都是 `True`（恒等式）**。四对合在一次规范化里只要 68.1s（共享子项只改写一次）。
- **为什么路线全部失败**：`_prove_equal` 在 128s 内对每对都是 unknown，blast 只证出 arg2/arg3（19s/37s），arg6 的 blast 300s 仍是 unknown。normalize 路线规范化的是整条公式（140s）：它会用路径条件判定 ite 守卫，判定之后 gas 字在 **EVM 侧**变成了字节拆分形式，需要的拼接恒等式 `low8 == Extract(7,0,S)`（17 个加数，含 bvmul 和 ite）在 1/10/60s 内都是 unknown。于是 4 对参数里有 3 对合上了，gas 那对没有合上。

### 2.3 Permit2 8750 H2

- **复现**：`discover`（1576 个实例，200s）→ `load_worker` → `prove_instance`，节点的 pair 阶段跳过（H2 不读 pair 记录；只用于诊断）。`close_edge` 的每个部分都打了耗时记录，脚本见 §7。
- **出边**：proof instance d11 符号只有一个上下文 `(5, 3940)`（服务器上的 `c0`）。共 12 条出边：(0,1)(0,3)(0,5)(0,7)(0,9)(0,11)(1,0)(1,2)(1,4)(1,6)(1,8)(1,10)，目标是 pc 8910 / 9128 的各 7 个实例。t0 被屏蔽（`stack_constant_predicate` 筛掉），实际要证的是 t1。
- **逐合取项记录（旧代码）**：

| 出边 | 合计 | memory_0 | memory_size_0 | memory_gas_0 | memory_gas_1 | gas_0 | return_data_source_1 | return_data_source_2 |
|---|---|---|---|---|---|---|---|---|
| (0,1) | 426s（close 555.6s） | 169.5 | 7.9 | 81.6 | 12.4 | 49.2 | 69.7 | 30.5 |
| (0,3) | 442s（577.8s） | 183.6 | 8.4 | 82.0 | 10.9 | 49.4 | 69.5 | 33.0 |
| (0,5) | 2768s（2901.1s） | **2272.7** | 8.3 | 86.2 | 11.0 | 49.2 | 170.8 | 163.2 |

  其余每条出边约 22 个小合取项，各自 <1s。没有任何部分失败：**这个目标本来就应该匹配，义务成立，只是难证。**
- **(0,5) 为什么慢**：x86 路径 5 = CALLDATACOPY 的长度高位全为 0，且 `len ≤ CallDataSize`（复制落在 calldata 内）。`memory_0` 是 `λ_EVM == λ_x86`（125KB 对 3.4MB）。规范化之后，剩下的差别是复制区间的写法：EVM 用 `ULT(i − dst, len)` 加 `min(src, CDS)` 夹取，x86 用 `i < dst + len`。两者只有在不溢出时才相等，要靠前提，所以不是恒等式。新代码下这一条 2581.6s 证出，所有路线都失败，最后靠收尾的直接查询（756s）。单独试过的策略中，blast 过的规范式直接解 578s 可以证出；原始直接查询 1500s 是 unknown。
- **共用情况**（按 AST 摘要比对 12 条出边的目标合取项）：`memory_0`、`return_data_source_1/2` 的等价类是 {(0,j),(1,j−1)}，每类 2 条出边。`memory_size_0`、`memory_gas_0/1`、`gas_0` 是 {(0,1),(0,3),(0,5),(1,0),(1,2),(1,4)} 和另外 6 条两类。同一类内各条出边的 base 只差 2–6 个分支字面量（公共部分 166–168 / 171–172）。
- 公共 base 上离线证一次的结果：`gas_0` 一次覆盖 6 条出边，50.1s（原来每条约 49s，6 条约 295s）；`return_data_source_1` 覆盖 2 条，119.1s；`memory_0` 覆盖 (0,1)/(1,0)，188.9s。

## 3. 改动位置

- `verification/block_equivalence.py`
  - **修法 1**：`_normalized_lambda` L945、`_normalize_lambdas` L965。`normalize_word_arith` 在各轮改写之前先调用它，见 L1010。
  - **修法 2**：`_constant_names` L2528、`unify_identities` L2545。`_unify_node` 在 `unify_across` 之前调用（L3436，上限 4 个查询超时）。`_retry_with_uf_unification` 先做恒等合并，合并后先跑一次 quick 查询，再把原来的流程交给新拆出来的 `_unify_and_split`（L3744、L3758、L3771；上限也是 4 个查询超时）。
  - **修法 4**：`_route_class` L1838，正则改为 `_[ct]?\d+(?=_|$)`。
  - import 增加 `BoolSort`。
- `verification/block_parallel.py`
  - **修法 3**：`shared_bases` L261。`close_edge(..., shared=None)` L291；共用检查在 L399，位于原有的无前提尝试和合同性拆分之后、`hard.append` 之前。`prove_instance` 为每个上下文建一个 `shared`，见 L498。
- 测试：`tests/unit/test_block_hard_blocks.py`（新增 16 条，其中 1 条 slow）。
- 数据：`cloud-inputs/m/smt2/`（新增）：`permit2_1327_x86_maps_0_46.smt2`、`permit2_1327_m192_f128_x86_maps_0_46.smt2`、`aave_8248_pair_0_1.smt2`，都是按 `_check_rows` 的做法（`forward_selects` + `canon_binders`）从本机重建的义务。

## 4. 健全性论证

- **修法 1（lambda 体规范化）**：对 `t = λi. b`，取新常量 k，对 `hold(b[i:=k])` 做 `normalize_word_arith`，得到 `hold(b')`，其中 `hold` 是一个新的 Bool 值 UF。
  - normalize 的每条改写 `old → new` 都由 `_identity_proof` 证明，且证明时 UF 应用、乘积都是不透明的，所以对 k 的任意取值都成立。由于 k 在其中是自由常量，`b[i:=k] = b'` 是有效式。按外延性，`λi. b = λk. b'`。
  - `hold` 是新的 UF，也不是 ite 守卫，`_join_and_decide` 不会拿它判定任何东西，所以只有项被改写，判定不会混进来。
  - 内层 lambda 在递归时作为 body 的一部分规范化。结果做 `canon_binders`，只是 α 改名。
  - 每次 lambda 改写记为一条 `normalize_<n>_lambda` 引理，内层的改写引理作为它的子引理。没有一条改写被证出时，返回 None，原 lambda 保持不变（fail-closed，有测试 `test_lambda_rewrite_needs_the_inner_proofs`）。
  - 所以 F' ≡ F，与原有的 normalize 一样，只是作用范围扩大到了 binder 内部。
- **修法 2（恒等合并）**：设 G = ∧_k (m_k ⇒ x_k = y_k)，m_k 是新的 Bool 常量，`normalize_word_arith(G)` 返回 N ≡ G。若 m_k 不在 N 中出现，那么 x_k = y_k ≡ G[m_k:=⊤, m_j:=⊥] ≡ N[m_j:=⊥] ≡ G[全部 :=⊥] ≡ ⊤。这一步用到了"m_k 不出现在 N 中"，因此 N 在 m_k 上取 ⊤ 还是 ⊥ 都一样。于是 x_k = y_k 是**有效式**，不依赖任何前提。
  - 对任意公式 F 都有 F ≡ F[big:=small]，节点里的所有兄弟 pair 都可以直接改写。
  - deadline 只会让改写变少：N 仍然 ≡ G，只是消失的 m_k 变少。
  - 有前提才成立的相等不会被当作恒等式（测试 `test_premise_equalities_are_not_identities`）。
  - 记录：一条 `unify_identities_<n>` 引理，子引理是 normalize 的全部改写证明。改写过的 pair 带上 node lemmas，与原有的 `unify_across` 相同。
- **修法 3（共用合取项）**：公共 base C 的每个合取项都是各出边 base 的合取项（按 AST id 求交集），所以 base_n ⊨ C。C ∧ ¬c 不可满足，就推出 base_n ∧ ¬c 不可满足，c 在每一条出边上都成立。
  - 共用证明失败（sat、unknown 或超时）时记为 None，各出边退回自己的 base，与原来完全一样。
  - 出边记录的 lemmas 里放的是这条共用记录，其中的查询是一个弱化。`EdgeCertificate` 的消费方只检查 `obligation.proved`，判据不变。
- **修法 4（路线类）**：`_winners_first` 只改变路线的尝试顺序，每条路线仍然要自己反驳 F，所以只影响耗时，不影响结论。
- 没有"提议"出错就会误证的通道：merge 的候选、共用的候选、路线顺序都只是提议，所有结论最终都落到被反驳的查询上，或者落到被证明的恒等改写上。

## 5. 测试结果

- 新增 `tests/unit/test_block_hard_blocks.py`，16 条，逐个按节点 ID 单独运行都是 1 passed，确认都被收集到了。耗时：两条用真实 SMT2 的测试分别是 27.7s（1327 0_46）和 81.4s（Aave，标记为 `slow`），其余都 <0.4s。
  - 修法 1：EVM 读 `M[p+i]` 与 x86 在 `λa.M[a−R15]` 上 store/读 `R15+p+i` 的哈希，规范化后合为一个项；去掉 lambda 这一步就合不上（证明这个修法是必要的）；嵌套 lambda 也能处理；输入不同时不会合并；内层证明全部失败时 fail-closed；1327 0_46 真实 SMT2 的 blast 规范式 unsat。
  - 修法 2：字节拆分的和合并后，"一个失败、一个成功"的矛盾变成语法上的矛盾；只在前提下才成立的相等不合并；只合并是恒等式的那几对；节点级会改写所有兄弟 pair；unify 路线也会用到；Aave pair_0_1 真实 SMT2（slow）。
  - 修法 3、4：H2 部分名的路线类；`shared_bases` 取公共合取项，且每个 base 都蕴含它，只有一条出边时为空；`close_edge` 对共用合取项只调用一次 `_check`；公共 base 太弱时退回逐出边，结果仍然证出。
- 全量快测 `pytest tests/unit -m "not slow" -p no:cacheprovider`：**1747 passed, 3 skipped, 0 failed**。基线是 1732 passed；中间只含修法 1、2 时是 1743 passed。

## 6. 离线验证数据（本机：4 核，z3 4.15.4，每查询 30s，多任务并行，耗时偏高）

### 6.1 单条义务（生产 `_check`，route_trace，每条 1800s）

| 义务 | 修法前 | 修法后 | 获胜路线 |
|---|---|---|---|
| 1327 符号 `x86_maps_0_46` | 1800.5s unknown（所有路线失败；服务器 4025s） | **96.6s proved** | blast*（0.36s；其前的 lia 52s 与 normalize 26s 照旧） |
| 1327 m192 f128 `x86_maps_0_46` | 服务器 6352s unknown | **85.8s proved** | blast*（0.41s） |
| Aave 8248 `pair_0_1`（节点级合并 + `_check`） | 1801.4s unknown（服务器 5325s） | **71.4s + 0.2s proved**（另一次 78.9s + 0.1s） | 合并后 quick |
| Aave 8248 `pair_0_1`（只走 `_check`，不经节点级合并） | 同上 | 见 §6.5 | unify |

### 6.2 回归：任务 L 的 SMT2（`check_obligation.py`，修法 1–2 之后）

| 义务 | 任务 L 报告 | 现在 |
|---|---|---|
| 4837 `x86_maps_12_0` | 23.9s proved | 23.8s proved（68 lemmas） |
| 4837 `x86_maps_14_0` | 13.7s proved | 14.1s proved |
| 1327 `x86_maps_0_0` | 812.1s proved | **82.4s proved** |
| 1327 `x86_maps_0_1` | 839.6s proved | **58.5s proved** |

### 6.3 8750 d11 H2（`h2_probe.py`，跳过 pair 阶段，单上下文 (5,3940)，串行）

| 出边 | 修法前 close_edge | 修法后 close_edge | 修法后各部分合计 | 说明 |
|---|---|---|---|---|
| (0,1) | 555.6s | 504.9s | 374.1s | 共用证明（memory_0 144.9、gas 45.1、memory_gas 50.8+10.4、return_data_source 74.0+31.9）都记在这条出边上 |
| (0,3) | 577.8s | 302.9s | 171.1s | memory_size / memory_gas / gas 复用 |
| (0,5) | 2901.1s | 2806.2s | 2678.3s | `memory_0_shared` 2421.6s（这一条同时覆盖 (1,4)） |
| (0,7) | —（旧跑在 3 条出边后中止） | 233.6s | 111.5s | 第二组 memory_size / gas 的共用证明 |
| (0,9) | — | 159.4s | 40.0s | |
| (0,11) | — | 155.9s | 39.4s | |
| (1,0) … (1,10) | — | 122.9–126.9s（6 条） | 1.2–8.3s | 昂贵的合取项全部复用；剩下约 120s 是 `close_edge` 的屏蔽和无前提尝试 |
| **合计** | 前 3 条已 4034s；按每条 EVM 路径各有一条慢出边估算，12 条 ≥ 11000s（服务器 3 实例并行，耗尽 21600s） | **4910.6s，12/12 闭合，reasons 为空** | | 60 个部分中 36 个走共用证明 |

修法 4 的效果混在上表里，没有单独拆出来：路线类名改为 `H2_memory` 等之后，第一条出边上赢的路线（`blast*`），在后面的出边上会先试。(0,7)/(0,9)/(0,11) 的 `memory_0_shared` 只要 12.7–14.3s，其中有多少来自路线顺序、多少因为这几种复制情形本身就容易，本次没有分开测。修法 1 让 (0,1) 的 `memory_0` 从 169.5s 降到 148.1s（单独 route_trace）。

### 6.4 整节点（`probe_block_obligations.py --timeout-ms 30000 --node-seconds 21600 --keep-going`，串行，修法 1–2，`BLOCK_SUMMARY_LEMMAS=1 PYTHONHASHSEED=0`）

| 节点 | 结果 |
|---|---|
| Permit2 1327 d10 符号 | 21722s 用完节点预算，inconclusive。**没有任何 `x86_maps` 失败**（2064 个查询，EVM 61 条路径 / x86 65 条路径，233 个 terminal 已证）。keep-going 记下两条 unknown：`pair_0_6`（5925s）和 `pair_0_7`（1943s），都是 `exit@1273 / terminal@75335`。这两条在服务器上从来没有被尝试过，因为节点在 `0_46` 就停了 |
| Aave 8248 d17 m=352 | 本机**被内存 cgroup 的 OOM 杀掉**（约 6.6h 时 RSS 6.6GB，dmesg：`Memory cgroup out of memory: Killed process … (python)`），没有输出。单条义务上的结论见 §6.1、§6.5。整节点要在服务器上验证 |
| Permit2 1327 m=192 f=128 | 本机在报告提交时还没有跑完（与上面两个节点并行），未纳入 |

`pair_0_6` / `pair_0_7` 是 all 行（correspondence 提议为 all）：x86 路径 6、7 等于 x86 路径 0 的前缀加上**最后一个 gas 检查取反**（181KB 的合取项，含三层 `sha3_slice` 和 `host_gas_sstore`），即 x86 在 SSTORE 一类的检查上 OOG，而 EVM 路径 0 的所有检查都通过。这和 `x86_maps_0_46` 是同一个 gas 等价关系，只是方向相反（EVM 通过 ⇒ x86 通过）。本机试过：整条公式做 lambda 规范化 + blast，120s unknown；单独拿 EVM 合取项 0/9/17/46 与 x86_6 求合取，各 60s unknown。公式已存为 `cloud-inputs/m/smt2/permit2_1327_pair_0_6.smt2`，见 §8。

### 6.5 其他

- Aave `pair_0_1` **只走 `_check`**（不经节点级合并，模拟 x86_maps 或 H2 部分这类不走 `_unify_node` 的义务）：修法前 1801.4s unknown，修法后 **1227.9s proved**。获胜路线是 `unify`（plain，73.4s），恒等合并后 quick 即可证出。之所以这么晚，是因为 `unify` 在路线表的最后。生产里 pair 会先经过 `_unify_node`，那一步就能合并（79s）。
- 8750 (0,5) 的 `memory_0`：新代码 route_trace 2581.6s proved。路线全部失败，收尾的直接查询 756s 证出。单独试过：blast 过的规范式直接解 578s unsat，未规范化的直接查询 1500s unknown。

## 7. 诊断工具（`cloud-inputs/m/tools/`，仅用于诊断，供服务器复现）

- `capture_pairs.py STEM NODE.json OUTDIR`：跑到 pair 阶段为止，导出 premise、每条路径条件、correspondence、前缀 pass 与卡住组的结果（`meta.json`）以及各个 pair 的 SMT2，然后中止。用 `CAPTURE_ONLY=<正则>` 限定导出哪些 pair。`build_maps.py CAPDIR J K|all OUTDIR` 再按 `_check_rows` 的做法重建 `x86_maps_J_K`。
- `h2_probe.py STEM PC DEPTH CONSTS OUTDIR [--skip-pairs] [--digests]`：discover → `proof_groups` → `load_worker` → `prove_instance`，记录每个 H2 部分的耗时。`H2_SAVE=<正则>` 时只导出匹配的部分、不求解。`--digests` 时输出每条出边的 base / 目标合取项摘要，用于找共用合取项。
- `joint_norm.py`：某义务中，哪些 UF 参数对在联合规范化之后是恒等式。`l2diff.py`：逐层列出 `sha3_slice` 参数的最小差异。`shared_try.py`：用若干出边的部分公式算公共 base 上的查询，跑生产 `_check`。
- 抓取 pair 阶段的义务：给 `_check_rows` 打补丁，在 `_check_all` 之前把各个 pair 写成 SMT2，然后中止。注意要跳过 `_discharge_all_rows` 的 `pair_group_*` 试验。另外，前缀 pass、卡住组的结果和 correspondence 都能直接从 `_pair_phase` 里拿到。
- H2：`discover` → `proof_groups(..., True)` → `load_worker` → `prove_instance`，并对 `close_edge` 和 `_check` 打计时补丁。若只关心 H2，可以把 `_pair_phase` 替换成直接返回 correspondence（只用于诊断，**不是证明**）。

## 8. 未解决的问题 / 下一步

1. **8750 慢出边上的 `memory_0`**（CALLDATACOPY 长度落在 calldata 内）仍要约 2400–2600s，是 H2 剩余时间的大头（4910s 中占 2422s）。差别在复制区间的写法：EVM 是 `ULT(i − dst, len)` 加 `min(src, CDS)`，x86 是 `i < dst + len`。两者只有在不溢出时才相等，要靠前提。下一步可以考虑：
   - 用前提判定 lambda 体内的闭守卫，并在判定之后重新规范化 lambda 体。原型（`decide_guards`）判定了 2 个守卫，但还不够让两侧合上。
   - 区间成员的规范化：在已证明不溢出的前提下，把 `ULT(i−d, n)` 写成 `ULE(d, i) ∧ ULT(i, d+n)`。这需要单独的前提引理。
   - 收尾的直接查询改用 blast 过的规范式（本机 578s 对 1500s+；只有一个样本，还要更多数据才能定）。
2. **8750 的另外两个实例**（d11 (0,0)、d15 (0,0)）本机没有单独跑。它们和 d11 符号是同一个块，出边结构相同，修法 3、4 同样适用，需要服务器确认。服务器上 H2 和 3 个实例并行，单条出边的耗时会比本机高。
3. **跨出边共用的前提是公共 base 足够强。** 8750 上 36 次共用证明全部成功。若在别的合约上公共 base 太弱，共用尝试失败后要按出边各自再证一次，这部分时间就浪费了（这是耗时问题，不影响健全性）。如果服务器上发现这种情况，可以给共用尝试加一个预算上限。
4. **对其他合约耗时的影响**：修法 1 扩大了 normalize 的作用范围（每个单变量 lambda 体都要规范化一次）。修法 2 在每次 unify 路线和每个节点的 `_unify_node` 上多做一次规范化（上限 4 个查询超时）。在 1327 上 lambda 规范化只要 1–2s。但对 lambda 很多的大公式，normalize 本身可能变慢。本机能回归的只有任务 L 和本任务的 SMT2（全部变快或持平，§6.2），其他合约（Safe / CErc20 / PoolManager）已证块的耗时需要服务器全量验证来确认。
5. **1327 符号实例的 `pair_0_6` / `pair_0_7`**（x86 在 SSTORE 一类的 gas 检查上 OOG，EVM 正常退出；见 §6.4）是本次整节点运行中新暴露出来的。义务应当成立：gas 表达式与 `0_46` 相同，只是方向相反。但本机没有证出。下一步可以先在 `permit2_1327_pair_0_6.smt2` 上做同形比较：x86 那个取反的检查和 EVM 合取项 46（及 0/9/17）在 lambda 规范化之后的差别，看是否需要把 x86 的 L3b 链和 EVM 的链按层合并（任务 L 的 unify 加上本次修法 1）。
6. **Aave 8248 整节点**在本机因内存限制被 OOM 杀掉，没有整节点结果。1800 个 pair 是全积，节点级 `unify_identities` 会在所有 host pair 上做一次联合规范化（上限 4 个查询超时），需要在服务器上看它的耗时和内存。
7. 1327 m=192 f=128 整节点本机未跑完。

