# 块级 lock-step 等价验证方案

> **状态**：2026-09-03 设计定稿，未实现。七组实验的实测数据支撑，脚本在 `tmp/`（待固化进 `tools/`）。
>
> **一句话**：把 EVM IR 的**每个 basic block** 与其编译出的 x86 代码区间配对，从块入口的关系式状态出发逐块证明等价，用 CFG 边归纳取代整程序路径枚举。
>
> **与 `docs/cutpoint泛化方案.md` 的区别**：那份被否决的方案把 cutpoint 放在函数入口、追求"函数体证一次多处复用"（乘法变加法）；本方案把切点放在**每个块**、追求"复杂度局部化"（路径爆炸变块数线性），不要求任何复用，因此不依赖函数边界恢复。两者共享 cutpoint / havoc / 关系证明这套骨架，但收益模型与实测结论相反。

---

## 0. 摘要

### 0.1 方案骨架

```
对每一对配对块 (B_evm, B_x86)，在块入口建立关系 R，证明四件事：
  ①  到达：每条到达 B 的边上，实际状态满足 R + 域约束 + 结构前提
  ②  保持：从满足 R 的入口状态执行块体，两侧走同一条出边，且后继块入口 R 保持
  ③  终止：块内 terminal 路径（REVERT / OOG / 栈错误 / RET）两侧 observable 等价
  ④  覆盖：每条 CFG 边都被 ①②③ 覆盖，未覆盖即 fail-closed
```

结构上这是**两阶段**的：阶段 A 逐块证块级定理，阶段 B 把每个块折叠成一个点、在折叠图上归纳出整程序结论。①② 是阶段 A 交付给阶段 B 的**接口契约**，③④ 是阶段 B 闭合归纳所需的**记账**（详见 §2.5）。

归纳对象是 **CFG 边**而非执行路径，因此任意迭代次数的循环被归纳吞掉，不需要单独的循环不变式。

### 0.2 关键设计：三参数专门化

块入口状态不是纯 havoc，而是按三个**编译期可静态推断**的参数专门化：

| 参数 | 含义 | 现状 | 实测作用 |
|---|---|---|---|
| `k` | 绝对栈深度（`stack_byte_offset = k*32`） | `build_havoc` 已具备 | **分水岭**：符号 vs 具体 = 150.3s vs 7.9s（19×） |
| `msize` | 入口 `memory_size` | **本方案新增** | 三个成败点块从 TIMEOUT 变收敛 |
| `fmp` | 入口 `mem[0x40]` free memory pointer | **本方案新增** | 必须与 `msize` 联合，否则 CErc20 最坏块仍 TIMEOUT |

三者都不是"免费简化"而是**定理的适用域**：①（到达）必须在实际到达状态上重新证明它们，且必须证明取值集合对块转移**封闭**（对标 `verification/loop_induction.py:1475` 的 `_check_depth_transition_closure`）。

### 0.3 结论强度：可行性是**分块的**

这不是一个 yes/no 的方案。实测把块分成三类：

| 类别 | 占比（ENS/CErc20/Safe） | 状态 |
|---|---|---|
| **可专门化块** | 93.7% / 43.6% / 51.9% | ✅ 秒级收敛，判死率 93–95% |
| **⊤ 块**（`msize` 静态不可知） | 0% / 55.9% / 47.2% | ❌ 降级即 TIMEOUT，无中间态 |
| 其中真·动态块 | 少数 | ❌ 需换机制（仿射内存抽象） |

**方案的价值**：把 CErc20/Safe 从"整程序完全跑不完"变成"可专门化块秒级证完 + 一份根因明确的待攻克清单"。**方案不承诺全覆盖。**

### 0.4 与既有两份方案的关系

- **`docs/循环处理增强方案.md`（主方案，已落地于本分支）**：本方案的**地基**。`CutpointRelationSchema`、段执行原语、TAG 指纹、copy-loop summary 全部复用。同时本方案修复它 §9.0 记录的最大缺口——46% 的配对循环因"出口按数量相等 + 顺序 zip"被拒，而 §9.0 自己给出的方向正是"用 TAG 指纹做语义配对"（见 §5.1）。
- **`docs/cutpoint泛化方案.md`（已否决）**：其 §2.2（cutpoint 集合而非函数摘要）、§3（pc↔addr 权威映射）、§4.2–4.6 的义务形式**原样适用**。其 §1.3 的否决理由（havoc 过近似 3.2× + 深度类倍增）在本方案下被实测部分推翻，见 §1.2。

---

## 1. 动机与实测依据

### 1.1 当前管线的瓶颈是实证的

整程序符号执行（具体初始状态，`max_depth=240`）：

| | ENSRegistry | CErc20 | Safe |
|---|---|---|---|
| 能否跑完 | 跑得完 | **880s 未跑完** | **880s 未跑完** |
| jcc 静态判死率 | 86.5% | 81.9%（前缀样本） | 33.5%（卡死于 `je` 判死率 1.5% 的区域） |

`X86SymbolicExecutor._handle_jcc` 唯一的剪枝器是纯静态的 `not is_false(simplify(cond))`（无 solver），它是 x86 侧吞吐的主力。**判死率的临界值在 90% 附近，边际极陡**——低于它路径爆炸，高于它秒级。这解释了上表：ENS 的 86.5% 勉强跑得完，CErc20/Safe 跑不完。

### 1.2 为什么切在"每个块"，而不是 cutpoint 泛化的选点

`cutpoint泛化方案 §1.3` 的切点数–代价表，趋势是**单调**的：

| cutpoint 数 | 17 | 20 | 30 | 47 |
|---|---|---|---|---|
| 段路径 | 5501 | 3823 | 2971 | **3038** |
| 最大条件 AST | 13386 | 13107 | 4829 | **4782** |

47 是它测过的最多、也是最好的点；127/723 个切点（本方案）**从未被测过**，而已有趋势朝本方案的方向改善。文档写的"不能多切也不能少切的困境"只有"少切更差"这一半有数据。

两笔被认定为致命的罚金，实测都不成立于本方案：

- **深度类倍增**：文档记 4.4×/~17×，但那是在**不动点未收敛**状态下读的。用返回地址影子栈重测，收敛值是 **1.27×/2.55×/2.22×**（§3.2）。
- **havoc 过近似**：文档记 3.2×，成因是"栈上具体常量被 havoc 成符号"。本方案的三参数专门化正是对这条的直接回应——联合注入后判死率 93–95%，**高于整程序基线**。

此外，本方案独有一项 cutpoint 泛化拿不到的收益：**AST 深度被硬性封顶在单块内**。ENS 的真实瓶颈是内部函数调用链让 Z3 项线性膨胀（~35 节点/步，`Z3_simplify` 占 61% 墙钟），块级分解切断这条链；cutpoint 方案的段跨多个块，拿不到。

### 1.3 三笔成本的实测总表

| 成本 | 结论 | 数据 |
|---|---|---|
| 深度类倍增 | ✅ 可接受 | 1.27× / 2.55× / 2.22×，全收敛，块覆盖 100% |
| jcc 判死率损失 | ✅ 可接受 | 纯 havoc 27.5% → 三参数专门化 **93–95%** |
| 块内路径尾部 | ⚠️ 分块 | 可专门化块秒级；⊤ 块 TIMEOUT |

块的形状（12 条 TAG 序言指纹对齐，ENS 127/127、CErc20 723/723、Safe 742/742 全覆盖）：

```
每 EVM 块的 x86 basic block   均值 55.6 / 47.6 / 41.6   最大 300 / 366 / 490
每 EVM 块的条件跳转           中位 8–10   p95 66–89   最大 167 / 167 / 228
守卫分支 : 数据分支            43 : 57（三合约一致，数据分支占多数）
```

**注意：EVM 块内是顺序的（127/723 块里各只有 1 个非末尾分支），但 x86 侧不是。** "块内顺序执行所以块等价好证"这个直觉只在 EVM 侧成立。

> **一项尚未实测的数据：全量规模。** 已有的段执行耗时来自**随机采样 25 个入口**（CErc20 7.9s、Safe 6.6s，每入口路径均值 1.9、最大 5），而条件跳转分布强右偏——25 个随机样本期望只撞上 1–2 个尾部块，实测最大路径数只有 5，**说明一个尾部块都没采到**。因此"外推到全合约约 10 分钟"这类数字**不成立，本方案不作此承诺**。真实的全量成本必须用**分层采样**（按条件跳转数分层，每块设墙钟上限，超时块照实计入）测得，这是 §6 阶段 5 的验收产出，不是本方案的前置论据。

---

## 2. 机制

### 2.1 块对齐：结构性证据，不是启发式

`compileEVMTag` 为每个 EVM 块发射固定 12 条序言（`$GOPATH/src/github.com/bcds/go-hpc-evm/evm/aot/impl_amd64.go`）。取三元组 `(static_gas, min_depth*32, max_depth*32+1)` 作指纹，与 EVM 块按 pc 升序 / x86 地址升序单调对齐：

```
ENSRegistry 127/127   CErc20 723/723   Safe 742/742   逐位一致，零错配
```

**两个相互独立的证据源**：
1. TAG 序言指纹（全覆盖）；
2. 动态 JUMP 的返回比较链——`CMPQ rax, $pc` 的立即数是 EVM 目标 pc，紧随 `JEQ` 的 rel32 是对应 x86 地址（纯立即数编码、无跳转表）。ENS 33 对 / CErc20 192 对 / Safe 166 对，与 (1) **100% 吻合**。

**pairing 错误是安全方向的**：对齐错了块等价证不出来（假红），不会假绿——前提是 ② 里带上"后继块也配对"这条义务。

> ⚠️ **不要用 `x86_64/loop_analysis.py` 现有的 3 指令判据定位块。** 它只看 `mov [r13+0x70]` / `cmp` / `jb`，那是 `makeStaticUseGas` 的公共前缀，动态 gas 路径也生成，过匹配 2.1×（CErc20 命中 1523 vs 723）。实测的最小充分判据是"3 条指令且 `cmp` 的第二操作数必须是**立即数**"（动态 gas 路径发射的是 `cmp TMP, dynamicCostReg` 寄存器形式）；本方案取完整 12 条，因为需要全部三个立即数。

### 2.2 R：复用现有 schema，新增两个分量

`R` 直接取 `verification/cutpoint_relation.py` 的 `CutpointRelationSchema._COMPONENTS`（14 项）：

```
stack_geometry, live_stack_prefix, memory, memory_size, memory_gas, gas,
host_gas_seq, return_data_source, storage, transient_storage,
return_metadata, environment, callengine_environment, callengine_mirror
```

**本方案新增一项分量**：

| 新分量 | 内容 | 为什么必须是独立分量 |
|---|---|---|
| `free_memory_pointer` | `mem[0x40:0x60] == fmp`，**两侧各自**钉到具体值 | 它是**专门化参数**，必须同时进 havoc、进 ① 的到达义务、进 ② 的封闭义务、进证书指纹（四处齐全纪律） |

> **实现时的细化（已落地）**：早期草稿把"当前程序点对属于权威映射"也列为 `R` 的一个分量（`block_pairing`）。**这是错的**——`_COMPONENTS` 的每一项都是**状态谓词**（产出一个 Z3 条件），而程序点配对是元数据检查，不是状态上的等式。它的正确位置是**编排层**（§6 阶段 4）：块图推进时校验后继块对在权威映射内，不在则 fail-closed。混进 `R` 会让 `component_goals` 产出一个恒真或恒假的伪条件，两种都无意义。

`memory_size` 与 `free_memory_pointer` 的义务都**不只写"两侧相等"**：专门化时两侧各自钉到具体值。只证相等的话，定理在任意取值上都成立，却会被应用到按具体值证出的结论上——(H1) 到达覆盖形同虚设。

`memory_size` 已在 `_COMPONENTS` 里，但当前被 havoc 成自由符号（只带 `MSize ≤ cap` + 32 字节对齐两条域约束）。本方案把它从"自由符号 + 弱域约束"改成"按静态推断值专门化"。

> **纪律（沿用主方案，不重新论证）**：分量必须四处齐全（进 R / 进 havoc / 进 ①② 的义务 / 进指纹）。`_assert_component_symmetry` 与 `_assert_mirror_coverage` 是这条纪律的机器检查，新增分量必须同时登记。踩过的坑：`callengine_mirror` 曾"分量名在、义务里没有它"，实测 5/5 字段接受陈旧 limb。

### 2.3 三参数专门化与其健全性

```
theorem key = (block_pair_id, k, msize, fmp, R版本, GasCheck档, summary_config, aot_profile,
               pc↔addr 映射指纹)
```

**健全性由三条义务闭合，缺一不可**：

```
(H1) 到达覆盖：任何到达块 B 的边，其携带的 (k, msize, fmp) 都在 B 的已登记集合内
(H2) 转移封闭：每个已登记三元组的块出口，只转移到下游块的已登记集合内
(H3) 不动点收敛：(H1)(H2) 的传播在预设轮数内收敛；不收敛 ⇒ fail-closed 拒绝
```

这与 `_check_depth_transition_closure` 是同一机制的三维推广。**⊤ 值不是一个"桶"**——它表示该块的参数不可静态确定，只能降级（§4.4）。

### 2.4 四条证明义务

```
① 到达（Base）
   (a) 对每条边 (A → B)：证明 A 的出口状态满足 R_B + 域约束 + 结构前提（两侧均 running）
   (b) entry：两侧入口程序点是配对的 (pc₀, addr₀)，且初始状态满足 R_{B₀}
       —— 不能只说"由初始状态给出"，入口配对本身是义务

② 保持（归纳步）
   从 R_B 的 havoc+专门化状态出发，两侧各执行块体，证明：
   (a) 两侧选中同一条出边（含 JUMPI 条件等价、动态 JUMP 目标选择一致）
       写成双向蕴含：EVM 选边 e ⟺ x86 选对应边 e'
   (b) 到达任一后继块入口时 R_{B'} 保持（**在出口 site 上求，见下**）
   (c) 后继块对属于权威映射 —— **编排层检查**（§2.2），不是 R 的状态分量

③ 终止路径
   块内 terminal（REVERT / OOG / 栈错误 / RET）按 status 分桶，逐桶证 observable
   等价。**status 只作分桶键，绝不作免检依据。**
   (b) 分类穷尽：块的每条出路必须落入"出边"(②) 或"terminal"(③) 之一，不得有
       第三种。host bridge 退出**不是 terminal**（它是暂离后返回），必须显式归入
       出边一侧并证明返回点对应

④ 覆盖
   (a) 每条 CFG 边恰好被一条 ① 覆盖；每个块恰好被一条 ② 覆盖
   (b) x86 侧每条指令恰好属于一个块区间——区间**两两不重叠且完全覆盖**代码段
   (c) 任何未覆盖的边、未被接管的块、落在所有区间外的指令 ⇒ fail-closed
```

**④(b) 是块级分解的地基，此前只是实测观察，本方案要求升格为 fail-closed 检查。** 实测：区间边界与 `identify_basic_blocks` 的边界完全重合，覆盖 ENS 7059/7060、CErc20 34444/34445、Safe 30868/30869。

> **实现修正（阶段 3 PoC 暴露，原文写错）：那唯一"未覆盖"的 12 字节不是非块代码，它是 entry 块的前缀。**
>
> ```asm
> mov r14, [r13+0x38] ; add r14, [r13+0x30] ; mov r15, [r13+0x10]   ; 0x1000–0x100b
> mov rax, [r13+0x70] ; cmp rax, $StaticGas ; jb  <OOG>             ; 0x100c 起是第一个 TAG
> ```
>
> 它执行必经，与第一个 TAG **同属一个 basic block**，且它做的事（从 callEngine 重建 R14/R15）正是 `stack_geometry` 分量断言的内容。把它当"非块代码"剔除，entry 块的 x86 入口就落在 basic block 中间，执行器直接报 `Entry block not found`。
>
> **正确处理：entry 块的 x86 区间从程序起点开始**，其余块的区间起点仍是各自的 TAG。

**②(b) 的 site 语义：`R` 在块出口与块入口不是同一组义务**（阶段 3 PoC 暴露）。

x86 在块内**不维护 R14 与 `[R13+0x30]` 的同步**：块出口时 `callengine_stack_byte_offset` 已经是新栈深，而 R14 仍停在入口值。实测 muti_block `pc=13 → 65`：

```
EVM 出口 SP = 1                       ✓
x86 callengine_stack_byte_offset = 32 ✓   (= 1×32)
x86 R14 − stack_base = 0              ✗   (仍是入口值，期望 32)
```

原因是后继块的 TAG 序言会**无条件**执行 `mov r14,[r13+0x38]; add r14,[r13+0x30]` 把 R14 重建（`compileEVMTag`，impl_amd64.go:4283-4285）。所以：

```
site="entry"  完整 stack_geometry，含 R14 == 栈基 + byte_offset
site="exit"   省略 R14 那一项；byte_offset 仍是义务
```

**这是 codegen 的结构性质，不是假设**——但它依赖"后继块一定以 TAG 序言开头"，因此**只对块转移边适用，terminal 路径不得使用**（terminal 没有后继 TAG 来重建 R14）。不做这个区分，每个有净栈效应的块都会假失败：PoC 上 `pc=13` 的 97 条转移全部卡在 `stack_geometry`。

**②(a) 的动态 JUMP 臂集不对称**（沿用 cutpoint 泛化 §4.3，仍成立）：Go 的 `isValidJumpDest` 会**静默丢弃**不在 jumpTable 里的目标，因此 x86 臂集可以是 EVM `immediate_set` 的真子集。守卫必须写成：

```
x86 臂集 ⊆ EVM immediate_set                              （结构检查）
∧ ∀ t ∈ EVM immediate_set \ x86 臂集. 证明 dest = t 在 R_B 下不可达
```

差集**不能假设为空**——那正是"编译器漏掉一个合法跳转目标"这类 bug 的形态。

### 2.5 两阶段：块内等价 ⇒ 折叠图上的归纳

方案的组织形式就是"先局部后全局"两阶段：

```
阶段 A（局部）  对每个配对块 (B_evm, B_x86) 证一条块级等价定理
阶段 B（全局）  把每个块折叠成一个点，在折叠图上证"从 entry 到 terminal，两侧一致"
```

**这个结构成立，而且它就是 ①②③④ 的结构。** 要让它真正闭合，必须把三件事说准：折叠出来的"点"是什么、块定理必须交付什么接口、阶段 B 折叠之后还剩多少真活。

> 修正：早稿把两阶段写成"顺序在归纳结构上不成立"。那是误读——被驳倒的是**静态 CFG 同构**（§2.5.4），与"折叠后点对点"不是一回事。

#### 2.5.1 折叠出的点不是 EVM 块，是"块 × 参数"实例

折叠要合法，块定理必须**上下文无关**：对任意满足 `R_B` 的入口状态成立，而不只是对"实际到达的那些状态"成立。只有全称量化的块定理才能当成折叠图里的一个原子转移、在图的任何位置代入。这正是 havoc 的作用——它不是性能技巧，是折叠的合法性前提。

代价是 §2.3 的三参数专门化：定理带 `(k, msize, fmp)` 的适用域，因此

```
折叠图的节点 = (block_pair_id, k, msize, fmp)
```

同一个 EVM 块在不同深度类 / 不同 `msize` 下是折叠图里的**不同节点**。§3.2 实测的深度类倍增 1.27× / 2.55× / 2.22× 就是这个节点膨胀的量。**⊤ 块给不出有限节点集**——这才是它不能进折叠图、只能降级的根本原因（§4.5），不只是"块内证不动"。

#### 2.5.2 块定理的接口契约：阶段 B 只能用契约里写下的东西

折叠之后阶段 B 看不见块内部，能用的只有块定理的结论。因此块定理必须交付四样，少一样阶段 B 就断：

| 契约项 | 阶段 B 用它做什么 | 落在 |
|---|---|---|
| 入口 `R_B` ⇒ 出口 `R_{B'}` 保持 | 归纳假设沿边传递 | ②(b) |
| **两侧选中同一条出边**（双向蕴含） | 决定折叠图上走哪条边 | ②(a) |
| 块内 observable **增量**对应（gas 增量 / storage 写 / `host_gas_seq`） | 终点 observable 由增量沿边合成 | §4.8 |
| 块内 terminal 分桶等价，且 terminal 是吸收态 | 折叠图的终点良定义 | ③ |

**②(a) 是两阶段能闭合的关键，也是最容易漏的一项。** 如果阶段 A 只证"块内数据等价"（入口对应 ⇒ 出口对应），阶段 B 就拿不到任何材料判断两侧走哪条边：走哪条边是**数据相关**的（EVM `JUMPI` 看栈顶值，x86 `jcc` 看标志位），而折叠图是静态的，静态图上比对边集**证不出每次执行走同一条边**。"边一致"不是阶段 B 事后能补的全局性质，它必须由阶段 A 在 `R` 下逐块**语义地**证出来、写进契约。

同理，observable 不能只在终点比。块内的 gas 消耗、storage 写折叠后就看不见了——不把增量写进契约，折叠会把它们折没，阶段 B 比出来的"结果一致"是个残缺投影。

#### 2.5.3 阶段 B 剩下什么：归纳骨架平凡，三笔账不平凡

契约齐全时，阶段 B 对轨迹长度做归纳：

```
base   entry 两侧程序点配对，初始状态满足 R_{B₀}                              ①(b)
step   由 ②(a) 两侧走同一条边 e；由 ②(b) 后继入口 R 保持；后继块对在权威映射内   ②
stop   两侧同时进入配对的 terminal，由 ③ observable 等价                      ③
```

归纳本身是平凡的。**不平凡的是三笔账**——它们才是阶段 B 的实际工作量：

1. **覆盖记账（④）。** 归纳成立的前提是"没有第三种出路"：每条 CFG 边被 ① 覆盖、每个块被 ② 覆盖、每条出路落入出边或 terminal、x86 每条指令属于唯一区间。任一缺口就是归纳的漏洞，必须 fail-closed。折叠的**良定义性**直接依赖 ④(b)——区间重叠或指令落在所有区间外，折叠出来的图就不是原程序。
2. **节点集闭合（H1)(H2)(H3）。** 因为节点带参数，"后继确实是折叠图里的一个点"本身是义务：到达 B 的边携带的 `(k,msize,fmp)` 必须在已登记集内、转移封闭、传播收敛。**这就是"两边的点一致"在有专门化参数时的真实形态**，不是免费推论。
3. **累积量的合成结构（§4.8）。** gas / storage / `host_gas_seq` 的增量必须能沿边相加。"terminal 是吸收态"是这里的关键性质：终止即整程序终止，不产生新的 caller 分支，所以合成是加法，不需要重新枚举路径。

#### 2.5.4 被驳掉的是另一件事：静态 CFG 同构

"折叠后点对点"与"静态证两侧 CFG 同构"必须分开——后者仍然不成立，理由有二：

- **折叠前两侧图不同构，而且差得远。** 一个 EVM 块编译成 ~50 个 x86 basic block 的子图（均值 55.6/47.6/41.6，最大 300/366/490）。所以**折叠是必要前置**：折叠掉块内那 ~50 个节点，两侧才谈得上点对点。
- **折叠后也不要求边集相等。** 动态 JUMP 下 x86 臂集可以是 EVM `immediate_set` 的真子集（`isValidJumpDest` 静默丢弃非法目标，§2.4），这是编译器的合法行为。我们只要求**实际可达**的转移对应：差集里的目标要么对应，要么被证在 `R_B` 下不可达。静态同构因此**既不充分**（证不出走同一条边）**也不必要**（可达性弱于边集相等）。

两阶段落到证据形态上是三层：

| 层 | 内容 | 证据形态 | 落在哪条义务 |
|---|---|---|---|
| **节点对应** | `pc ↔ addr` 双射；x86 区间两两不重叠且完全覆盖 | **结构性证据**（TAG 指纹 723/723 + 返回链锚点交叉验证），进指纹，codegen 变更后自动失效 | §2.1 + ④(b) |
| **边对应** | `R_B ∧ 块体执行 ⇒ 两侧选同一条出边`，且后继块对在权威映射内 | **逐块的语义定理** | ②(a)(c) |
| **完备性** | 每条边/每个块/每条出路/每条指令都被覆盖，无遗漏、无第三种出路 | **记账 + fail-closed** | ①(b) ③(b) ④ |

三层合起来给出的是**块粒度的双模拟（bisimulation）**——比"同构"更强也更准确：同构只断言图结构一致，双模拟断言每一步转移都对应**且**状态关系保持。

> **一处必须警惕的**：节点对应那一层是**结构性证据而非定理**（§7.2 已如实标注）。所以 ④(b) 的 fail-closed 检查是它唯一的兜底——**区间重叠或指令落在所有区间外时必须拒绝，不得局部修补**。
>
> **⚠️ 判别力的依据要说准（阶段 0 实测推翻了本文早先的说法）。** 早稿写"依赖同一合约内 TAG 三元组两两不同"，**这是假的**：
>
> | | 块数 | 不同三元组 | 最大重数 |
> |---|---|---|---|
> | ENS | 127 | **65** | 17 |
> | CErc20 | 723 | **304** | 55 |
> | Safe | 742 | **350** | 79 |
>
> 三元组远非唯一。对齐不受影响——它是**单调 zip + 逐位验证**，从来不是按指纹查表。真正的依据是三条合力：**① 计数相等**（TAG 命中数 == EVM 块数）、**② N 个逐位相等**（127/723/742 位全部一致，任一位不符即整体拒绝）、**③ 一个完全独立的锚点源**（返回链 `cmp/je` 立即数，33/192/166 对，100% 落在已匹配的 TAG 上且 pc 一致）。把依据说成"指纹唯一"会让人以为可以按指纹反查块，那是错的。

#### 2.5.5 两阶段拿不到的：终止性

折叠图上的归纳是对**已经走完的轨迹**做的，给出 partial correctness："若两侧都走到下一块，则 `R` 保持"。"从开始走到结束"里的"**走到**结束"不在其中——要证两侧同时终止或同时不终止，需在折叠图的 SCC 上给 ranking function。本方案 v1 不证（§2.6 第 2 条），结论按 §7 如实标注。

### 2.6 循环：吸收了什么，没吸收什么

**被吸收**：EVM 层的循环（合约里的 for/while）。因为归纳在 CFG 边上，回边只是普通的一条边。而且这是**关系式**验证——`R` 只说"两侧状态对应"，不需要知道循环变量的取值范围，所以循环头的 `R` 与普通块的 `R` 是同一个模板，**不需要推断任何合约相关的数据不变式**。这条性质依赖 go-hpc-evm 是模板式 codegen、不做跨块优化。

**没被吸收，必须单独处理的三项**：

1. **编译器引入的 x86 内部循环**。CErc20 的 x86 有 48 个 natural loop，EVM 侧只有 9 个——**39 个是编译器引入的**（copy 族），藏在"EVM 侧顺序执行"的块里。含循环的区间：CErc20 37 个、Safe 26 个，其静态路径数无界。这些必须靠 copy-loop summary 折叠（§4.5）。
2. **终止性**。块归纳只证 partial correctness（"如果两边都走到下一块，则 R 保持"）。要证"两侧同时终止或同时不终止"，仍需在 CFG 的 SCC 上给 ranking function。本方案 v1 **不证终止**，结论按 §7 如实标注。
3. **深度类不动点的收敛**本身承担了递归检测：不收敛 ⇒ fail-closed 拒绝，比语法判据更强。

---

## 3. 前置能力：三个静态分析器

三者都是**纯分析、无证明义务**的前置，产出进 theorem key 与证书指纹。选错只影响性能与覆盖率，不影响结论正确性——因为 ①②③④ 会在实际状态上重新证明一切。

### 3.1 pc ↔ addr 权威映射（`tools/tag_align.py`）

12 条 TAG 序言指纹单调 zip + 返回链锚点交叉校验。**任何一位对不上就整体拒绝**（fail-closed），不做局部修补。

### 3.2 返回地址影子栈 → 深度类（`tools/call_provenance.py`）

朴素的上下文不敏感 CFG 会把每个 callee 的返回点连回**所有** caller，栈深度沿假环无限增长：ENS 3.87×、CErc20 **≥240× 发散**、Safe **≥267× 发散**。

**正确机制是返回地址影子栈**：每个块把它 PUSH 的**全部** pad 按程序序压栈（排除跳转目标本身），返回点弹栈顶。实测：

```
动态 provenance 恢复率  ENS 46/46、CErc20 915/915、Safe 378/378 = 100%，零回退
深度类倍增              1.27× / 2.55× / 2.22×，全收敛，块覆盖 100%
最大深度类              4 / 37 / 31        单一深度块占比 81% / 67% / 69%
```

> ⚠️ **`cutpoint泛化方案 §1.5` 记的静态判据（调用点 pad ∩ 返回点 `immediate_set` 交集唯一）不足以建图。** CErc20 块 836 是 `PUSH 855; PUSH 850; JUMP 13048`——855 是留给**后续**调用的 continuation，只压"本次调用的 pad"就会丢帧，之后返回 thunk 链连续弹三帧却只压过一帧，影子栈见底 ⇒ 假环复活 ⇒ 深度跑到 -41001。**栈序比集合交集信息量大。** 静态交集判据只用于报告，不参与建图。
>
> ⚠️ **没有优雅降级，只有悬崖。** 把静态恢复失败的调用点强制 fail-closed（栈顶匹配也不采信），CErc20 立刻 **1080×、不收敛、可达掉到 437/723**。一次保守回退让影子栈错位，之后每个返回点都错、级联全崩。因此这笔成本的真实形态是「2.5×，或彻底不可用」，必须做成被验证器**检查并 fail-closed** 的结构前提，而不是一个可以退让的近似。

### 3.3 `memory_size` / `fmp` 抽象解释（`tools/msize_absint.py`）

EVM 侧 MSize 的前向抽象解释，三个并行分量：抽象值栈（具体 int | ⊤）、抽象常量内存（追踪 `mem[0x40]`）、MSize（值集合）。演化规则以 `evm_ir/semantics_gas.py::charge_dynamic_gas` + `state/evm_gas_state.py::memory_expansion_fee` 为准：`MSize' = max(MSize, ceil32(requested))`，`length == 0 ⇒ requested = 0`。

> 注：**CALL 族在当前模型里不改 MSize**（`evm_ir/semantics.py` 明说不建模 host 内部扩展）。抽象解释必须与实现一致，不能按协议直觉写。

**结果是二元的，这是最重要的结构性发现**：

| | MSize 唯一 | 2–4 值 | 5–16 值 | **⊤** |
|---|---|---|---|---|
| ENS | **93.7%** | 6.3% | 0 | **0%** |
| CErc20 | 43.6% | 0.6% | 0 | **55.9%** |
| Safe | 51.9% | 0.9% | 0 | **47.2%** |

**没有中间桶**——`5-16` 档恒为 0。深度类那种"按值分桶"在这里退化成「唯一 vs ⊤」两档。唯一值高度集中在 `0x60`（Solidity 多数块只碰 scratch 区 0x00–0x60，free pointer 停在 0x80）。

**⊤ 的结构给出最大杠杆**：

```
⊤ 几乎全是"继承"不是"自产"：CErc20 402/404、Safe 349/350 的源站点在上游块
源站点极少：CErc20 仅 28 个、Safe 仅 8 个
且高度集中：CErc20 单站点 (块 4236 的 MSTORE@fmp) 解释 304 块
            Safe   单站点 (块 9351 的 CALLDATACOPY) 解释 255 块
msize=⊤ ⟺ fmp=⊤（0/404、0/350 例外），两者同生共死
```

自校验（必须在实现时保留为回归）：Σ(per-op delta) 对 1592 个块**逐块等于** Go 导出的 `EVMBlock.stack_depth`，零处不符。

---

## 4. 设计决议

每条决议都附实测依据。**没有依据的决议不写进本节。**

### 4.1 `msize` 与 `fmp` 必须**联合**注入

这是本方案最关键的一条。三个 `cdl=0 & copy=0` 的最坏块（此前从 havoc 出发跑 2400s / 7000+ 路径不收敛）：

| 块 | 基线 | 只注 `msize` | 只注 `fmp` | **联合** |
|---|---|---|---|---|
| ENS 1455 | TIMEOUT 33.2% | p=80 **35.4s** 47.5% | TIMEOUT 78.3% | **p=11 3.0s 93.5%** |
| CErc20 5343 | TIMEOUT 26.9% | **TIMEOUT** 27.1% | TIMEOUT 78.6% | **p=49 42.5s 94.3%** |
| Safe 6275 | TIMEOUT 85.4% | p=8 4.8s 95.1% | TIMEOUT 85.5% | **p=8 4.9s 95.1%** |

**"哪个够用"因块而异，联合总是最好**：CErc20 5343 只注 `msize` 仍 TIMEOUT（必须加 `fmp`），Safe 6275 只注 `msize` 就够。机制是块内的 `MLOAD(0x40)` 读的是被 havoc 的内存数组——不注入 `fmp`，free pointer 仍是自由符号，`checkMemoryAndCalcDynamicGas` 的溢出检查链照样泡开。静态指标印证：5343 的块内内存 op 偏移常量率 4/10 → **10/10**。

**实现要点**：改 EVM 侧的 memory array 后**必须重建 x86 侧的 Lambda**。`build_havoc` 里 x86 的 `evm_mem` 是 `Lambda(addr, Select(snapshot, addr - r15))`，引用的是 havoc 时那个 array 变量；只改 EVM 侧会让两侧指向不同数组——那正是 `R` 的 `memory` 分量被悄悄破坏的形态。

### 4.2 取什么值不重要，具体化本身才是关键

`msize ∈ {0x80, 0x100, 0x400, 0x2000, 0x10000}` 全部收敛（35.9–46.0s，判死率 45–49%）。

⇒ **专门化不需要精确值**，这降低了对抽象解释精度的要求。但注意：取值仍必须是**被 ① 证明的实际到达值**，不能取一个"够大的常数"——那是把定理钉在证明域之外。

### 4.3 区间不变式路线：**否决**

两条独立证据：

1. **实测**：`UGE(msize, 0x80) ∧ ULE(msize, 0x2000)` 作为 assumption 加入，ENS 1455 仍 TIMEOUT（判死率 39.5%，与基线 33.2% 几无差别）。原因是 `_handle_jcc` 的剪枝器是**纯静态** `is_false(simplify(cond))`，根本不看 assumptions。
2. **结构**：抽象解释显示所有 ⊤ 块的区间上界恒为 CAP（`0x1FFFFFFFE0`），**上界零信息**。区间本身就无法让 `cmp/jb` 判死。

**可做的小改进**：现有域约束 `ULE(mem_size, cap)` 可以补一条 `UGE(mem_size, lo)`（lo 有信息且不平凡：CErc20 `0x60` 594 块 / `0xa0` 78 块 / `0xc0` 31 块）。但它只砍掉"扩展 vs 不扩展"的一半，`memoryGasCost` 里 `rounded > mem.Len()` 那条 jcc 仍然活着。**不要指望它救 ⊤ 块。**

### 4.4 把剪枝器升级成 solver 版：**否决**

把 `_keep_branch` 从纯 `simplify` 改成带路径约束 + assumptions 的可满足性判定，实测（ENS 1455，90s 预算）：

```
133 次 solver 调用，判死 67 次（50%），耗时 46.5 秒 —— 占预算一半
结果仍然 TIMEOUT
```

平均 ~350ms/次，开销远大于收益。**剪枝器必须保持纯静态。** 这条同时说明：任何"靠约束让分支变可判"的设计都必须让约束进入 `simplify` 可见的位置（即具体化），而不是进 `assumptions`。

### 4.5 ⊤ 块：降级 + 源站点攻坚，两条路分开走

⊤ 块**没有中间态**——降级即回到自由符号即 TIMEOUT。因此：

**(a) 降级路径**：⊤ 块不接管，退回整程序展开。这要求块级折叠与整程序展开**可混用**，且覆盖区不重叠（否则重复记 observable、重复扣 gas）。`verification/segment_validation.py` 需要扩一条 reason。

**(b) 源站点攻坚（最高杠杆）**：⊤ 是继承的（99.5%+），源站点仅 8–28 个且高度集中。优先攻克 CErc20 `4236/11250/6554/7613`、Safe `9351/11531/4946`。攻克手段是已有的 copy-loop summary / 循环折叠机制——**吃掉这几个站点，⊤ 会成片回落**。这比改抽象域划算得多。

**(c) 真·动态块必须换机制**：Safe 5377 的 19 个内存 op 里 18 个偏移动态，MSize 语义上就是 calldata 长度的函数。实测四档全 TIMEOUT（判死率 1.0% → 9.2%）。它的 EIP-712 编码模式很规整（`base + 0x20/0x40/.../0x160`），值得单独探一次**仿射内存抽象**（符号基址 + 常量偏移），但不在本方案范围内。

### 4.6 CALLDATALOAD summary：先补 per-hit proof，再依赖

CALLDATALOAD 是块内条件跳转的头号来源（岭回归系数 30.5/33.5/33.8，R²=0.99+）——`compileEVMCALLDATALOAD` 的 partial-read 尾路径 `moveMemToLoc` 展开 8 迭代 × 4 limb = 32 个 per-byte `cmp/jb`，加 3 个边界检查 = 35 分支/个。

开启 summary 能把这类块压平 **600–820×**（Safe 10750：静态 2¹²⁸ 路径 → 2 条段路径 / 10 块-步 / 0.13s，coverage complete）。**但按 shipped 配置在 havoc 入口下是硬失败**：

```
_requires_concrete_low_offset（x86_64/summaries/calldataload.py:550）在 havoc 入口下必然为真
  ⇒ 抛 CallDataLoadSummaryMatchError
  ⇒ 它继承 ValueError 而非 SummaryPreconditionError
  ⇒ x86_64/cfg_executor.py:735 不 fallback ⇒ 整段执行当场炸掉

覆盖面：require_concrete_offset=True 的站点 ENS 11/12、CErc20 25/26、Safe 58/59 = 96–98%
```

**决议**：块级方案若要依赖 CALLDATALOAD summary，**先决条件是给它补 per-hit proof**（含符号 offset 下 `add offset,32` 的 64-bit 回绕义务），对标 `x86_64/summaries/mul_proof.py`。理由是这条信任链在块级方案下**两次加重**：暴露面从少数扩到 96–98% 的站点；且可用性要求关掉 `require_concrete_offset`，关掉后只剩 `calldataload_no_overflow_assumption` 这条**加进 `assumptions` 的未证前提**兜底——正是 prove-or-reject 纪律列为假绿方向的做法。

**在补完 proof 之前，块级方案不得开启 CALLDATALOAD summary。** 这意味着 CDL 密集块暂时归入待攻克清单。

> **阶段 5 实证：这条前置条件就是 ENS 上唯一的失败类别。** 端到端跑 ENSRegistry（144 个定理实例）：
>
> ```
> proved 130 / 144 = 90.3%
> 失败 14 个实例，落在 9 个不同的块上
> 其中 13 个失败模式是 R 分量 live_stack_prefix 不保持
> ```
>
> 全合约 127 块里**只有 10 个含 `CALLDATALOAD`**，而**9 个失败块全部含 `CALLDATALOAD`（9/9 = 100%）**。不开 summary 时，每个 CALLDATALOAD 展开成 32 个 per-byte `cmp/jb` 拷贝，`live_stack_prefix` 的 256-bit 相等在两侧建模下证不出来。
>
> 换句话说：**块级方案在 ENS 上的边界恰好等于 CALLDATALOAD summary 的信任链缺口**。补上 per-hit proof（含符号 offset 的回绕义务）之后，这 10 个块应当一并转正——这是最高优先级的后续项，收益明确且已量化。

### 4.7 Tier2 copy-loop 在 havoc 入口有新故障，需前置门

整程序基线没暴露过的两处：

```
CErc20 8186（copy=1）→ Z3 ArgumentError: RecursionError，5.6s 崩溃
Safe 5377（copy=1） → 240s 只走 175 块-步，precondition_failures=32
                       （copy-loop 前提在 havoc 入口下逐条被拒，每次拒绝烧数秒）⇒ 净负收益
```

**决议**：Tier2 在块级方案下必须有**前置适用性检查**（静态判断该块的 copy-loop 前提在专门化状态下能否成立），不能靠运行时逐条拒绝。前提不满足直接降级，不进入段执行。

### 4.8 观察量：块级需要增量记账

`common/path_observation.py:6` 的 `OBSERVATION_KEYS` 是**十项**，**不含 logs**。当前是"终态快照"语义。块级方案需要把 observable 拆成"每块的增量贡献"（gas 增量、storage 写、terminal 分桶），并证明增量对应。

**块内 terminal 是吸收态**——终止即整程序终止、后继块不执行，因此不产生新的 caller 路径分支。这正是加法结构的来源。消费端只需 (i) 计入全局 coverage 记账；(ii) 与到达条件合取；(iii) **不重证** observable。

> **一个必须写死的陷阱**：OOG terminal 的可达性依赖实际 gas，而块定理是在专门化但仍符号的 gas 上证的。块定理对 OOG 的结论只能是"两侧同时 OOG 且 observable 一致"（先证 `oog_evm ↔ oog_x86` 再桥接，`common/oog_bridge.py` 已有机制），**不能**是"这条路径不可达"；消费端不得用具体预算把 OOG 分支折死——那是把待证命题假设掉。

---

## 5. 从 `develop-cutpoint` 继承什么、丢弃什么

本分支（`50eca71 落地cutpoint关系与循环归纳的机制层`）约 1 万行。实现本方案时**只保留需要的、干净正确的**部分。

### 5.1 直接继承（本方案的地基）

| 模块 | 继承理由 | 需要的改动 |
|---|---|---|
| `verification/cutpoint_relation.py` | **就是本方案的 R**。14 分量、`build_havoc`、`_assert_component_symmetry`、`_assert_mirror_coverage`、`CutpointModelRangeError` | 新增 `free_memory_pointer` / `block_pairing` 两分量；`memory_size` 从自由符号改为专门化参数 |
| `verification/loop_induction.py:362/459` `run_evm_segment` / `run_x86_segment` | 已支持任意 stop 集合 + coverage fail-closed，**块边界作为 stop 集合是现成能力** | 无需新原语 |
| `verification/loop_induction.py:1475` `_check_depth_transition_closure` | (H1)(H2) 的现成实现 | 推广到三维 `(k, msize, fmp)`；`registered` 从 `(self.stack_depth,)` 改为全局已登记集合 |
| `verification/segment_validation.py` | havoc 段的静态健全性检查（拒绝 GAS、无 MSize 关系时拒绝 MSIZE） | 补一条 reason：段内不得含未被接管的下游块（展开与折叠混用会重复记账）；`GAS` 那条可在 gas 进 R 后放宽 |
| `common/oog_bridge.py` | OOG 谓词先证后桥接，§4.8 依赖它 | 从循环头推广到每个块入口 |
| `x86_64/summaries/copy_loop.py` + `registry.py` | ⊤ 源站点攻坚的手段（§4.5b） | 加前置适用性检查（§4.7） |
| `verification/loop_certificates.py` / `loop_certificate_prover.py` | theorem/certificate 两层结构、四条缓存纪律（vacuity 拒绝 / range-error 降级 / 只缓存成立的定理 / `require_*` 进 application key） | 骨架照搬，key 换成 §2.3 的三参数形式 |

### 5.2 需要替换的

| 现状 | 问题 | 替换为 |
|---|---|---|
| `verification/loop_induction.py:1383` `exit_pairing = dict(zip(self.evm_exits, self.x86_exits))` | 按数量相等 + 顺序配对。**这是主方案 §9.0 里 46%（6/13）配对循环被拒的根因**，且多目标 JUMP 下两侧计数口径本就不同（`0xb39` 20 vs 15） | **块级方案下整体消失**：出口就是已配对的块边界，由 §3.1 的权威映射给出，不需要配对 |
| `x86_64/loop_analysis.py` 的 3 指令 TAG 判据 | 过匹配 2.1× | 12 条完整指纹（§2.1） |
| `verification/call_site_mapping` 的顺序 zip | bridge 站点按地址顺序猜对应关系，顺序错误时静默 | 由权威块映射直接给出，已知 soundness gap 消失 |

### 5.3 明确不继承

- **不搬 `develop-cycle` 的 `paired_segment_graph`**：1 万行单类，且其 `_normalize_evm_edge_state` 会与本分支的 gas 建模**双重扣减**。关系式同步推进层要在本分支重写。
- **不继承"循环归纳作为性能手段"的定位**：主方案 §0.5 自己写明"解决封闭性，不解决可扩展性"。本方案的性能收益来自块级分解，不来自循环归纳。
- **三个默认关的开关**（`loop_guard` / `fold_loops` / `enable_oog_bridge`，`verification/program_verifier.py:287-288`）：块级方案是独立的顶层路径，不复用这三个开关的语义；但 `loop_guard` 的结构守卫应升格为**前置门**而非失败附注。

---

## 6. 实施步骤

六个阶段，每阶段有独立可验收的产出。**前一阶段不通过不进入下一阶段。**

### 阶段 0：把分析器固化进 `tools/`（无证明义务）

产出 `tools/tag_align.py`、`tools/call_provenance.py`、`tools/msize_absint.py`（§3 三项），带自校验回归：

```
tag_align       三合约 127/127、723/723、742/742 全覆盖 + 返回链锚点 100% 吻合
call_provenance 动态恢复率 100%，深度类倍增 1.27×/2.55×/2.22× 且收敛
msize_absint    Σ(per-op delta) == EVMBlock.stack_depth 逐块相等（1592 块零不符）
```

**验收**：三个分析器在三合约上复现上述数字；任一位不符即整体拒绝（fail-closed）。

### 阶段 1：`R` 的两个新分量 + 三参数 havoc

改 `CutpointRelationSchema`：新增 `free_memory_pointer`、`block_pairing`；`build_havoc` 接受 `(k, msize, fmp)`；`fmp` 注入必须同时重建 x86 侧 Lambda（§4.1）。

**验收**：
- `_assert_component_symmetry` / `_assert_mirror_coverage` 通过（16 分量四处齐全）；
- 反向用例：故意漏登记一个分量，必须当场抛错；
- 复现 §4.1 的三行数据（三个最坏块联合注入后收敛，判死率 ≥93%）。

> **实现发现（阶段 0）：闭包检查要消费的是 `(pc, k)` 粒度的边，不是 `pc` 粒度。**
> `call_provenance` 产出的 `succs` 在 pc 粒度上与朴素 CFG **逐块相等**（三合约 163/1025/1002 条边完全一致）——每条返回边都在**某个**上下文里被真实走到，剪枝全部发生在 `(pc, 深度)` 粒度（strict subset 状态数 14/265/156）。所以 (H1)(H2) 必须在 `depth_succs` 上检查；用 `succs` 会让闭包义务恒过。

### 阶段 2：三维闭包检查

`_check_depth_transition_closure` 推广到 `(k, msize, fmp)`，`registered` 改为全局已登记集合，加 (H3) 不动点收敛判据。

**验收**：
- 非递归合约在预设轮数内收敛；
- 人为构造递归，不动点必须不收敛并 fail-closed；
- ⊤ 参数必须被识别为"不可专门化"而非一个桶。

### 阶段 3：单块等价证明（PoC）

在小 fixture（`muti_block`，40 块）上跑通 ①②③④ 四条义务，逐块证明。

**验收**：40 块全部通过，且反向用例成立——人为改动一个块的 `static_gas`，映射构造器整体拒绝而非局部错位。

### 阶段 4：块图编排 + 降级混用

把单块定理串成全程序结论：覆盖记账、⊤ 块降级回整程序展开、覆盖区不重叠校验。

**验收**：
- ENSRegistry 端到端跑通（127 块，⊤ 块 0 个，应当全覆盖）；
- 降级用例：人为把一个块标记为 ⊤，验证它退回展开且 observable 不重复记账。

### 阶段 5：大合约与待攻克清单

CErc20 / Safe 端到端，产出「可专门化块证完 + ⊤ 块清单」。

**验收**：给出三个数字——可专门化块的通过率、⊤ 块数量、总墙钟。对比基线（整程序 880s 跑不完）。

### 阶段 6（可选，收益导向）：⊤ 源站点攻坚

按 §4.5b 攻克 CErc20 28 个 / Safe 8 个源站点，度量 ⊤ 块回落比例。

---

## 7. 结论强度

### 7.1 本方案（落地后）证明什么

对通过全部义务的**可专门化块**：块内所有路径的 observable 等价，且块间转移保持 `R`。全程序结论 = 块结论按 §2.4 ④ 的覆盖记账合成。

### 7.2 不证明什么

- **observable 一致是"当前建模投影内"的一致。** `OBSERVATION_KEYS` 十项中**没有 logs**；status 与 gas 已纳入，revert 以 `status_code` + return memory 体现。不得读成"完整 EVM 外部可观察行为已覆盖"。
- **不证终止**（§2.5）。v1 是 partial correctness，SCC 上的 ranking function 不在范围内。
- **⊤ 块不被本方案覆盖**，它们退回整程序展开——而整程序展开在 CErc20/Safe 上跑不完。所以这些块**实际上未被验证**，必须在报告里显式列出，不得以"整体 VERIFIED"掩盖。
- **host gas 公式与 `HOST_GAS_UPPER_BOUNDS` 仍是外部人工审计所得的 assume。**
- **pc↔addr 映射是结构性证据**（指纹全覆盖 + 锚点交叉验证），不是定理；它进指纹，codegen 变更后自动失效。
- **深度类的 2.5× 依赖影子栈 100% 命中**（§3.2 的悬崖性质）。这必须是被检查的结构前提，不是假设。

---

## 8. 验收基准

| # | 基准 | 判据 |
|---|---|---|
| 1 | pc↔addr 映射反向用例 | 改一个块的 `static_gas`，映射构造器**整体拒绝**而非局部错位 |
| 2 | 返回臂集差集用例 | x86 臂集真子集于 EVM `immediate_set` 时，差集不可达证不出必须拒绝（不得假设相等） |
| 3 | 三维闭包用例 | 人为构造递归 ⇒ 不动点不收敛 ⇒ fail-closed；非递归合约必须收敛 |
| 4 | provenance 无关性 | 喂错误的函数边界推断，**结论不得改变**（只有性能/报告改变） |
| 5 | 影子栈悬崖哨兵 | 强制一次保守回退，验证系统 fail-closed 而非静默产出错误深度类 |
| 6 | 块内 OOG 用例 | 有充足具体预算时，消费端仍不得把块定理里的 OOG 分支判为不可达 |
| 7 | 降级混用用例 | ⊤ 块退回展开时 observable 不重复记账、gas 不双重扣减 |
| 8 | 分量遗漏哨兵 | 漏登记任一 `R` 分量，`_assert_component_symmetry` 必须当场抛错 |
| 9 | 收益回归 | 三个最坏块（ENS 1455 / CErc20 5343 / Safe 6275）联合注入后收敛，判死率 ≥93% |
| 10 | CALLDATALOAD 前置门 | 未补 per-hit proof 时开启 CDL summary，必须被拒绝而非静默使用 |

> **验收基准必须进常规回归。** 主方案踩过的坑：验收基准 1 是 `skipif(not RUN_LOOP_INDUCTION_ACCEPTANCE)`，连 `-m slow` 都跑不到，长期红着无人发现，而"全量绿"完全看不出来。**默认 skip 的验收测试会静默腐化。**

---

## 9. 已否决的路线（不要重走）

| 路线 | 否决依据 |
|---|---|
| 区间不变式（不改剪枝器） | 实测无效：assumption 不进 `_handle_jcc` 的纯静态 simplify（§4.3） |
| 区间 + solver 剪枝器 | 实测净负：133 次调用 46.5s，仍 TIMEOUT（§4.4） |
| 只注入 `msize` 不注入 `fmp` | CErc20 5343 仍 TIMEOUT（§4.1） |
| 用 `fmp - msize` 关系式不变量 | `fmp-msize=0x20` 看似占 88–99%，但全部由平凡的序言态支配；去掉后差值散成 6 种值。**无可用关系式不变量** |
| 静态 pad ∩ `immediate_set` 建返回边 | 丢帧 ⇒ 假环复活 ⇒ 深度 -41001（§3.2） |
| 补全 `_TERMINAL_ERROR_STATUSES` 救出口配对 | 主方案 §9.0 实测净负（7→6）；且块级方案下出口配对整体消失（§5.2） |
| 用静态路径计数评估 havoc 机制 | **第二次踩坑**。CDL 块 2⁷³ 静态路径实际能跑完（105–215 条终态），per-byte `cmp/jb` 是线性嵌套链、solver 剪枝收成 O(33·n)。**真正的瓶颈量纲是每路径墙钟，不是路径数** |
| 把循环归纳当性能手段 | 主方案 §0.5 自己写明"解决封闭性，不解决可扩展性" |

---

## 参考

- `docs/循环处理增强方案.md` — 主方案（本分支已落地）。§0.5（收益边界四条）、§4.1（`R` 分量）、§4.1.3（镜像闭包）、§4.1.4（深度类两条义务）、§4.2（三条查询）、§4.6（OOG 谓词桥接）、**§9.0（真实覆盖率：13 对循环 6 对被拒，端到端从未跑通）**
- `docs/cutpoint泛化方案.md` — 已否决方案。§2.2（cutpoint 集合）、§3（pc↔addr 映射）、§4.2–4.6（义务形式）仍适用；§1.3 的否决数据见本文 §1.2 的修正
- `verification/cutpoint_relation.py` — `CutpointRelationSchema`、`_COMPONENTS`、`build_havoc`、`CutpointModelRangeError`
- `verification/loop_induction.py` — `run_evm_segment`(362) / `run_x86_segment`(459) / `_check_depth_transition_closure`(1475) / `exit_pairing`(1383，待替换)
- `verification/segment_validation.py` — `SegmentStructuralValidator`
- `common/path_observation.py:6` — `OBSERVATION_KEYS`（十项，无 logs）
- `common/oog_bridge.py` — OOG 谓词先证后桥接
- `x86_64/summaries/calldataload.py:550` — `_requires_concrete_low_offset`；`x86_64/cfg_executor.py:735` — fallback 只对 `SummaryPreconditionError`
- `$GOPATH/src/github.com/bcds/go-hpc-evm/evm/aot/impl_amd64.go` — `compileEVMTag`（12 条序言）、`compileEVMCALLDATALOAD`(2897)、`compileEVMJUMP`（返回比较链与 `isValidJumpDest`）、`compileExitFromNativeCode`（内联错误退出）
- 实验脚本（待固化）：`tmp/tag_align_survey.py`、`tmp/depth_class_provenance.py`、`tmp/msize_absint.py`、`tmp/msize_joint_inject.py`、`tmp/exp1_jcc_pruning.py`、`tmp/exp_summary_blocks.py`
