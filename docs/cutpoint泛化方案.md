# cutpoint 泛化方案

> **状态:2026-09-02 实测后否决当前形态。不要实现。**
>
> §1.3 的端到端实测推翻了本方案的收益前提:在 ENSRegistry 上 cutpoint 化让 EVM 侧路径数从 73 涨到 3038(**净负 40 倍**);在 CErc20 上它把"枚举不完"换成了"深度类不动点不收敛",并没有解决问题。
>
> **推翻的是收益,不是机制。** §2(cutpoint 集合而非函数摘要)、§3(pc↔addr 权威映射)、§4.2–4.6 的义务形式仍然成立且有独立价值;§3 的映射已在主方案里落地。重启本方案需要先解决 §1.3 指出的两笔固定罚金,判据见 §7。

## 0. 概述

`docs/循环处理增强方案.md`(下称主方案)把 cutpoint 固定选在**循环头**。但 cutpoint + havoc + 三条查询这套骨架**不绑定循环头**——它只要求切开后剩余的段图无环。把 cutpoint 移到 Solidity 内部函数的入口与返回点,可以让"函数体在每个调用点重复展开"的乘法代价变成一次证明多处引用。

四处核心判断:

1. **不做"函数摘要",做"cutpoint 集合 + 段摘要"。** 实测发现 Solidity 产物里"函数"这个概念本身不可靠恢复(§2.1:尾调用链、continuation 当参数)。而健全性根本不需要恢复它——需要的只是一个 cut 后无环的 cutpoint 集合加覆盖论证。**调用/返回 provenance 因此退出信任链,降级为调度启发式**(§4.5)。这条**成立**。
2. **新增两个必须设计的问题**:pc↔addr 权威映射(§3)与摘要表示/消费端(§4.6)。这条**成立**;§3 已在主方案里以 TAG 序言指纹的形式落地。
3. ~~v1 不换符号 frame,用具体深度类专门化(只差 2.3×)~~ —— **被 §1.3 推翻**。深度类倍增实测是 4.4×(ENS)到 ~17×(CErc20),是两笔主罚金之一,不是尾部优化。
4. **收益前提整体被 §1.3 推翻。** 静态路径计数在**两个方向上都错**:它高估了 BASE(忽略执行器的具体值剪枝),又低估了 CUT(忽略 havoc 的过近似)。这是本文档此前最核心的方法论错误。

---

## 1. 动机与收益量化

### 1.1 两条相互独立的收益轴

| 轴 | 症状 | 期望 cutpoint 怎么消除 | 实测结果(§1.3) |
|---|---|---|---|
| **路径数** | 同一函数体在 N 个调用点各展开一遍,前缀路径数与体内路径数相乘 | 函数体只证一次,调用点引用 | **反向**:ENS 73 → 3038 |
| **表达式规模** | 内部函数调用链让 Z3 项线性膨胀(ENSRegistry ~35 节点/步),`Z3_simplify` 占 61% 墙钟 | cutpoint 的 havoc 把项截断成新鲜符号 | **反向**:ENS 路径条件最大 AST 305 → 4732 |

两条轴都实测为反向。**表达式规模那一轴的反向尤其反直觉**——直觉是"havoc 用新鲜符号替换长链所以项会变短",实际是 havoc 让原本具体的栈值变符号,下游算术与分支条件反而堆得更大。这条直觉错误是本方案立论的起点,必须记住。

### 1.2 静态路径计数(**已被 §1.3 证伪,保留作为反面教材**)

口径:EVM IR 块级静态 CFG,与 `verification/loop_pairing.build_evm_cfg` 一致。

| 合约 | 块数 | 全展开 | 理想摘要 | 具体深度专门化 |
|---|---|---|---|---|
| CErc20 | 723 | 2.45 × 10¹⁴ | 325 | 753 |
| ENSRegistry | 127 | 360 | 63 | 80 |
| Safe | 742 | n/a(含环) | 179 | 发散 |

**这张表不能用来预估收益。** §1.3 的实测显示两列都错:

- **"全展开"被高估。** 静态计数不知道符号执行器会用具体值把分支静态判死。ENSRegistry 静态 360 条,实测只有 **73** 条。
- **"摘要"被严重低估。** 静态计数假设段内路径与上下文无关,而实际的段要从 **havoc 状态**出发,会探索上下文中根本不可达的路径。ENSRegistry 静态 63/80 条,实测 **3038** 条。

保留这张表是为了记住这个教训:**评估一个基于 havoc 的机制,不能用静态 CFG 路径计数**。唯一有效的口径是端到端跑真实符号执行器(§1.3)。

Safe 的深度类发散(6 万+)结论仍然成立,根因是 6/154 个调用点的返回地址无法唯一恢复(§2.1),静态分析连出一条不存在的边、把一段变成净栈深非零的环。这是 §4.5 那条纪律的实证:**provenance 失败若不 fail-closed,后果是静默的 CFG 污染**。

### 1.3 端到端实测:方案被证伪

口径:真实的 `verification.loop_induction.run_evm_segment`(即项目自己的 EVM 符号执行器),整合约符号 calldata(`calldata_size_max_bytes=2⁶³−1`、`abstract_calldataload_words=True`,与 `test_verify_ext_*_whole_contract` 一致),`max_depth=100000`。

- **BASE** = 不设 cutpoint,从 entry 跑到全部 terminal(当前管线的行为);
- **CUT** = cutpoint 取 §2.2 的集合(循环头 ∪ 调用目标 ∪ return pad),entry 段 + 对每个 `(cutpoint, 深度类)` 从 `CutpointRelationSchema.build_havoc` 的状态跑各自的段,并按 §4.2 跑深度类**不动点**直到收敛。

| | ENSRegistry | CErc20 |
|---|---|---|
| 块数 / cutpoint 数 | 127 / 47 | 723 / 264 |
| **BASE** 路径 / 时间 | **73 / 3.0s** | **12 分钟未跑完** |
| BASE 路径条件最大 AST | 305 | — |
| **CUT** `(cutpoint,深度)` 实例 | 205(收敛) | **≥4482(未收敛**,预算 4000 用尽,队列仍有 482) |
| **CUT** 路径 / 段执行时间 | **3038 / 13.1s** | **≥57791 / ≥282s** |
| CUT 路径条件最大 AST | 4732 | 6045 |
| 深度类 / cutpoint | 4.4 | ~17 |

**结论一:ENSRegistry 上净负 40 倍。** 路径 73 → 3038,最大条件 AST 305 → 4732,墙钟 3.0s → 13.1s。三项全劣。

**结论二:CErc20 上不是"有效",是换了一种不可行。** BASE 枚举不完;CUT 的深度类不动点在 4482 个实例后**仍未收敛**。把一个"枚举不完"的问题换成一个"不动点不收敛"的问题,没有解决问题。

#### 两笔固定罚金

**(a) havoc 过近似 ≈ 3.2×。** 同一 cutpoint、同一深度,从**实际到达状态**跑 vs 从 **havoc 状态**跑(ENSRegistry,12 个到达点):

```text
段内路径   具体到达 24  →  havoc 76      3.2×
条件 AST   具体 63      →  havoc 113–134  约 2×
```

成因:真实执行中栈上大量是具体常量(tag、`0x40`、位掩码),havoc 后全部变符号,下游每个 `JUMPI` 都分叉。**这笔罚金是可复用性的代价,不是实现缺陷**——摘要要能被多个 caller 引用,就必须在 havoc 状态上证明。

**(b) 深度类倍增 4.4×(ENS)/ ~17×(CErc20)。** 一个 cutpoint 要按每个绝对深度类各证一条定理。这条直接推翻了 §0 旧的第 2 条:符号 frame 不是"2.3× 的尾部优化",它是两笔主罚金之一。

两笔相乘约 **14×(ENS)/ 54×(CErc20)**,而 cutpoint 的复用收益必须先跨过这个门槛才谈得上净正。

#### 收益导向的选点不能救

"只切被多个调用点共用的函数"是自然的优化方向。实测**反而更差**(ENSRegistry,阈值 = 最少调用点数):

| 选点 | cutpoint 数 | 实例 | 路径 | 最大条件 AST |
|---|---|---|---|---|
| BASE 不切 | 0 | — | **73** | **305** |
| ≥1 个调用点(全切) | 47 | 205 | 3038 | 4782 |
| ≥2 | 30 | 136 | 2971 | 4829 |
| ≥3 | 20 | 59 | 3823 | 13107 |
| ≥4 | 17 | 47 | 5501 | 13386 |

切得越少,段越长、跨越的分支越多,路径与条件规模单调恶化。**cutpoint 数与总代价不是单调关系**,存在一个既不能多切也不能少切的困境。

#### 三条未测项,全部指向更差

1. **x86 侧未测。** 而项目的真实瓶颈在 x86(既有剖析:x86 符号执行阶段 `Z3_simplify` 占 61%)。x86 侧还会额外坏:cutpoint 处返回地址被 havoc 成符号后,`cmp/je` 返回比较链一条臂都剪不掉(CErc20 最大 31 臂 ⇒ 33 条路径),而 `_handle_jcc` 的 `simplify` 正是主力剪枝器(静态判死 97.7%)。
2. **`R` 的证明义务未计入 CUT。** 每个 cutpoint 到达都要证一次 `R` + 域约束 + 结构前提;CErc20 就是 ≥4482 条。这些成本只加在 CUT 一侧。
3. **真实成本是 EVM × x86 配对,不是单侧路径数。** 上表只统计 EVM 侧。

三条都让 CUT 相对更差,因此结论是稳健的:**不是"测得不够细所以未必",而是"再细只会更糟"**。

### 1.4 调用形态普查

| 合约 | resolved_multi JUMP(返回点) | 返回 pad | 调用点形态块 | 返回地址可唯一恢复 | 函数入口 | 递归 |
|---|---|---|---|---|---|---|
| CErc20 | 83 | 192 | 230 | 215 (93%) | 69 | 0 |
| ENSRegistry | 22 | 33 | 30 | 30 (100%) | 14 | 0 |
| Safe | 83 | 166 | 154 | 148 (96%) | 64 | 0 |

CErc20 的 83 个返回点里 **51 个 `immediate_set` 只有一个元素**——即该"函数"只被一处调用,返回跳退化成经栈的静态跳。真正多调用点的只有 32 个。

绝对深度类分布(CErc20,69 个函数入口):`{1类:28, 2类:7, 3-8类:9, 11-26类:11, 37类:1}`,Σ = 313。即 **40% 的函数只在一个绝对深度被调用**,长尾最深 37 类。

### 1.5 复现方法

无需新脚本即可复现的部分:`verification.loop_pairing.classify_raw_jump_ops` / `analyze_evm_blocks` 给 JUMP 形态分类;`x86_64.loop_analysis.analyze_x86_blocks` 给 x86 侧。

需要新写的部分(建议随 §7 路线图第 0 项一并固化成 `tools/` 下的普查脚本,不要留在临时目录):

- **净栈效应**直接取 Go 导出的 `EVMBlock.stack_depth`——已校验它就是块的净栈效应(CErc20 709/723 与手算 delta 表一致,分歧全在 `LOG`/`SSTORE` 这类 `param` 不是操作数个数的 op 上,以 Go 为准)。**不要自己维护 delta 表。**
- **静态 JUMP 不 pop**:Go 已把 `PUSH target; JUMP` 折成 `JUMP immediate=target`,块里没有对应的 PUSH。按"pop 1"算会让 709/723 掉到 171/723。
- **返回地址 provenance**:调用点块压入的 pad 集合 ∩ 被调方返回点的 `immediate_set`,交集唯一才算恢复成功。

---

## 2. 机制

### 2.1 为什么不做"函数摘要"

旧版把 cutpoint 定位成"函数入口/返回点",隐含假设"函数体 = 从入口可达、以自身返回点结束的块集合"。**这个假设在实测中不成立。** Safe 的两个真实形态:

**(a) 尾调用链——返回地址被链条深处消费。**

```text
块 2091:  PUSH 2103 (pad); DUP6; DUP11; DUP11; DUP6; JUMP → 6935
块 6935:  DUP2; MLOAD; PUSH 6948 (pad); DUP3; PUSH 32;  JUMP → 7082   ← 不返回,尾调用
块 7082:  PUSH 0; DUP1; PUSH 7094 (pad); DUP4; DUP6;    JUMP → 11424  ← 继续尾调用
```

6935 自身没有返回点,2103 由链条深处的某一环消费。"函数体以自身返回点结束"直接失效。

**(b) continuation 当参数传递。**

```text
块 7917:  PUSH 7931; DUP6; PUSH 7799; DUP10; DUP10; JUMP → 7082
```

一次压入两个 continuation:7931 是自己的返回地址,7799 作为参数交给被调方。这是高阶控制流,"返回目标 ∈ 本函数的 pad 集合"这条判据在这里没有唯一解。

**结论:把"函数边界恢复"放进信任链是错误的设计方向。** 它既不可靠(§1.3 的 93%/96%),失败时又是静默污染(§1.2 的 Safe)。

### 2.2 正确的抽象:cutpoint 集合 + 段摘要

健全性只需要三件事,**都不需要知道什么是"函数"**:

```text
(H1) 无环:  以 cutpoint 集合 C 切开后,每个段(cutpoint → 下一 cutpoint 或 terminal)内部无环
(H2) 覆盖:  从 entry 出发的每条路径,要么到 terminal,要么撞上 C 中某点;
            每个段同理。任何未被覆盖的边 ⇒ fail-closed
(H3) 闭包:  每个 cutpoint 的到达深度类集合对"段转移"封闭(§4.2)
```

`C` 怎么选是**纯粹的调度问题,选错只影响收益不影响结论**:

- 选少了 ⇒ 某个段内出现环 ⇒ (H1) 检出 ⇒ 拒绝或退回展开;
- 选多了 ⇒ 段更碎、cutpoint 上要证的 `R` 更多次 ⇒ 慢,但仍然正确;
- 选错位置(把一个非函数入口的块当 cutpoint)⇒ 没有任何后果,它就是一个普通切点。

v1 的 `C` 取:**所有 EVM natural-loop 头 ∪ 所有被静态 JUMP 跳入的 TAG 块 ∪ 所有 return pad**,再按 §7 的收益排序裁剪。这个集合不依赖任何 provenance 分析。

### 2.3 三条查询的推广

主方案的 ①②③ 原样适用,只是段的两端换了:

```text
① 到达(原 Base)  : entry 或上游 cutpoint → 本 cutpoint,证实际到达状态满足 R + 域约束 + 结构前提
② 段定理(原归纳步): 从 havoc 的 cutpoint 状态出发,执行到下一批 cutpoint 或 terminal,证
                    (a) 两侧走同一条出边(含返回目标选择一致,§4.3)
                    (b) 到达任一下游 cutpoint 时 R 保持
                    (c) 段内 terminal 路径(REVERT/OOG/栈错误)当场证配对 observable 等价
                    (d) 若本 cutpoint 处在 SCC 上(即真循环),额外要 §4.2②(e) 的终止义务
③ 续接           : 由下游 cutpoint 的 ① 承接,不再是独立查询
```

**与循环归纳的差别在 ②(d):** 非 SCC 的段定理是普通的 Hoare 式段定理,不需要归纳、不需要 ranking function、不需要终止证据。只有 cutpoint 图上的 SCC(真循环、递归)才退回归纳。这一点旧版没有区分。

### 2.4 与循环归纳的关系

旧版写"循环归纳是本机制的特例(回边 = 函数调用自己)"。**这个说法要收紧成类比。** 在证明图层面二者共享骨架,但语义上不等价:

| | 循环回边 | 调用/返回 |
|---|---|---|
| frame | 复用同一个 | 新建,返回时恢复 |
| 返回地址 | 无 | 有,且是符号参数(§4.3) |
| 需要什么 | 不变式 + ranking | 前后置关系 + call/return 匹配 |

准确表述:**循环归纳与段摘要共享 cutpoint / havoc / 关系证明 / 两层证书这套骨架**。主方案里下列纪律因此**原样适用**,不需要重新论证:

- `R` 的分量必须四处齐全(进 `R` / 进 havoc / 进 ①与②的证明义务 / 进指纹);
- 凡 by construction 耦合的量都必须有对应证明义务(含主方案 §4.1.3 的镜像闭包);
- havoc 纪律:跨段演化的量给任意符号,绝不给具体常量;
- theorem / certificate 两层拆分与缓存键构成;
- 查询极性、vacuity 守卫、prove-or-reject、归纳步 SAT ≠ bug。

---

## 3. 前置能力:EVM pc ↔ x86 地址的权威映射

段摘要要求两侧 cutpoint **成对**。当前仓库没有块级跨侧映射:`verification/call_site_mapping.build_call_site_mapping` 只覆盖 host bridge 站点且是顺序 zip;`loop_pairing.pair_natural_loops` 按 header 排序逐位配对、只校验 latch 数。把这两者当 cutpoint 配对源,等于把配对正确性建立在无守卫的顺序假设上。

**实测结论:权威映射可以建,而且有两个相互独立的证据源。**

**(a) 完整 TAG 序言指纹 —— 全覆盖。** `compileEVMTag`(`$GOPATH/src/github.com/bcds/go-hpc-evm/evm/aot/impl_amd64.go`)是 10 条定长模式:

```text
mov  rax, [r13+0x70] ; cmp rax, $StaticGas      ; jb  <OOG>
sub  rax, $StaticGas ; mov [r13+0x70], rax
mov  rax, [r13+0x30] ; cmp rax, $MinDepth*32    ; jb  <Underflow>
                       cmp rax, $MaxDepth*32+1  ; jae <ReachLimit>
mov  r14, [r13+0x38] ; add r14, rax
```

取三元组 `(static_gas, min_depth*32, max_depth*32+1)` 作指纹,与 EVM 块按 pc 升序 / 地址升序单调对齐:**CErc20 723/723、Safe 742/742、ENSRegistry 127/127 逐位一致**。

> **必须换掉 `is_evm_tag_header`。** 现有实现(`x86_64/loop_analysis.py`)只看三条指令(`mov [r13+0x70]` / `cmp` / `jb`),而那是 `makeStaticUseGas` 的公共前缀,动态 gas 路径也生成。它过匹配 2.1×:CErc20 命中 1522 个 vs 723 个真实块。用它定位 cutpoint 会直接引入错配。

**(b) 返回比较链锚点 —— 27% 覆盖、零冲突、独立。** resolved_multi JUMP 的 x86 下降形态里,`CMPQ rax, $pc` 的立即数就是 **EVM 目标 pc**,紧随的 `JEQ` 的 rel32 就是**对应 x86 地址**(纯立即数编码,无跳转表)。CErc20 提取 192 对、Safe 166 对、ENS 33 对,全部落在 x86 块起点上、与 (a) 交叉验证 **100% 吻合**。

**设计要求:** 映射构造器以 (a) 为主、(b) 为交叉校验,**任何一位对不上就整体拒绝**(fail-closed),不做局部修补。映射本身进证书指纹——它是所有 cutpoint 配对的根依据。

---

## 4. 设计决议

### 4.1 frame 参数化 —— 旧决议已被 §1.3 推翻

> **旧决议(2026-09-01):v1 不引入符号 frame base,因为它只值 2.3×。**
> **该判断错误。** §1.3 实测深度类倍增是 4.4×(ENS)/ ~17×(CErc20),是两笔主罚金之一,且 CErc20 的深度类不动点根本没收敛。具体深度专门化不是"够用的 v1",它本身就是方案不可行的一半原因。
>
> 但**消掉它也救不了方案**:另一半罚金(havoc 过近似 3.2×)与 §1.3"选点困境"都独立存在。因此符号 frame 从"尾部优化"变成"必要但不充分条件"。

以下关于符号 frame **技术可行性**的分析仍然有效,重启时直接用。

**符号 frame 的真实阻塞点(与旧版记述不同)。** 需要更正一条流传的判断:x86 侧 `go_function_semantics` 那条 `sp: int` 链**不是**阻塞点。那个 `sp` 是 `locationStack.sp`,`compilePreambleForBlock` 每块开头清零,是**块内相对量、编译期常量**(实测有负值 `-8`,绝对深度不可能为负)。绝对 frame base 在两侧**早已是符号**(`R14_stack_base` 是 BitVec),地址算术全走 Z3 Array,`common/store_forwarding.linearize_address` 支持"符号项 + 常量和"的转发。

真正被卡死的只有**一个量**:`callengine_stack_byte_offset`(`[r13+0x30]`)。它符号化会引发两件事:

1. `CutpointRelationSchema.build_havoc` 直接 `raise CutpointModelRangeError`(`verification/cutpoint_relation.py`),且该处注释记载这条路**已经走过并被取消**——符号 offset 正是 no-stack-limit envelope 的实现;
2. TAG 序言的栈下溢/超限检查两条 `cmp/jcc` 泡开成不确定。x86 侧 `_handle_jcc` 唯一的剪枝器是 `not is_false(simplify(cond))`(纯静态、无 solver),符号 offset 下一条都剪不掉 ⇒ **每个 TAG 块 ×3 路径**。723 个块的合约,这一项就能把 §1.2 省下的收益吃回去。

**v1 方案:**

```text
theorem key 含具体 depth class k;沿用 build_havoc(stack_depth=k) 的绝对编码
live_stack_prefix 仍按 range(k) 展开
超出 max_stack_byte_offset ⇒ CutpointModelRangeError ⇒ 降级(不放宽边界)
```

同一 cutpoint 的多个深度类各证一条定理,由 §4.2 的闭包义务保证枚举完整。CErc20 的代价是 313 条定理实例(69 个入口),ENSRegistry 是 23 条(14 个入口)。

**符号 frame 的重启判据(留给 v2):** ①(H3) 的深度类不动点在目标合约上不收敛,或 ② 深度类总数超过段数的 5× 且实测成为瓶颈。届时的编码方向是主方案 §5.2 同款的 lambda 闭式(`live_stack_prefix` 用 `Lambda(i, ...)` 而非 `range(k)` 展开),并且必须同时给出 TAG 栈检查在符号 offset 下不泡开的办法——**不能重蹈 envelope**。

### 4.2 深度类闭包 —— 从 latch 推广到 cutpoint 图

主方案 §4.1.4 的两条义务原样推广,只是"latch 边"换成"段转移边":

```text
(i)  到达覆盖:任何到达 cutpoint C 的段转移,其携带的深度类都在 C 的已登记集合内
(ii) 转移封闭:每个已登记类的段出口,只转移到下游 cutpoint 的已登记集合内
```

实现形态是 cutpoint 图上的**不动点**:从 entry 的 `{0}` 出发,反复用段转移传播深度类直到稳定。

**递归检测由此免费获得,且比语法判据更强。** 递归调用让深度类无界增长,不动点不收敛。因此:

```text
不动点在预设轮数内不收敛 ⇒ fail-closed 拒绝,报告"深度类不封闭(疑似递归或未识别的栈增长循环)"
```

这**不需要**单独的调用图 SCC 分析,也不依赖 provenance——它检测的是实际的无界增长而非语法形状。§1.2 里 Safe 的 6 万类正是这个机制该拦住的东西。

> 现有实现的一处收紧要求:`_check_depth_transition_closure` 目前把 `registered` 取成 `(self.stack_depth,)`(只含本定理那一个类),Base 登记的其它类会被算作逃逸。方向安全(只多降级),但推广到 cutpoint 图后必须改成全局已登记集合,否则任何多深度类的 cutpoint 都无法通过。

### 4.3 返回目标参数化

**两侧形态(已核实真实 codegen):**

- EVM 侧:`JUMP immediate_set`,多目标、边显式。
- x86 侧:先 `compileLocIsUint64` 检查目标高 192 位为零(不为零 ⇒ 内联 invalid-jump 退出),再是 `CMPQ rax, $pc_i ; JEQ tag_i` 比较链,**目标 pc 以立即数编码、无跳转表**;全不匹配 ⇒ 再内联一份 invalid-jump 退出。错误退出**不是共享 stub**,而是每站点内联三条:`MOVB $8, [r13+0xE0]; MOVQ $sp, [r13+0x28]; RET`(status 8 = `InvalidJump`)。

**义务 1:臂集不对称,不得按数量配对。** Go 侧 `isValidJumpDest` 会**静默丢弃**不在 `jumpTable` 里的目标(编译期不报错),因此 x86 臂集可以真子集于 EVM `immediate_set`。守卫必须写成:

```text
x86 臂集 ⊆ EVM immediate_set                     (结构检查)
∧ ∀ t ∈ EVM immediate_set \ x86 臂集. 证明 dest = t 在本 cutpoint 的 R 下不可达
```

差集**不能假设为空**:那正是"编译器漏掉一个合法跳转目标"这类 bug 的形态,写成相等就把它假设掉了。差集非空且证不出不可达 ⇒ 拒绝。

**义务 2:两侧选中同一目标。** 与主方案 ②(a)"回边/出口决策一致"同类:

```text
R ∧ 段前置 ⇒ (EVM 选中 t) ↔ (x86 比较链选中 t)     对每个 t 各一条
∧ (EVM 无匹配目标) ↔ (x86 落到 invalid-jump 退出)
∧ 溢出支:两侧对 dest 高位非零的处置一致(x86 是 invalid-jump,EVM 侧须有对照物)
```

**路径代价的正确核算(旧版与外部评审都算错了)。** 返回地址在 cutpoint 处被 havoc 成符号后,比较链一条都剪不掉,单个返回跳展开成 **N+2 条路径**(N 臂 + 全不匹配 + 溢出;CErc20 最大 31 臂 ⇒ 33 条)。但这个 N+2 是**每条段定理付一次,不是每个调用点付一次**——它恰恰就是加法结构本身:定理枚举全部返回臂各证一次,调用点实例化时代入自己压入的具体 pad,只取其中一臂。

因此正确的核算是 `Σ_cutpoint (段内路径 × 深度类)` —— §1.2 的第三列已经包含了这一项。**把 N+2 记成收益损失是重复计数。**

> CErc20 的 83 个返回站点里 51 个只有 1 臂,退化成 `cmp + je + invalid`(3 条路径)。这些正是 §7 第 2 步"叶子优先"的天然试验场。

### 4.4 caller-frame live 槽

**v1 决议:沿用绝对表述,不做相对化。** 具体深度类下 `live_stack_prefix` 仍取"从栈底到当前 SP",语义清楚、与现有 `read_x86_stack_slot` 的窗口映射自洽。代价是公式大(深度 37 的 cutpoint 要 37 条 256-bit 相等),但这是可接受的常数。

**符号 frame(v2)才需要的三件事**,一并记在这里以免届时重新发现:

```text
(1) caller frame 作为整体关系保存(一个数组片段等式,而非逐槽展开)
(2) callee 只显式比较自己的参数槽、局部槽与返回值
(3) frame preservation:证明 callee 不写 caller frame 区域(callee-saved 式论证)
    —— 缺了它,摘要在函数体内成立、返回后 caller 读旧局部变量时两侧已脱钩
```

(3) 在 `CutpointRelationSchema` 里应是一个新分量(`caller_frame_preservation`),按 `_assert_component_symmetry` 的纪律同时进 havoc 与义务。

### 4.5 【新增】调用/返回 provenance 的定位

外部评审把"函数边界与调用/返回关系如何可靠恢复"列为方案漏掉的关键问题。**问题是真的,但定位应当反过来:它必须被排除在信任链之外。**

理由是 §2.1 与 §1.2:恢复不可靠(93%/96%/100%),且失败模式是静默 CFG 污染。任何把它放进信任链的设计,都会让证明结论依赖一个启发式。

**决议:**

```text
provenance 分析只用于两件事,两件都不影响结论:
  (a) cutpoint 集合的收益排序(先切哪些点更划算)
  (b) 报告与诊断(告诉人"这个 cutpoint 大概是哪个函数")
它绝不用于:
  (x) 决定段的边界        —— 由 cutpoint 集合决定,§2.2
  (y) 决定返回目标        —— 由 immediate_set 与比较链决定,§4.3
  (z) 决定深度类          —— 由 ① 的实际到达状态决定,§4.2
```

对应地,**"识别递归"也不靠 provenance**,靠 §4.2 的不动点不收敛。

### 4.6 【新增】摘要表示与主验证器消费

这是本方案的**主体工作量**,旧版完全没写。核心事实:**本仓库当前是"两侧各自枚举整程序路径,再对终态做笛卡尔积配对"**——

```text
program_verifier: evm_program.to_z3_paths(...)  与  x86_program.to_z3_paths(...)  彼此独立
equivalence_paths: for evm_index × x86_index    ← 乘法就在这里
比较对象是终态 observation dict,不含程序点、不含中间状态
```

段摘要要把乘法降为加法,**必须先有"关系式同步推进"这一层,而它在本分支是零基础**(`paired_segment_graph` 只存在于 develop-cycle,且主方案 §9 已判定不搬:1 万行单类,其 `_normalize_evm_edge_state` 会与 develop 的 gas 建模双重扣减)。

**同时必须说明:现有 x86 summary runtime 不能承载它。** `X86Summary` 是单侧的(`apply(summary, state) -> state`,挂在 `X86SymbolicExecutor` 上,EVM 侧无对应机制),且强制**唯一** continuation。段摘要的入口是**一对**程序点、出口是**多返回目标**,结构冲突。主方案 §4.5 已有定论:关系式证书不是可分别应用到单侧状态的函数 summary。**可复用的是纪律形状而非类**:`SummaryPreconditionError` 的异常协议、fallback 语义的健全性论证、`assumed_premises` 守卫(summary 不得往 `assumptions` 里补未证前提)、覆盖区不重叠校验。

**模块清单(接口形状,非实现):**

| # | 模块 | 性质 | 职责 |
|---|---|---|---|
| 1 | `verification/pc_address_map.py` | 新建 | §3 的权威映射。TAG 指纹单调 zip + 返回链锚点交叉校验,任一位不一致即整体拒绝;进证书指纹 |
| 2 | `verification/cutpoint_plan.py` | 新建 | `PairedCutpoint(evm_pc, x86_addr, kind, id)` / `CutpointPlan(cutpoints, evm_stops, x86_stops, unpaired_reasons)`。`unpaired_reasons` 非空 ⇒ 拒绝折叠 |
| 3 | `verification/segment_graph.py` | **新建(核心)** | 关系式段推进器。`run_paired_segment(plan, start, state_pair, ...) -> SegmentResult(arrivals, terminal_pairs, defects)`;`defects` 非空即 fail-closed;每个到达点按 ①-align 的**双向**范式证 |
| 4 | `verification/segment_summary.py` | 新建 | 定理/证书两层,与 `loop_certificates` 同构。Key 含:pc↔addr 映射指纹、cutpoint id、depth class、返回目标集合、`R` 版本、`GasCheck` 档、summary_config、aot_profile |
| 5 | `verification/segment_summary_prover.py` | 新建 | 编排 ①②,骨架照抄 `loop_certificate_prover`,四条缓存纪律原样带走(vacuity 拒绝 / range-error 降级 / 只缓存成立的定理 / `require_*` 进 application key) |
| 6 | `verification/cutpoint_relation.py` | 修改 | v1 只需补 `callengine_mirror` 分量(§6 前置项);v2 才动 frame 参数化 |
| 7 | `verification/program_verifier.py` | 修改 | 在两次 `to_z3_paths` 之前插入 `build_cutpoint_plan`;把 `_loop_guard_note` 从"失败附注"升格为**前置守卫**;保留全展开路径作为降级分支 |
| 8 | `verification/segment_validation.py` | 修改(小) | 加一条 reason:段内不得含未被摘要接管的下游 cutpoint(展开与折叠混用会重复记 observable / 重复扣 gas) |

**现成可复用的原语:** `loop_induction.run_evm_segment(blocks, cut_state, entry_pc, stop_pcs, ...)` 与 `run_x86_segment(..., stop_addrs, ...)` 已经支持任意 stop 集合并带 coverage fail-closed——cutpoint 作为 stop 集合是它们的**现成能力,不需要新原语**。`equivalence_paths.check_equivalence_paths` 只吃 observation 列表 + coverage 证书,与"整程序"无耦合,可直接当段终止路径比较器。

**嵌套摘要的组合:** 不内联。证书携带 `callees: tuple[SummaryRef, ...]`,`proved` 是条件性的——

```text
C.proved ⇔ 本地义务全成立
         ∧ ∀ref ∈ callees. 缓存中有对应 proved 证书
         ∧ 实例化参数被证明落在其适用域内
```

段执行遇到下游 cutpoint 自然停住(它在 stop 集合里),不需要新机制。

> **不要重复现有 Tier-1 的分层错误。** 单张 `Tier1LoopCertificate` 只覆盖一个 depth class,"深度类集合完备"只在 `LoopProofOutcome.proved` 那一层才闭合。消费端若只持有证书对象而不持有 outcome,就会漏掉"其它深度类根本没证"。段摘要的证书必须自带完备性结论,或消费端强制持有 outcome。

**段内 terminal(REVERT/OOG/栈错误)的表示:**

```text
inner_terminals: tuple[TerminalClass, ...]
TerminalClass = (status_bucket, evm_condition, x86_condition, observable_proof)
```

- 证明期:按主方案 ②(d) 逐桶证全部 observable;`status` 只作分桶键,绝不作免检依据。
- 消费期:段内 terminal 是**吸收态**,终止即整程序终止、caller suffix 不执行,**因此不产生新的 caller 路径分支**——这正是加法结构的来源。消费端只需 (i) 计入全局 coverage 记账;(ii) 与 caller 到达条件合取;(iii) **不重证** observable。
- **一个必须写死的陷阱**:OOG terminal 的可达性依赖 caller 的实际 gas,而摘要是在 havoc 的符号 gas 上证的。摘要对 OOG 的结论只能是"两侧同时 OOG 且 observable 一致"(主方案 §4.6 先证 `oog_evm ↔ oog_x86` 再桥接),**不能**是"这条路径不可达";消费端不得用 caller 的具体预算把 OOG 分支折死——那是把待证命题假设掉。

---

## 5. 结论强度

**本方案(落地后)证明什么。** 对通过全部义务的合约对:所有 root-to-terminal 路径的 observable 等价,其中经过 cutpoint 的部分由段摘要按 §4.6 的合取条件折叠;所有段内 terminal 按配对桶证明。

**不证明什么。**

- **observable 一致是"当前建模投影内"的一致。** `OBSERVATION_KEYS` 十项中**没有 logs**;status 与 gas 已纳入,revert 以 `status_code` + return memory 体现。§2.3 里"observable 效果一致"必须按此理解,**不得读成"完整 EVM 外部可观察行为已覆盖"**。
- 终止结论仍是条件定理(主方案 ②(e) 六项前提),且只对 cutpoint 图上的 SCC 才需要。
- host gas 公式与 `HOST_GAS_UPPER_BOUNDS` 仍是外部人工审计所得的 assume。
- §3 的 pc↔addr 映射是**结构性证据**(指纹全覆盖 + 锚点交叉验证),不是定理;它进指纹,codegen 变更后自动失效。

**当前状态下不会造成假绿:** Tier-1 证书链在生产管线里没有消费端(`prove_loop_certificate` 生产调用点为 0),本方案同样尚未实现。**但也因此,本方案描述的收益一分未兑现。**

---

## 6. 前置阻塞项(必须先关闭)

按"关不掉就别开工"的顺序:

**(B1) `R` 的镜像闭包缺口(假绿方向)。** CALLENGINE side-channel 属性 ↔ `[R13+off]` limb 的一致性未进入证明义务,实测 5/5 字段接受陈旧 limb(主方案 §4.1.3、§9)。**段摘要会把这个缺口按 cutpoint 数量放大**——每个 cutpoint 的 ① 都只证属性、允许 limb 陈旧。

**(B2) `require_termination=True` 下证书 `proved` 恒为 False。** `TerminationEvidence.external_premises` 里 `no_unidentified_inner_loop` 与 `all_sccs_cut_or_certified` 硬编码 `discharged=False`,导致默认档拿不到任何一张 proved 证书(端到端 prover 测试全部显式传 `require_termination=False` 绕开)。消费端接上前必须提供这两条的兑现渠道:前者 ← 结构守卫升格为前置门(§4.6 模块 7),后者 ← §4.2 的深度类不动点。

**(B3) sp 无法定成常量时静默跳过 Go 函数语义。** `x86_64/cfg_executor.py` 在 `_extract_stack_pointer` / `_read_sp_from_memory` 都返回 None 时**只打一条 warning**,既不抛异常也不 `_mark_coverage_incomplete`——host/builtin 的全部语义效果被静默丢弃,且不在 coverage 证书链里。段摘要会更频繁地把执行起点放在非 entry 位置,命中该分支的概率上升。**必须先改成 fail-closed。**

另外两项虽非阻塞,但直接影响本方案的可信度:

- **`is_evm_tag_header` 过匹配 2.1×**(§3),用于 cutpoint 定位会引入错配;
- **①(Base) 首次到达覆盖目前是一个无条件写入的字符串常量**,`proved` 只检查它 `is not None`,实质由上游三道门兑现。推广到 cutpoint 图时应换成携带真实证据对象。

---

## 7. 路线图与验收基准

**当前路线图:无。方案已被 §1.3 否决,不进入实现。**

原路线图的第 1、2 步已在主方案里独立落地(TAG 序言指纹判据、循环折叠消费端),不依赖本方案;第 3 步(收益实测)已执行,结果就是 §1.3。第 4–6 步取消。

### 7.1 重启判据

本方案不是被永久否决,而是**被两笔固定罚金卡住**。任一条件成立后值得重估:

1. **havoc 过近似被前置条件机制压下去。** 纯 havoc 是 3.2× 的根源。正解方向是**带前置条件的摘要**(contract-style):在 cutpoint 上不是"任意状态",而是"满足某个已证不变式的状态"(例如"栈槽 3 取值在返回 tag 集合内"、"`mem[0x40]` 是 ≥ 0x80 的自由指针")。这需要一整套前置条件推断/维护机制,本文档完全没有设计。**做到 3.2× → 1.3× 以内,才谈得上重启。**
2. **符号 frame 消掉深度类倍增**(§4.1),同时不让 TAG 栈检查泡开成 ×3。
3. **出现 BASE 确实跑不完、而 CUT 的不动点确实收敛的合约。** CErc20 两条都不满足(BASE 跑不完,CUT 也不收敛),所以它不是这个判据的证据。

三条里 1 和 2 必须**同时**满足——只做一条,罚金仍在 3–17× 量级。

### 7.2 若重启,验收基准

(在主方案 13 项之外新增)

14. **pc↔addr 映射反向用例**:人为改动一个块的 `static_gas`,映射构造器必须整体拒绝而不是局部错位。
15. **返回臂集差集用例**:构造 x86 臂集真子集于 EVM `immediate_set` 的情形,差集不可达证不出时必须拒绝(不得假设相等)。
16. **深度类不动点用例**:人为构造递归调用,不动点必须不收敛并 fail-closed;非递归合约必须在预设轮数内收敛。
17. **provenance 无关性用例**:故意喂错误的函数边界推断,**结论不得改变**(只有性能/报告改变)。这是 §4.5 那条定位的哨兵。
18. **段内 OOG 用例**:caller 有充足具体预算时,消费端仍不得把摘要里的 OOG 分支判为不可达。
19. **收益回归**:CErc20 的段数落在 §1.2 第三列的量级(~10³),而不是退回全展开。

---

## 8. 与主方案的关系

- 主方案 §6 把"识别并排除 call/return 形态的伪回边候选"定位为达成率优化。本方案落地后它**整体消失**——不再需要把这些候选从循环检测里摘出去,它们就是普通 cutpoint。在此之前形态识别仍是过渡措施,不必追求判据完美。
- 主方案 §7.3 把"符号深度类"列为非目标并归入本文。**本次细化把它进一步推后**:§1.2 表明它是 2.3× 的尾部优化,重启判据见 §4.1。
- 主方案仍有两项未兑现性质(`R` 镜像闭包、主消费端落地),二者都在本方案 §6/§7 的前两步里。**顺序不可颠倒**。

---

## 参考

- `docs/循环处理增强方案.md` — 主方案。§3.3(实证)、§4.1(`R` 分量)、§4.1.3(镜像闭包)、§4.1.4(深度类两条义务)、§4.2(三条查询与 ②(d)/②(e))、§4.5(证书结构与折叠形态)、§4.6(OOG 谓词桥接)、§6(降级管线)、§7.3(非目标)、§9(实现状态)。
- `verification/cutpoint_relation.py` — `CutpointRelationSchema.build_havoc` / `component_goals` / `CutpointModelRangeError`。
- `verification/loop_induction.py` — `run_evm_segment` / `run_x86_segment`(stop 集合分段执行,可直接复用)、`_check_depth_transition_closure`。
- `verification/loop_certificate_prover.py` — 三条查询的编排与两级缓存,泛化后可复用的骨架。
- `$GOPATH/src/github.com/bcds/go-hpc-evm/evm/aot/impl_amd64.go` — `compileEVMTag`(TAG 序言 10 条)、`compileEVMJUMP` / `compileEVMJUMPI`(返回比较链与 `isValidJumpDest`)、`compileExitFromNativeCode`(内联错误退出)。
- `$GOPATH/src/github.com/bcds/go-hpc-evm/evm/aot/engine_evm.go` — `evmNativeCallStatusCodeInvalidJump = 8`、callEngine 字段偏移。
