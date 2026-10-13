# 块级 lock-step 等价验证方案

> **版本**：2026-09-14 修订版。
>
> **状态**：本文规定完整的证明契约、组合规则和验收条件；这些条件成立时，§7 的整程序结论成立。当前代码仍是 PoC，尚未满足全部条件，不能把本文视为实现正确性证书。实现核对基线为 `d51b351`（`块级等价验证方案first version`），差距见 §10。
>
> **目标**：把 EVM IR 块与其 x86 实现区域配对，从明确的块边界关系出发证明有限步行为对应，再用初始状态和逐边闭包组合成整程序的、限定于建模投影的等价结论。
>
> **本次范围**：更新设计文档，不修改验证器代码。历史实验保留在 §12，仅作选型与性能线索，不作为已经完成证明的证据。

## 0. 核心决策与结果语义

### 0.1 采用的路线

主路径按块建立局部定理，登记有限个参数关系 `p=(k,m,f,κ)`；`m/f` 可分别是精确整数或表示符号参数的 `None`，其中 `k` 为绝对栈深，`m` 为 MSize，`f` 为 EVM 字节内存 `mem[0x40:0x60]` 的 256-bit 大端值。`κ` 是可选的返回地址栈槽常量谓词，随同实际 H0/H2 检查。`f` 只是一个内存字，不假设任意 EVM 程序都遵守 Solidity 的 free-memory-pointer 约定。

局部定理证明四类义务：

1. **执行完备且有限推进**：每个合法入口在两侧均能于有限步内到达下一切点或语义终态，不遗漏块内循环、错误或 host 行为。
2. **控制流对应**：包括继续／继续、继续／终止、终止／继续、终止／终止的全部可共现组合。
3. **后继关系与专门化闭包**：继续执行时实际出口落入一个已有后继定理的完整前提。
4. **终态对应**：终止时比较状态码和请求的全部 observable。

全局层另外证明真实入口 Base、核对代码与语义路径覆盖、关闭所有证书依赖。局部定理可以先独立产生，只有组成一个闭合证书图之后才有整程序结论。

**块边界统一放在 TAG 执行之前。** 该处允许 R14 是前一块留下的值；下一块定理必须从这种状态出发执行 TAG，包括重建 R14 之前的 OOG／栈错误路径。不得用较弱的出口关系直接代替较强的入口关系。

### 0.2 结果不能混用

| 结果 | 含义 | 能否代表整程序等价 |
|---|---|---|
| `LOCAL_THEOREM_PROVED` | 一个明确前提下的局部完整定理成立，应用与后继依赖另有记录 | 否 |
| `UNREACHABLE_PROVED` | 在给定已证明到达条件下，该入口或分支不可达 | 否；不能冒充局部定理 |
| `VERIFIED` | Base、全部所需局部证书、闭包、覆盖和请求的证明范围均通过 | 是，限于报告中的模型、输入域与 observable |
| `INCONCLUSIVE` | 有 timeout、unknown、缺证书、覆盖缺口、未证明前提或不支持形态 | 否 |
| `COUNTEREXAMPLE` | 在真实初始输入及模型下重放确认了两侧行为差异 | 否，表示模型内反例 |

局部 havoc 下出现 SAT，可能说明关系过弱或候选域过宽；可以拒绝该定理，但不能未经真实入口重放便报告整程序反例。证明过程中不允许默认创建 `proved=True` 再仅凭“没有记录错误”保留它。

### 0.3 收益与范围

收益来自把跨块的符号表达式传播和路径枚举局部化。总成本近似为：

```text
分析成本 + Σ(各块 × 各专门化实例的段执行与证明成本)
         + Base、闭包、覆盖、证书组合成本 + 已实际发生的降级成本
```

这不是关于块数的无条件线性复杂度保证。参数组合、块内路径、内部循环和 solver 查询仍可能昂贵。框架不要求恢复 Solidity 函数边界；返回地址 provenance 是候选域分析的一种辅助信息。该路线不排斥以后加入函数摘要或更一般的切点。

## 1. 语义对象、输入域与信任边界

### 1.1 被验证的两个程序

固定 EVM IR 程序 `P_E`、x86 字节程序 `P_X`、ABI／AOT profile 和语义配置 `C`。EVM 侧包含本项目 IR 的 TAG gas／栈检查语义；x86 侧从实际解码的指令及已声明的 host 模型执行。本文证明的是这两个模型之间的对应，不自动扩展为解释器、完整 EVM 协议或真实主机执行的正确性。

`C` 必须列出初始 gas 域、gas 扣费模型、observable 集合、内存／地址域、字宽及版本、host 行为与外部前提、summary 配置。改变这些内容就是改变定理。

定义 `A_C` 为公开、冻结的环境前提；`I_C(e0,x0)` 为两侧真实初始状态关系。对同一 calldata、环境、初始 storage 等输入建立对应，不能通过合取两个程序各自临时产生的约束偷偷缩小输入集合。固定输入后，给定共同且一致的 host oracle，v1 要求模型执行确定；若某模型保留非确定性，必须先明确选择的双向行为匹配关系，再扩展检查器，不直接套用 §4 的路径笛卡尔积算法。

共享 host UF 的身份、参数、调用历史和返回状态必须由接口定义及调用点义务支持。不能为了消除差异，把不同参数、不同事件或不同调用顺序强行绑定为同一个自由值。

### 1.2 Observable 的精确定义

`common/path_observation.py::OBSERVATION_KEYS` 当前有十个传输字段：

```text
condition, offset, length, memory, base_addr, has_return_data,
storage, transient_storage, status_code, gas
```

这不是十个互相独立的语义观察量：`condition` 是路径 guard，`base_addr` 是地址解释参数。v1 的终态投影 `O_C` 至少包括：

- 两侧终止状态码及正常／错误／REVERT 分类；
- `has_return_data`，以及适用时的长度和逐字节返回内容，使用各自正确的基址和偏移解释；
- 模型给出的完整 storage 和 transient storage 终态；
- 请求比较时的 gas 终值。

返回偏移本身不要求作为外部行为相等，只要返回内容语义一致。内部内存、栈、return-data buffer 和 host 序号虽然未必都是终态 observable，仍可能影响下一块，必须在边界关系中保持。REVERT／错误下是否回滚 storage、如何形成终态投影，要沿用并明确记载模型定义；模型未实现的真实回滚语义不能写成已经覆盖。

当前投影不含 logs，也不含完整 host 调用轨迹。若任务要求这些行为，必须扩展模型、状态关系、observable 与检查链路，否则不能给出满足该任务的 `VERIFIED`。

### 1.3 可信基础与算法前提

可信基础包括 IR／机器码解析、指令语义、状态与路径公式编码、Z3 的有效 UNSAT 结果、证书检查器，以及公开声明的 ABI／host 模型。本文给出相对于这些基础的数学组合论证，不声称已在证明助手中验证检查器。

每个局部求解前提都必须有来源：

| 来源 | 可用方式 |
|---|---|
| `A_C`、完整入口关系及其域约束 | 作为该局部定理的公开前提；全局应用必须证明入口满足它们 |
| 指令执行产生的分支条件／定义等式 | 编入相应路径公式；按各自侧语义产生 |
| 已成立引理或已经 discharge 的 summary 前提 | 附证据后使用，保留依赖 |
| 分析器猜测、未证 no-overflow、未证 OOG 等式 | 不得直接加入 assumptions |

局部假设即使可满足，也不能说明没有漏掉真实输入。除了拒绝空真，还必须检查 havoc 表示范围、路径完备性与 Base／闭包。

## 2. 块映射、边界与执行区域

### 2.1 候选映射的构造和核验

候选 `M : pc ↔ addr` 可由 TAG 序言模式、`(static_gas,min_depth*32,max_depth*32+1)` 常量和地址顺序产生，再用动态 JUMP 的 `cmp pc / je addr` 链交叉核验。完整指令模式随 ABI／codegen 版本绑定，不把“永远恰好 12 条”当作跨版本公理。

TAG 三元组不唯一；单调 zip、数量和锚点只构成导航证据。v1 对不能整体解释的模式拒绝该候选映射，不局部挪动以掩盖错位。对应是否足以支撑等价，还由真实程序入口、完整段语义、后继地址和终态义务证明。

即使映射错了，只要所有语义义务仍成立，得到的仍是有效对应；不能笼统说“错映射一定假红”。不允许由候选映射本身生成相等的跳转目标或删除未配对的行为。

### 2.2 三种明确的程序位置

| 位置 | x86 位置 | 使用的关系 |
|---|---|---|
| 原始入口 `q_init` | native 程序第一条指令 | 真实初始关系 `I_C` |
| 块边界 `q_B` | B 的 TAG 第一条实际指令之前 | `R_cut(B,p)` |
| 块体入口 `q_body(B)` | TAG 正常检查及 R14 重建之后 | 可选内部关系 `R_body(B,p)` |

原始入口的 R14/R15 加载前缀必须执行或单独证明。v1 将其作为有限的入口适配段：EVM 暂不执行 TAG，x86 执行前缀，到 `q_B0` 后证明 Base。该段不扣一次额外的 TAG gas。

`q_init` 与 `q_B0` 不得因属于同一个解码 basic block 而混为一个位置。若执行器不能在 TAG 指令边界停止，要增加保留指令语义的块拆分／指令级 stop，或证明一个包含前缀的入口专用定理。后续跳到 B0 的 TAG 不能错误地再执行原始入口前缀。

### 2.3 区域覆盖和真实控制转移

冻结区域清单：入口适配段、每块的 x86 实现区域、显式支持的 helper／bridge 区域。每条已解码指令有唯一物理归属，区域边界必须位于指令边界，完整说明代码段；无法解码或无法归属的字节按输入格式规则拒绝，不能默默跳过。

物理归属不等于动态执行只发生一次。共享 helper 可由多块调用，但要有独立证书和返回点契约；v1 未支持该形式时拒绝相应接管。不能因为一条指令落在某个区间内，就宣称从任何 caller 执行它都已证明。

每个段运行到下一已登记切点、语义终态，或显式支持的子证书接口。必须检查实际控制流：

- 跳转到其他块的内部指令不能算作已经到达该块入口；没有专门的中间入口关系即拒绝。
- 跳到未配对地址、漏掉的 fallthrough、未知 indirect target、未处理 host 恢复点都必须产生覆盖缺陷。
- 跨区执行只允许通过登记的后继入口或子证书接口。静态 CFG 仅作候选；完整性依据是未经过猜测剪枝的指令语义。
- **重新进入当前块也要停止。** 初次进入时只豁免这一次 stop，执行至少一个语义步骤后遇到原入口即产生自环边。不得永久从 stop 集中删除当前块。

未到达区域可以不产生局部定理，但必须由 Base 加逐步闭包保证其不被执行，或附在已证明到达条件下的不可达证据；不能采信分析器的“不可达”标签直接排除。

### 2.4 动态 JUMP、非法目标与 host 站点

动态跳转需要比较实际目标选择条件，而不只是静态边数。对 EVM 有、x86 没有的合法成功目标，必须证明其 guard 在入口关系下不可达，否则拒绝；x86 额外成功目标同样检查。非法目标若在两侧均按模型终止，应比较错误终态，不能强迫其不可达。

`immediate_set` 只有在解析／执行语义保证完整，或已证明 `dest` 属于该集合时才可作穷尽候选。集合外路径必须证明不可达或执行已建模的错误语义，不能凭编译器导出的列表直接消失。

一个配对块中可能有多个 CALL／CREATE／builtin 站点。块映射不能自动解决站点对应；必须逐次证明调用种类、参数、顺序、状态更新和恢复地址。顺序 zip 只能提议候选，不能作为语义证据。

## 3. 状态关系与三参数专门化

### 3.1 边界关系 `R_cut`

定义：

```text
R_cut(B,p,e,x) = Running_E(e) ∧ Running_X(x)
                ∧ R_state(e,x) ∧ D_C(e,x) ∧ Spec_p(e,x) ∧ Inv_B(e,x)
p = (k,m,f)
```

`B` 的程序点配对由证书接口检查；`D_C` 是完整域约束；`Inv_B` 默认 True，可容纳后续确有必要且已证明闭合的辅助不变式。模板式 codegen 使关系模板有希望足够，但并不保证所有程序都不需要额外不变式。参数集合本身也是归纳不变式。

现有 schema 的十五个分量作为实现起点，不能仅靠分量名齐全认定语义齐全：

```text
stack_geometry, live_stack_prefix, memory, memory_size, free_memory_pointer,
memory_gas, gas, host_gas_seq, return_data_source, storage,
transient_storage, return_metadata, environment, callengine_environment,
callengine_mirror
```

| 类别 | `R_cut` 要表达的条件 |
|---|---|
| 栈 | EVM SP、callengine byte offset 对应；每个有效栈槽与 x86 栈内存对应；合法表示范围 |
| 内存 | 完整 EVM 内存与 x86 EVM 内存视图对应；基址与地址解释有效；MSize、memory gas、lastGasCost 对应且满足各自模型的派生关系 |
| Gas 与 host | 剩余 gas、影响未来扣费的序号及模型状态对应；与配置一致 |
| 返回数据 | return-data buffer 的内容、长度／来源及 metadata 对应，覆盖未来 RETURNDATA* 读取 |
| 持久状态 | storage、transient storage 对应，供未来读写及 host 使用 |
| 环境与 ABI | 所有未来会读取的环境字段对应；R13／R15 等活跃基址与 ABI 条件正确 |
| 内存镜像 | side-channel property 与真实 CALLENGINE limb 在各自侧一致；两侧 property 相等不能代替镜像闭包 |

**TAG 前不要求 `R14 == stack_base + byte_offset`。** 边界栈值通过 canonical stack base／byte offset 定位，不能继续用尚未重建的 R14 来解释 `live_stack_prefix`。R14 及其他未受关系约束的寄存器／flags 保持任意；若某值在覆盖前会被读取，就必须由真实执行证明该读取无影响，或把所需约束纳入关系并证明到达／保持。

边界放松不适用于任意 host-resume／块内位置；它们必须有自己的关系。terminal 直接使用 §6 的终态投影，不借用一个无后继 TAG 的修复承诺。

### 3.2 TAG 前缀的有限衔接证明

局部块定理包含 EVM 与 x86 的 TAG 语义。可以拆成前缀引理和块体证明，但内部接口必须精确：

```text
R_cut(B,p)
  -- 两侧实际 TAG 前缀 -->
  ① 配对的 OOG／栈错误终态，证明 O_C 等价；或
  ② 两侧均正常，R_body 成立，然后执行块体。
```

`R_body` 包含已重建 R14 的几何关系，以及 TAG 后的真实 gas 等状态；不能仍要求 gas 等于 TAG 前值。进入分支②前，证明重建前的读取、检查顺序、错误状态和 gas 更新均正确。不得在未执行前缀时直接把 R14 写成正确值。

当前 Go codegen 在 `compileEVMTag` 中先执行 gas／栈检查，再重建 R14；“后继 TAG 无条件修复 R14”不作为公理。前缀证书绑定实际指令及 ABI，删除／改坏重建指令必须导致证明失败。

### 3.3 专门化与域约束

```text
Spec_(k,m,f) = SP_E = k ∧ byte_offset_X = 32*k
              ∧ MSize_E = m ∧ MSize_X = m
              ∧ word_E(0x40) = f ∧ word_X(0x40) = f
```

参数须按宽度、非负性、对齐、模型上界检查，不能用位向量截断悄悄接受非法整数。物理栈表示范围与 TAG 的 `min_depth/max_depth` 检查条件要区分：不能把会触发已建模栈错误的输入提前从定理中排除。

上式描述精确专门化。对指定了具体整数的参数，分别相等不能代替等于该整数，也不能用“大于实际 MSize 的常量”代替精确值。动态参数使用另一类合法节点：

```text
Spec_(k,*,*) = SP_E = k ∧ byte_offset_X = 32*k
              ∧ MSize_E = MSize_X
              ∧ word_E(0x40) = word_X(0x40) ∧ D_C(m,f)
```

`*` 在实现中编码为 `None`；每个参数独立选择精确或符号形式。共享内存关系已经蕴含 word 相等，不能把符号节点误解为免除内存比较。默认 `D_C` 包含内存大小对齐、协议模型 cap 和其余完整边界域；增加其他谓词时必须对同一谓词建立 havoc、H0/H2 和身份绑定。节点数有限不要求每个节点表示的参数值个数有限。为多个精确／符号节点建立定理时使用有限析取，允许重叠。

所有 `D_C` 与 `Inv_B` 必须同时进入 havoc 前提、Base、后继闭包和证书身份。内存 cap 等用于限制模型的条件，若不是实际语义不变式，就必须在报告中作为经过 Base／闭包检查的受限输入域。段执行发生超界时先记录未建模行为或覆盖缺陷，不通过事后 assumption 删除该路径。

### 3.4 Havoc 必须覆盖所有被契约允许的状态

安全的参考构造是两侧独立 fresh 状态，加上完整 `R_cut`。为了性能可共享数组／值或使用 canonical 表示，但必须证明这种编码覆盖每个满足 `R_cut` 的状态对，至少在会影响后续语义的状态投影上等价。

共享 snapshot 表达“初始内存对应”是允许的；执行后两侧的更新必须独立。专门化 `f` 时先把 word 写入共同的入口 snapshot，再构造 x86 地址平移视图，不能只更新一侧。证明出口内存对应时比较真实的两侧更新，不重置为入口 snapshot。

`create_initial_state()` 的默认常量不能作为任意块入口事实：未被 `R_cut` 约束的 scratch register、flags、非活跃栈内存、metadata 等都要 havoc，或者有显式的不可观察／先写后读证明。status 则由 `Running` 约束；它不是可随意默认且忽略检查的字段。

分量／镜像登记检查用于发现遗漏，不代替上述表示完整性证明。增加任意新状态前提都要经过“生成、关系、到达／保持、指纹”四处同步与单侧破坏测试。

## 4. 局部完整定理及求解规则

### 4.1 宏步骤与局部推进

在 `q_B` 执行一次宏步骤：消费本块的 TAG 和块体，直到第一次到达下一切点或语义终态。记其结果为：

```text
Continue(B', e') / Continue(addr', x')
Terminal(status, state)
```

raw x86 `RET` 不自动等于语义 terminal。host bridge 的暂离与恢复在 §6.3 中建模；未支持的暂离属于缺陷。每次宏步骤两侧必须实际消耗有限且非零的语义步骤，自环也如此。

v1 局部推进证据可来自：完整探索的有限执行树、经检查的无环区域、带有已证终止条件的内部循环 summary，或其他明确的 well-founded 局部证明。内部 copy-loop 仅证明“若结束则输出正确”还不够。

`max_depth`／墙钟预算是资源限制。触顶、未展开 backedge、executor crash、未知语义或 summary 进度不明均使证书不完整。**路径 guard 的析取覆盖所有输入不能单独证明执行会到达出口**；必须与路径确为实际有限执行及内部循环推进证据共同使用。

### 4.2 路径公式与单侧覆盖

令 `P = A_C ∧ R_cut(B,p)`。两侧段执行分别返回路径 `(g_i, outcome_i, state_i)`、`(h_j, outcome_j, state_j)`。在共享入口符号编码下，每个 guard 表示其侧从该入口执行到相应结果的条件。

两侧均要证明：

```text
P ⇒ OR_i g_i
P ⇒ OR_j h_j
```

并附段执行的语义完整性和有限推进证据。guard 与状态变换必须来自该侧原始语义或已检查的 summary；不能在所有 guard 外围加一个未经证明的过滤条件。

v1 固定输入／oracle 后语义确定。重复路径或重叠 guard 允许存在于表示层，但必须代表相同语义结果，或全部纳入严格比较；不能任意选一条来隐藏另一条。局部 `P` 若 UNSAT，标记不可应用的空域，不能产出可折叠定理；SAT 只解决非空性，不能替代覆盖。

### 4.3 全部跨侧组合

对每个路径对构造 `J_ij = P ∧ g_i ∧ h_j`。只有已证明 `J_ij` 不可满足才能跳过。否则按下表检查；也可直接证明 `J_ij ⇒ Goal`，不要求每对先单独查询 SAT。

| EVM 结果 | x86 结果 | 必需义务 |
|---|---|---|
| Continue | Continue | 实际后继程序点配对，且满足 §5 后继完整关系的析取 |
| Continue | Terminal | 证明 `UNSAT(J_ij)` |
| Terminal | Continue | 证明 `UNSAT(J_ij)` |
| Terminal | Terminal | 证明 `J_ij ⇒ O_C(e_i)=O_C(x_j)`，含状态码 |

terminal 可按 status 分桶以减少查询，但异桶对必须已证明不可共现。不能先只配同 status 再忽略剩余路径。两侧 terminal 数量、桶数量或“双方都存在 terminal”不能构成任何 observable 等价证据。

还应输出按后继／终态分类的 guard 对应证据，便于消费者检查：

```text
P ⇒ (Guard_E(Continue B') ↔ Guard_X(Continue M(B')))
P ⇒ (Guard_E(Terminal s)  ↔ Guard_X(Terminal s))
```

在语义完备、确定的路径集上，这些性质可由全组合检查导出，不必重复求解。但证书必须说明导出依据，不能仅记录一个裸计数。

### 4.4 Solver 结果与前提完整性

所有蕴含用反例形式查询：`P ∧ guards ∧ ¬Goal`。只有 UNSAT 接受。SAT 拒绝当前局部义务；unknown／timeout 不得视为 UNSAT。无 solver 查询也可能有合法的简化／结构证明，但必须有可检查的恒等式或已证引理，不能因跳过所有义务而“零查询成功”。

执行途中新增加的 assumptions 逐项审计来源。特别检查 calldata offset 回绕、memory range、host gas 界和桥接等式：除非是 `P` 的公开组成或已有推导，必须先证明，在成功之后才能用于后续查询。

## 5. 初始到达与专门化闭包

### 5.1 候选域不是到达证明

对每块定义有限候选集合 `S_B`，总体关系为：

```text
U_B(e,x) = OR_(p in S_B) R_cut(B,p,e,x)
```

`tools/call_provenance.py` 和 `tools/msize_absint.py` 可以提议 `S_B`。影子栈、`(pc,k)` 边以及多参数关联能改善精度，但“分析器收敛”“恢复率 100%”“两端集合非空”均不能代替真实状态闭包。

provenance 若建议在返回点只保留某一目标，证明器仍必须在 `R_cut` 下证明其他实际目标不可达。havoc 丢掉了返回地址值时，单有 `k,m,f` 未必足够；可以扩大候选域、加入已证 return-tag／栈槽不变式，或降级。不能把 shadow-stack 的栈顶当成未证假设。

### 5.2 H0：真实入口 Base

对每个允许的真实初始输入及共同 oracle，执行 §2.2 的入口适配段，证明有限推进、覆盖与：

```text
A_C ∧ I_C(e0,x0) ⇒ U_B0(e_entry,x_after_prefix)
```

若允许多个入口，则逐入口证明并核对入口集合穷尽。若适配段可能终止，按 §4 的全组合规则证明其结果；不得只挑正常入口。原始 `I_C` 的输入域不能替换成专门化 havoc，`block.min_depth` 也不是实际入口深度。

### 5.3 H2：逐出口语义闭包

对每个已选择的局部实例 `(B,p)`、每个可共现 Continue 路径对，证明：

```text
J_ij ⇒ OR_(p' in S_B') R_cut(B',p',e_i,x_j)
```

必须包含后继的参数谓词（具体值或符号域）、Running、完整 `D_C`、镜像及 `Inv_B'`。使用出口计算出的 `k'` 而不核对后继集合仍不充分；只证明 `MSize_E=MSize_X`、`fmp_E=fmp_X` 更不充分。

例：块 A 两侧 MSize 均从 96 变为 128，B 只登记 `m=96`。两侧状态等式可以成立，但上述析取为假，因此不能应用 B 的定理。

一个出口可因条件不同进入多个实例，使用 guard 分区或析取证明，不要求整个出口只有一个常量。更改 `S_B'`／`Inv_B'` 后必须重新核对所有依赖它的入边闭包；旧证据不能继续标成完整。

### 5.4 H1 与 H3 的正确位置

**H1（所有实际到达均被覆盖）由 H0 和 H2 沿执行步数归纳得到。** 不必回到整程序路径枚举逐条证明所有到达路径；但也不能省掉 Base 或任何真实出边。

**H3 是候选构造与证书依赖收敛检查。** 若采用不动点分析，要输出真正的稳定集合／剩余 worklist 状态，预算耗尽即不完整；实例数与块数的比值只是成本限制，不是收敛证据。即使分析器没有找到最小不动点，人工或其他方法给出的有限过近似也可被 H0/H2 验证接受。

递归不必导致参数发散，尾递归或有限参数域可以收敛；非递归程序也可能因动态内存使常量专门化不可用。不能用“递归必不收敛／非递归必收敛”作健全性条件。

### 5.5 候选工作流

```text
1. 构造候选映射、S_B、可选 Inv_B；冻结模型配置。
2. 为实际入口证明 H0，登记所需节点与待证明义务。
3. 从各节点完整执行一段，按 §4 检查全部结果。
4. 对每条 Continue 证明 H2，登记该证明依赖的全部后继实例。
5. 若候选集合需要扩大或关系需要改变，更新版本并重检受影响入边及局部定理。
6. 没有剩余必需义务、缺失节点或未验证依赖后，才封闭全局证书。
```

worklist 为空必须表示所有已产生的证明义务都关闭，不能仅表示“所有已知候选都尝试过”。遗漏的后继由步骤3的真实执行产生缺陷。不可达候选可不纳入最终证书，但要重证它的排除或其他实例对实际到达的覆盖。

## 6. Observable、Gas 与 summary

### 6.1 完整状态传递为默认接口

v1 不引入新的“observable 增量相加”语义。storage、transient storage、内存、gas 和影响未来调用的状态已经包含在 `R_cut` 中；保持它们的关系，并在 terminal 检查 `O_C`，即可沿执行归纳继承此前的效果。

如果以后为压缩证书引入 effect summary，它必须与完整状态转换等价。storage 写按有序函数复合，事件轨迹按串接；即使 gas 使用累计量，也要说明退款、溢出、错误路径及外部扣费的规则。terminal 为吸收态只表示之后没有继续步骤，不意味着所有 observable 都具有加法结构。

所有 terminal 路径使用同一份必检字段规范。复用现有 `EquivalenceChecker`／`PathObservation` 时，要明确传入 gas 比较开关与 coverage；请求的字段缺失必须失败，不能由 `None` 或 `.get()` 的默认值静默跳过。串行、并行翻译、merged 与 aggregate fallback 都不能改变这份规范。

### 6.2 Gas 配置与 OOG

| 配置 | 真实入口 gas 域 | 结论 |
|---|---|---|
| `FIXED_BUDGET` | 已指定具体预算 | 该预算下的模型行为和 gas 终值对应 |
| `FULL` | 符号 gas，范围明确 | 对该 gas 域全称量化的模型行为和 gas 终值对应 |
| `OFF` | 按现有入口契约固定，并明确实际执行的简化模型 | 不比较终值；不能声称真实扣费／OOG 行为正确 |

FIXED_BUDGET 和 FULL 的局部定理都可以在任意符号剩余 gas 上证明；前者通过 Base 绑定全局初始预算，后者保留全称量化。若局部进一步限制剩余 gas 范围，该限制必须进入关系、Base／闭包和 key。

v1 默认目标为 `FIXED_BUDGET`／`FULL`。`OFF` 兼容结果须醒目标记实际 gas 模型和未覆盖项：现有 OFF 关闭 host gas UF、可能改变 OOG、GAS 及由 gas 派生的分支，不能仅写成“少比较一项 gas”。局部生成器与执行器必须显式接收相同配置，不能沿用 `build_havoc(host_gas_uf_enabled=False)` 默认值证明另一种语义。

OOG 桥接是可选优化：先在当前公开前提下证明两侧真实 OOG 谓词等价，再用该等价关系优化路径配对。失败时回到全组合证明或报告 inconclusive，不强制共用一个 Boolean。所有 TAG／动态 gas 错误路径保持实际先检查再更新的顺序，错误状态不能被正常路径后续更新覆盖。

允许用已证明到达条件 `Q` 裁剪 OOG：证明 `Q ⇒ ¬oog` 后，在这次应用中删去该分支是合法的。仅因初始预算“很大”就裁剪后继 OOG 不合法；有动态扣费时具体预算也不能自动排除 OOG。

host gas 公式、warm/cold 等历史状态及 `HOST_GAS_UPPER_BOUNDS` 的未建模部分必须列入模型前提。FULL 不自动证明真实 host 公式或 host 内部耗尽／终止。外部上界若只为证明内部循环有限，不得悄悄进一步用于删除模型本应保留的错误路径。

### 6.3 Host bridge 和运行时暂离

v1 把已支持 host bridge 作为块内的已声明抽象调用：它在模型中是有限的原子步骤，返回后继续本块；该有限返回是模型边界，不是关于真实外部合约终止的证明。

每个站点须核对真实 raw code 的分发／恢复行为、操作类型、输入参数及读入内存、状态和 gas 更新、返回数据长度与内容、恢复点及活跃寄存器。状态性 host UF 必须包含足够的状态／历史输入，不能只比较调用次数。存在真实外部回调／再入而模型未覆盖时，只能给出该抽象模型内结论。

尚未支持的 bridge 不纳入 terminal，也不能绕过它继续证明块尾；整个相关节点不完整。若未来将 bridge 拆为独立图边，要同时引入 continuation 关系、有限进度与覆盖接口后才能采用。

### 6.4 CALLDATALOAD 与 copy-loop summary 的接管门

任何 summary 需要三层证据：抽象操作语义正确；每次命中绑定的真实机器码实现该语义；当前入口满足适用前提。必须同时覆盖正常／错误输出、frame 条件、后继位置及局部终止。模板证明可以复用，但每次命中要验证字节／位置／参数绑定和适用域。

CALLDATALOAD 在符号 offset 下必须处理 256→64 位截断、`offset+32` 回绕、完整／部分／越界读、零填充、calldata 长度域和结果 limb 绑定。可以证明 no-overflow，也可以显式实现溢出分支；不能只关掉 concrete-offset 检查再追加未经证明的 no-overflow assumption。

copy-loop 必须证明计数器／地址变换、方向、重叠复制语义、零长度、尾部、有限终止和 frame 条件，并覆盖所接管代码的 gas／错误影响。MCOPY 的外层 `size<=8` 分派与循环尾部 `size<8` 判据不能混淆；`size==8` 单独验收。

静态适用性预检用于节约成本：能判不适用时跳过；无法静态决定时允许做有预算的语义前提证明。预检成功不能代替 per-hit proof。命中失败后要么从未改变的同一输入状态执行原代码并保留全部 coverage，要么返回不完整；不能静默假定 summary 已执行。

summary 内部递归依赖也要有终止／well-founded 证明，不能用“证书互相引用”证明自己。完整证明接管门建成之前，块级路径不得依赖相应 summary 的优化结果。

## 7. 全局组合定理

### 7.1 成立条件

对固定 `P_E,P_X,C,A_C,I_C`，设选定的有限节点集为 `N={(B,p)}`。假定：

1. 解析与区域映射检查有效，所有实际语义转移被完整解释。
2. H0 覆盖所有允许的真实入口输入。
3. 每个被全局证书依赖的节点均满足 §4 的有限推进、路径覆盖、全组合控制流与 terminal 定理。
4. 每条 Continue 的 H2 成立，并指向同一证书图中有完整定理的后继节点。
5. 域约束、辅助不变式、host 模型、Gas 模式和所有 summary 前提都已按其契约处理，证书配置完全一致。
6. 未使用的候选或区域已由上述 Base／闭包排除，或有有效的不可达证据；没有未关闭的降级／证明义务。

则对于每个满足 `A_C,I_C` 的输入及共同 oracle：两侧的块边界执行逐步对应；若一侧终止，另一侧也在有限步后进入同类终态且 `O_C` 一致。两侧的无限执行也在块边界上对应。

### 7.2 证明骨架

Base 由 H0 给出某个 `R_cut(B0,p0)`。假设第 n 个边界满足某个已证节点关系，局部推进保证两侧有限到达下一结果；全组合检查排除 Continue／Terminal 错配。

若结果为 Continue，H2 给出后继某个已证实例的完整关系，从而建立第 n+1 个边界的归纳假设。若结果为 Terminal，局部终态义务直接给出 `O_C` 一致，且不再执行后继。

对任意有限边界前缀归纳可得全部对应。若一个执行无限但只经过有限个边界，就会与局部有限推进矛盾；因此无限执行必经过无限个边界，另一侧通过相同归纳和非零宏步骤也产生无限执行。有限步对应与 terminal 配对排除了单侧终止。

### 7.3 与“程序必然终止”的区别

本方案证明的是**终止行为对应**，不要求每个输入都终止。一个两侧都执行的 EVM 循环可以无限走回边；无需为整个合约 SCC 给出全局 ranking function。

块内编译器引入的循环和 summary 则必须保证有限推进。仅证明“双方都到出口时状态相等”不满足该要求；若只取得这种弱结果，应记录为未完成的局部证明，不能用 `partial correctness` 名义升级成 `VERIFIED`。

若用户额外要求“所有输入都终止”，需另证全局终止，可利用满足良基性和实际递减条件的 gas／其他 ranking。有限匹配与排除无限停顿的区别可参照 [CompCert Smallstep 的 simulation 定义](https://compcert.org/doc/html/compcert.common.Smallstep.html)；本文组合结论依赖的是上述明确列出的条件，不是对参考实现正确性的借用。

## 8. 不可专门化、失败与降级

### 8.1 `TOP` 的含义

`TOP` 仅表示当前分析域无法提供适合精确枚举的候选常量；不是“一个具体参数桶”，也不是数学上无法建立有限图的证明。`m` 和 `f` 必须独立处理，一侧 TOP 不意味着另一侧必然 TOP；空集合表示无候选，需要不可达证据，不能等同 TOP。

动态 `m`／`f` 可以用符号参数关系表达，在一个节点内代表许多值，但该节点仍须通过同样的局部及全局义务。成本可能较高。不能从历史几个 timeout 推出所有 TOP 节点必定超时，也不能承诺一份 copy summary 会使真正动态的 MSize 变成常量。

### 8.2 v1 的默认降级：独立整程序重跑

若主块图仍有必需节点未证明，先报告块图 `INCONCLUSIVE`，列出已证局部节点及缺口。可以从相同真实初始条件独立启动现有整程序验证器；只有后者在相同模型、observable、输入域和请求的证明强度下通过，才可由它独立给出 `VERIFIED`，报告实际 proof mode。替代 §7 的结论时，它也必须证明执行覆盖及终止行为对应；仅比较已收集终态、没有排除遗漏或单侧发散的结果不能充当替代证书。

整程序重跑不把旧的局部 `proved` 计数作为剩余路径已经覆盖的依据，也不复用已扣 gas／已写 storage 的中间状态作为新初始状态。该默认路径实现简单，无混用所需的新组合假设；重跑也超时则最终仍为 `INCONCLUSIVE`。

### 8.3 可选混用：相同接口的区域定理

混用作为后续明确验收的能力，而非默认已经具备。扩大或合并无法专门化的若干块，建立带显式入口关系的区域定理；它必须具有 §4 的有限推进、完整路径结果和 §5 的出口闭包。区域可采用符号 `m,f` 或额外已证不变式。

区域有多个入口时分别登记全部实际可达入口；区域内部不能包含未处理的外部跳入。对每个接口分别证明专门化→区域、区域→专门化、区域→区域的实际状态到达，仍不能把 TOP 直接替换成某个常量。

混用必须固定执行所有权：一个动态宏步骤选择原代码执行或已证摘要中的一种。不能既执行被接管的语义又重放摘要的扣费／写入；物理区域重叠只允许通过 §2.3 的显式子证书机制解释。若区域内部包含可能无限的 EVM 循环，必须保留循环切点或另证区域有限推进，不能靠有限展开伪造区域定理。

现有“从具体 caller 状态展开若干路径”的结果只能作为该到达域的 application 证据；不能未证明泛化就折成对所有 `R_cut` 成立的局部节点。任何区域失败、未覆盖或适用前提未证都会阻止全局成功。

## 9. 证书、缓存和消费端

### 9.1 证据对象

以下是设计接口，不表示已有同名生产实现：

| 对象 | 必需内容 |
|---|---|
| `BlockTheorem` | 程序与配置身份、入口关系／参数、havoc 表示依据、有限推进及两侧 coverage、全部结果 guard、控制流与终态证据、出口后置关系、外部前提 |
| `EdgeCertificate` | 来源实例和实际结果标识、目标程序点、后继实例析取、完整 H2 证据、目标关系及集合版本 |
| `EntryCertificate` | 原始入口和输入域、适配段语义与 coverage、H0 证据 |
| `ProgramCertificate` | 请求范围、入口集合、冻结节点／区域清单、全部局部和边证书、不可达依据、未关闭义务为空 |

局部定理可以先给出出口后置条件，待 `EdgeCertificate` 证明它蕴含后继关系。若局部直接证明了后继析取，也要导出等价的边证据。没有边证据的局部结果只用于诊断，不能折叠全局路径。

循环中的边证书可以引用后继**关系定义**，不靠假设后继已经等价来证明本块等价；各局部定理独立执行原始块／已证 helper。整张有限依赖图最后一起检查闭合。这种 CFG 归纳不允许推广为相互循环假设的 summary 正确性证明。

### 9.2 缓存身份

定理 key 至少包含：

```text
evm_program_digest, x86_bytes_and_decode_digest,
block_or_region_id, entry_phase, stop_set_and_partition_digest,
(k,m,f) 或一般入口谓词及其定义版本,
relation_and_domain_digest, semantic_model_version,
gas_execution_model, requested_observables, initial_domain_if_used,
summary_config_and_proof_digest, aot_profile_digest,
host_model_and_assumptions_digest, pc_addr_mapping_digest
```

仅有 `block_pair_id` 或 TAG 常量指纹不够：块体机器码、IR 立即数、目标集、static gas、CALL 站点语义变化都要使相关定理失效。`R` 版本要覆盖实际条件、地址域、镜像和前缀契约，不只是分量名列表。

应用 key 另外包含局部定理身份、caller 到达条件／实际状态身份、入口关系证明、请求的证明强度及后继证书版本。有限预算下可达性裁剪只属于该应用，不能污染通用定理缓存。只缓存完整成功证据；unknown、空真、异常和缺失依赖不进入成功缓存。

v1 建议仅做单次运行内缓存；若身份依赖 Python／Z3 对象 ID，要保留引用防止 ID 复用。以后做持久缓存时再增加稳定序列化及完整依赖校验，不能直接把进程内 ID 落盘。

### 9.3 消费端成功条件

```text
verify(request):
    freeze programs, model, observable scope, assumptions, partition
    check mapping and raw-entry adapter
    build and verify local nodes, actual exits and successor relations
    require valid EntryCertificate(s)
    require all referenced BlockTheorem / EdgeCertificate objects valid
    require all real results covered; no pending progress/domain/summary obligation
    require all certificate identities and requested strengths agree
    return VERIFIED only for this closed certificate graph
```

消费者不依据 `status == 'proved'`、`terminals_proved > 0`、测试通过数量或 CLI 文案判断证书完整。聚合、串行、并行及降级入口统一执行相同成功门禁。

## 10. 当前实现与目标设计的差距

以下为 2026-09-14 对 `d51b351` 的源码核对，不是一次新的全量代码审计。

| 模块 | 当前可复用部分 | 必须补齐／修正 |
|---|---|---|
| `tools/tag_align.py` | 候选 TAG 对齐、锚点、区域信息 | 核验真实入口与 TAG phase、全部控制转移和支持区；映射不是语义公理 |
| `tools/call_provenance.py`、`tools/msize_absint.py` | 深度／常量候选及诊断 | 结果只提议候选；丢帧、丢边、TOP、关联损失不能变为待证程序的假设 |
| `verification/cutpoint_relation.py` | 十五分量、msize/fmp 专门化、镜像基础 | 建立 TAG 前统一关系、任意 R14／scratch 的 havoc、完整域与 Base／闭包；不增添伪状态分量 `block_pairing` |
| `verification/block_equivalence.py` | 段执行接线与部分 Continue 检查 | `_classify` 当前只配 Continue×Continue；`_check_terminals` 只检查存在性并计数，尚未证明 observable；成功 API 必须重做 |
| 同上 `_check_control_flow` | 状态分量比较 | 目前未将后继 m/f 专门化传入目标；需完整 H2、运行状态、域和实际继承关系 |
| `verification/block_specialization.py` | 候选集合与 TOP 分类 | 两端深度非空不是 H2；实例数／块数阈值不是 H3；改成候选计划与语义证据分层 |
| `verification/loop_induction.py` | 段执行、部分 coverage 和关系工具 | 核验重入当前入口时的 stop、TAG 前关系、内部循环进度，不能原样认定接口满足块定理 |
| `common/oog_bridge.py` | OOG 先证等价再优化的接口 | 用当前块实际前提，证明失败允许回到完整检查 |
| `x86_64/summaries/` | 算术、CALLDATALOAD、copy 模板与部分 proof 基础 | 逐项满足 §6.4，包括每次命中前提、真实机器码绑定、终止和 frame |
| `verification/loop_certificates.py` 等 | theorem/application 分层与身份设计 | 块级证书另建完整合同，不以旧循环证书布尔字段替代新义务 |
| `tmp/e2e_block_lockstep.py` | 实验驱动、分析器与 PoC 接线 | 当前只是遍历局部实例计数，没有 Base＋闭包＋全局证书消费 |
| `verification/program_verifier.py` | 整程序路径与 observable 检查 | 新 proof mode 必须从统一全局门禁接入；当前局部 API 未作为完整块图证书消费 |

2026-09-07 审查在此前 PoC 快照上记录了两项反向探针：`muti_block pc=120` 的 x86 终态状态码全部改成 255 后仍 `proved, queries=0`；交换 Continue／Terminal 的 guard 仍通过。这一记录描述本轮实现之前的 PoC 基线；本轮已将上述反向探针纳入默认回归并拒绝假成功，当前验收见 §14。旧 `proved` 数据不能当作满足本方案的证明数量。

## 11. 实施顺序与验收

### 11.1 按证明依赖实施

| 阶段 | 产出 | 完成条件 |
|---|---|---|
| 0：先关闭假绿 API | 未完成义务返回 inconclusive；统一请求范围与结果类型 | terminal 破坏、跨类别条件交换、漏字段均不能返回可消费成功 |
| 1：统一边界关系 | `R_cut`、TAG 前缀证明、入口适配段、完整 havoc | 任意旧 R14 可正确处理；破坏前缀被拒；不重复 TAG gas；镜像／域遗漏被拒 |
| 2：局部完整定理 | 两侧覆盖、有限推进、全结果矩阵和终态比较 | 小直线、分支、自环边、OOG、错误、返回值／storage 等反向用例通过 |
| 3：Base 与闭包 | H0、真实出口 H2、候选版本和不完整分析处理 | 专门化错用、漏后继、假不可达、缺 Base 必须被拒；合理有限循环可通过 |
| 4：全局证书消费 | 冻结节点图、统一 verified gate、独立整程序降级 | 小完整程序从真实入口得到证书；删除任一必需证据即不再 VERIFIED |
| 5：已证明的 summary | CALLDATALOAD／copy 等 per-hit 接管 | 符号边界、frame、内部终止和配置失配测试通过，才用于性能实验 |
| 6：真实合约评估 | ENSRegistry／CErc20／Safe 的完整状态报告 | 同范围基线、分层耗时、真实缺口和复现材料齐全；不要求预设通过率 |
| 7：可选区域混用 | §8.3 的区域证书与三类接口闭包 | 接管／展开恰好一次，区域所有入口与内部循环均有证据 |

可提前运行分析器和性能调查，但不能以它们完成替代后续证明阶段。没有 TOP 也不意味着整个合约必然通过；小 fixture 的每块 `min_depth` 专门化通过，不等于从真实入口覆盖了全部状态。

### 11.2 必需反向与正向基准

| # | 输入或故意破坏 | 必须观察到的结果 |
|---|---|---|
| 1 | 真实终态 producer 单侧改变 status／返回字节／storage／transient storage／请求的 gas | 对每种字段单独破坏；原始基线通过，破坏后失败，且实际执行到对应检查 |
| 2 | EVM 在 c 时 Continue，x86 在 c 时 Terminal，反支对调 | 两侧各自 coverage 完整仍必须拒绝 |
| 3 | 删除实际可达的 status 桶、加入可共现但语义不同的 terminal、仅配同 status 而漏掉异桶行为 | guard／全组合覆盖检查拒绝；重复表示同一个语义结果不要求失败 |
| 4 | 后继两侧 m/f 同时变成未登记值，或 k 不在后继集合 | H2 拒绝；补齐正确实例和定理后才可通过 |
| 5 | 漏掉初始实例／真实入口前缀；以 block.min_depth 代替实际 SP | H0 拒绝；不能靠全体局部测试绿补足 |
| 6 | 删除后继节点，伪造分析器不可达，或让 shadow stack 给出错误唯一返回点 | 真实段控制流／后继闭包发现缺口；允许降低覆盖率，不允许制造全局成功 |
| 7 | 带旧 R14 的合法边界；删除／篡改 TAG 的 R14 重建 | 原始前缀通过，破坏后拒绝；另测重建前 OOG／栈错误 |
| 8 | 单侧 property 与 CALLENGINE limb 不一致、遗漏域约束或新分量 | Base／H2／终态相关检查拒绝，不能只测名字登记 |
| 9 | 本块自环；x86 内部无进展循环；summary 缺终止证据 | 自环在再次进入入口时停止并建立边；内部单侧发散不产生完整局部定理 |
| 10 | 所有语义查询注入 unknown／timeout，或 executor 达到 depth cap／抛异常 | 相应节点与全局均 inconclusive，未展开路径保留为缺口 |
| 11 | 矛盾入口前提、未经证明的新 assumption、只因 no-overflow 过滤而 coverage 完整 | 空真不成为定理；缺少前提来源／到达证明时拒绝 |
| 12 | 固定预算下已证明不可达的 OOG，以及含动态扣费的可达 OOG | 前者可在该应用中裁剪；后者必须比较，不能因预算具体就删掉 |
| 13 | 改 x86 块体字节、IR opcode／static gas／目标集、Gas 档、summary、ABI、后继参数集合 | 相应缓存与依赖证据失效；映射拒绝可作为保守失败，但需另测语义差异确被检查 |
| 14 | CALLDATALOAD 符号 offset、回绕边界、部分读、零填充；copy 长度 0/7/8/9 和重叠 | per-hit proof 覆盖真实分支，不能靠添加假设通过 |
| 15 | 同一块有多个同类 host 站点，交换参数／站点／恢复地址 | 逐调用语义匹配拒绝，块映射相同不能免责 |
| 16 | TOP 独立重跑；可选混用中摘要后又执行原块／重复扣 gas | 重跑输入一致；混用计账及状态破坏被拒，缺口不能消失 |
| 17 | 保持有限参数的循环／尾递归，与不收敛或超预算候选分析 | 前者可由闭包验证接受；后者记录不完整，不按语法名称猜测结论 |
| 18 | 串行／并行／merged／aggregate fallback 切换，单侧破坏 observable | 每条实际生产入口均拒绝；fallback 测试先确认正常 fallback 确曾成功 |
| 19 | 局部 certificate 缺 Base／某条 EdgeCertificate／progress／scope 身份 | 单个局部结果可供诊断，但全局消费者拒绝 |
| 20 | havoc 的默认 scratch 常量影响输出，或中途把两侧更新重新共用 | 表示完整性／真实语义测试拒绝；不能以“两模型输出相同”掩盖丢失状态 |

快反向基准默认进入常规回归。重型合约测试允许独立 slow 任务，但必须是显式执行并报告的验收门禁，不能长期默认 skip 却写成“全量通过”。性能快不能抵消任何 soundness 基准失败。

### 11.3 实验报告与复现材料

每次报告记录：程序与工具版本／摘要、完整配置和 assumptions、初始输入域、预算、实际命令、硬件及 worker 数；局部实例、完整定理、Base／边证书、TOP／未覆盖区域分别计数；所有失败阶段与原因单独列出。

成本拆成分析、段执行、summary proof、路径／observable 查询、闭包、组合和降级；给出总墙钟及分位数。设整次运行和每实例的墙钟／内存限制，不能把每条 solver 查询 30 秒写成“每块最多 30 秒”。超时、异常和未开始实例都保留在分母和报告里。

基线与优化必须使用同一程序、模型、Gas 域、observable、输入前提和验证强度。随机入口样本不能直接外推全合约；采用按 jcc 数、summary 种类、参数数目分层的样本，并最终报告真实完整运行。`VERIFIED` 只由 §9 的消费者产生。

## 12. 历史可行性实验与工程线索

本节保留原方案的实验记录，来源为旧文档及 `tmp/` 脚本，不是 2026-09-14 重测结果。未固化版本／配置的数字只作历史参考；旧 PoC 缺终态和闭包等义务，因此其 `proved` 统计不得改名为“已证完整块定理”。

### 12.1 路径局部化和块结构

| 历史指标 | ENSRegistry | CErc20 | Safe |
|---|---|---|---|
| 整程序实验（max_depth=240） | 可跑完 | 880s 未跑完 | 880s 未跑完 |
| 整程序 jcc 静态判死率 | 86.5% | 81.9%，前缀样本 | 33.5%，受局部瓶颈影响 |
| TAG 对齐数 | 127/127 | 723/723 | 742/742 |
| 返回比较链锚点 | 33 | 192 | 166 |
| 每 EVM 块的 x86 basic block 均值／最大 | 55.6 / 300 | 47.6 / 366 | 41.6 / 490 |
| 不同 TAG 三元组数／最大重数 | 65 / 17 | 304 / 55 | 350 / 79 |
| 深度类倍增 | 1.27× | 2.55× | 2.22× |

历史切点数 17/20/30/47 对应段路径 5501/3823/2971/3038，最大条件 AST 13386/13107/4829/4782。趋势表明局部化值得继续尝试，但路径数并非单调下降，也不能据此断言 47 对所有指标最好。

此前随机抽样 25 个入口记录 CErc20 7.9s、Safe 6.6s，平均路径 1.9、最大 5；该数据不足以判断是否覆盖了高成本尾部。每块条件跳转中位数约 8–10、p95 66–89、最大 167/167/228，说明应分层测量。静态潜在路径数不等于可达路径数，更不等于证明墙钟；局部化也不构成 AST 大小的常数上界。

### 12.2 MSize 候选与联合专门化

| 旧抽象分析结果 | ENSRegistry | CErc20 | Safe |
|---|---|---|---|
| MSize 唯一值 | 93.7% | 43.6% | 51.9% |
| MSize 2–4 值 | 6.3% | 0.6% | 0.9% |
| MSize TOP | 0% | 55.9% | 47.2% |

这些比例描述 MSize 分析结果，不是“可证块比例”；还要检查 fmp、k、关系前提和局部完整定理。

| 历史样本块 | 仅 msize | 仅 fmp | 联合 msize/fmp |
|---|---|---|---|
| ENS 1455 | 80 路径，35.4s，判死 47.5% | timeout，78.3% | 11 路径，3.0s，93.5% |
| CErc20 5343 | timeout，27.1% | timeout，78.6% | 49 路径，42.5s，94.3% |
| Safe 6275 | 8 路径，4.8s，95.1% | timeout，85.5% | 8 路径，4.9s，95.1% |

三块为旧实验选取的无 CALLDATALOAD／copy 样本。它们支持优先尝试联合专门化，不支持“所有可专门化块均秒级证完”或“判死率 90% 是普遍临界值”。Safe 样本仅 msize 已接近联合结果，故联合不是每块的正确性必需条件；主路径统一联合只是工程选择。

历史在不同 msize 常量 `0x80/0x100/0x400/0x2000/0x10000` 下均能完成的实验，只说明特定样本对常量的性能敏感性有限，不允许定理使用错误的到达值。

### 12.3 Provenance 与 TOP 来源

旧 shadow-stack 分析记录恢复率 ENS 46/46、CErc20 915/915、Safe 378/378；栈效果自校验在 1592 个块上与导出 `stack_depth` 一致。pc 粒度边表与朴素 CFG 相同，剪枝发生在带深度／上下文的状态上。源程序中的多 continuation PUSH 必须保持栈序；仅取 pad 集合交集或只压一次调用的返回点曾导致严重失真。

这说明上下文分析的重要性，不证明推断前提本身健全；返回地址经过 DUP／SWAP／存储等行为时仍须完整建模或保守处理。错误候选必须被后续语义义务挡住。

旧分析记录 CErc20 402/404、Safe 349/350 个 TOP 块继承上游 TOP，源站点计数分别为 28、8；CErc20 4236 的 MSTORE@fmp 关联 304 块，Safe 9351 的 CALLDATACOPY 关联 255 块。可优先调查 CErc20 `4236/11250/6554/7613`、Safe `9351/11531/4946`。

这些关联适合定位瓶颈，但不能推出“修复 copy-loop 就会使下游常量域恢复”。真实依赖 calldata 的 MSize 即使执行摘要正确仍可保持符号。Safe 5377 的多数内存偏移为动态，仿射地址关系或符号参数域是可选后续路线。

### 12.4 CALLDATALOAD 与 copy-loop

旧实验把 CALLDATALOAD 识别为大量块内条件分支的来源；Safe 10750 开 summary 后曾记录 2 条段路径、10 块步、0.13s。该运行收益不包含完整 per-hit proof，不能作为 summary 健全性证据，也不采用静态 `2^128` 与实际两条路径的比值作为可靠加速比。

旧 ENS 实验统计 `proved 130/144`，14 个失败实例落在9个块，其中13个报告 `live_stack_prefix`，9个失败块均含 CALLDATALOAD。这是失败相关性，不是“唯一证明缺口”；当前 PoC 的成功项也缺 §10 所列义务，补齐后必须全部重测。

历史还记录 CErc20 8186 出现 Z3／RecursionError，Safe 5377 在 240s 中出现32次 copy-loop 前提拒绝。这支持增加预检和预算，不支持跳过运行时前提证明。

### 12.5 暂不优先的性能尝试

| 尝试 | 历史观察 | 本版决定 |
|---|---|---|
| 仅把 MSize 区间加进 assumptions | 某样本静态 simplify 剪枝收益小 | 可作为公开且闭合的域；不预期自动解决该性能瓶颈 |
| 每个分支做 solver 可达性查询 | ENS 1455 的133次查询耗46.5s，整体仍超时 | 不默认全量开启；允许按成本选择性使用，不能写成永远禁止 solver 剪枝 |
| 统一假设 fmp-msize=0x20 | 旧结果主要受序言态支配，其他差值存在 | 不作为通用不变式；特殊区域若能证明则可使用 |
| 用静态路径数作为唯一指标 | 与实际可达路径及单路径求解成本不一致 | 同时报执行数、AST／求解成本和总墙钟 |
| 依赖函数入口复用解决全部性能问题 | 旧样本收益不足 | 本版优先块级局部化，不作一般性不可行结论 |

## 13. 最终边界与参考

本方案的完整结论是：**在冻结且公开的模型、输入域与外部前提下，通过全部局部推进／对应、Base、闭包和覆盖义务后，两侧块执行及终态投影一致，终止行为相互对应。** 不保证验证器能为任意输入程序找到合适关系，也不保证所有请求都在给定预算内完成。

没有 logs／真实 host／完整协议模型时，不宣称完整 EVM 外部行为等价；没有全局终止证明时，不宣称所有输入终止；存在必需 TOP／缺证书／超时区域时，不宣称块图已经 VERIFIED。返回局部证明清单是有用结果，但与整程序成功严格区分。

实现入口与参考：

- [cutpoint 关系](../verification/cutpoint_relation.py)、[段执行与循环工具](../verification/loop_induction.py)、[结构检查](../verification/segment_validation.py)。
- [块证明 PoC](../verification/block_equivalence.py)、[候选专门化计划](../verification/block_specialization.py)、[现有整程序入口](../verification/program_verifier.py)。
- [TAG 对齐](../tools/tag_align.py)、[provenance 分析](../tools/call_provenance.py)、[内存抽象分析](../tools/msize_absint.py)。
- [observable 容器](../common/path_observation.py)、[OOG 桥接](../common/oog_bridge.py)、[summary 实现目录](../x86_64/summaries/)。
- [循环处理增强方案](循环处理增强方案.md)、[cutpoint 泛化方案](cutpoint泛化方案.md)：历史背景；本文件明确规定的边界与义务优先用于本块级路线。
- 外部 codegen：`$GOPATH/src/github.com/bcds/go-hpc-evm/evm/aot/impl_amd64.go`，重点核对 `compileEVMTag`、`compileEVMJUMP`、`compileEVMCALLDATALOAD` 和 bridge／退出代码；随实际使用的编译器版本重新绑定。
- 历史实验：`tmp/tag_align_survey.py`、`tmp/depth_class_provenance.py`、`tmp/msize_absint.py`、`tmp/msize_joint_inject.py`、`tmp/exp1_jcc_pruning.py`、`tmp/exp_summary_blocks.py`、`tmp/e2e_block_lockstep.py`。这些路径表示旧记录来源，不替代经版本固定、可重跑的验收材料。

## 14. 实现落地说明（2026-09-14 工作区）

本节描述按本方案新增的实现；§10 保留为 `d51b351` 基线差距记录，§12 仍是历史实验，不能用作本实现的通过率。

### 14.1 生产入口与证据链

- `verification/block_relation.py::BlockRelationSchema` 定义 TAG 前的统一关系。R14、scratch 寄存器／标志和未使用的栈／CALLENGINE 内存任意化；已有十五分量之外，显式检查运行状态、内存／栈域、ABI 基址、其余已耦合镜像和持久不变式。运行中 `return_offset = return_length = 0` 是显式不变式，由 H0/H2 重新证明，不是隐含初始化假设。默认栈表示域覆盖 1024 个元素。
- `verification/block_partition.py` 在实际指令边界拆出原生初始化前缀和第一个 TAG，保留所有原始指令。第一个 TAG 的回边不会重新执行初始化前缀。
- `verification/block_equivalence.py` 从该关系独立执行两侧；stop 集合包含当前入口。每侧必须具备 executor coverage 和 guard coverage；新增 assumptions 必须由原始入口前提证明，不能在包含该 assumption 的最终 guard 下自证。全部结果笛卡尔积均检查，终态真正比较 observable。仅在完整查询证据生成后签发 `BlockTheorem`。
- 局部 Continue 输出作为带 guard 的实际后置状态交给 `verification/block_program.py`。编排层从原生入口执行适配段，只枚举有限栈深 `k`；对同一 `(pc,k)` 的变化 m/f 概括为符号关系，完成有限工作队列；冻结候选集合后逐条证明完整后继关系析取，形成 `EntryCertificate`、`EdgeCertificate` 和 `ProgramCertificate`。候选表 `.ok` 不再声明 H0/H2/H3。
- 真实动态 JUMP 的参考执行使用完整合法 JUMPDEST 集合；块模式的 `complete_jump_domain` 不允许 `immediate_set` 缩小参考目标域。尚不能处理的动态 JUMPI／其他形态明确失败。静态 IR 指令本身仍属于给定源程序，验证不向前覆盖 Solidity→IR 的编译过程。
- 消费端核对所有节点、实际 Continue 对的边证书、入口证书、冻结参数集合版本、程序／模型／配置身份和输出状态摘要。单独设置 `status="proved"`、删除某条边或替换已执行状态，均不能成为程序级成功。

`ProgramEquivalenceChecker.verify_program_pair(..., proof_mode="block-lockstep")` 和 CLI 使用上述统一消费端。块模式当前使用串行、不合流的局部执行，不声称已经提供独立的并行块证明实现；旧整程序路径模式保持独立。

### 14.2 Summary 与降级的具体策略

`verification/block_summaries.py::VerifiedSummaryRuntime` 把现有 summary 当作提议。每次命中从当前实际状态和 guard 出发，**关闭所有摘要重放原始机器码切片**，证明有限执行、完整覆盖、精确 continuation、完整状态效果与 frame；不能越过块切点或隐藏 host／RET 边界。对 summary 的新鲜 clobber 符号，以原始执行结果给出表示见证，验证过近似确实包含原始状态。每次命中的证据进入局部定理，缺失时不能消费。

该实现优先建立可信接管接口，尚不是任意长度符号 copy 的常数成本归纳证明。重放预算不足、别名／provenance 无法证明或 summary 语义不匹配时，strict 模式拒绝，fallback 模式执行原始指令；后者仍须通过完整局部定理，不能跳过该段。CALLDATALOAD 的符号 offset 不靠添加 no-overflow 假设放行。

整程序降级由 `fallback="full-program"` 显式启用，默认 `"none"`。它使用原始初始状态、相同 gas／calldata／host 模型和 observable，创建全新 executor，关闭摘要且不设块切点；必须证明所有完整终态及两侧覆盖，签发独立证书。之前的局部计数只保留为诊断，不参与成功门禁。无法在预算内完整执行的循环不会因为降级而变绿。可选区域混用（§8.3）尚未启用。

### 14.3 使用与复现

普通生产 CLI 的块模式默认真实初始栈深为 0；有意验证非空初始栈时显式指定 `--num-inputs`：

```bash
poetry run python main.py tests/data/mstore_return.json "$(cat tests/data/mstore_return.hex)" \
  --proof-mode block-lockstep --gas-check full
```

需要结构化证据统计、摘要检查和整次运行的硬墙钟上限时，使用独立进程驱动：

```bash
poetry run python -m tools.verify_block_lockstep tests/data/mstore_return \
  --gas-check full --summaries --timeout-ms 3000 \
  --wall-seconds 300 --hard-wall-seconds 360 --output /tmp/block-result.json
```

`--node-seconds` 默认 60 秒，限制每个局部定理的查询与 summary 检查；节点超时后继续已登记工作队列。期限不经 summary fallback 吞掉。`--wall-seconds` 是整轮编排／查询的软预算；Python 中正在执行的符号展开不能靠 solver timeout 中断。`--hard-wall-seconds` 由父进程监督整个工作进程，超过预算终止并报告 inconclusive。节点和全局期限均不能强制打断正在执行的 Python/C 扩展，因此保留外层硬预算。每条 solver 的 timeout 不能写成每块或整个合约的耗时上界。

结构化报告保存原始程序哈希、模型源码哈希（包括尚未跟踪的新文件）、工作区差异哈希、配置、机器／Python 信息、局部实例、Base／边证书、实际成功摘要命中、查询与阶段耗时。每完成一个实例就向父进程回传逐块诊断及闭包预检，写入同名 `.partial.json`；硬超时保留最近快照。`unvisited`／`queued` 不是不可达证据，尚未完成的当前节点不会伪装成已完成统计。

### 14.4 验证边界与评估材料

新快回归覆盖真实 terminal producer 的单侧 status／memory bytes／storage／transient storage／gas 破坏、跨类别 guard 交换、删除结果、unknown、未证 assumptions、scratch、候选漏边、真实 H0/H2、镜像／域／运行状态、旧 R14、自环与内部死循环、证书删除、独立降级，以及 per-hit summary 的效果、frame、切点所有权和有限执行。

终态目前采用完整内存数组与返回偏移相等的较强充分条件；这可能比 §1.2 的外部 observable 更严格，导致 inconclusive，但不扩大成功结论。host oracle 的已声明 cost 上界作为共同模型公理实例化，不是临时路径过滤；真正 host 内部耗尽、真实 runtime 终止、完整 logs／host trace、真实回滚和完整 EVM 协议仍不在本结论内。

此前短预算真实合约报告位于 [reports/block-lockstep-2026-09-14](reports/block-lockstep-2026-09-14)。本轮采用固定预算 `1,000,000,000`、每查询 1 秒、深度 200、最多 256 个实例、编排软预算 30 秒和外层硬预算 45 秒，分别关闭／启用 per-hit summary；三份合约都未形成完整程序证书，不能据此宣称合约等价或给出“已验证全部块”的通过率。具体失败和版本以各 JSON 为准；它们是有资源限制的完整请求结果，不是随机块样本外推。


### 14.5 符号节点、诊断与无界循环验收

`BlockSpecialization.memory_size/free_memory_pointer` 支持 `None`；候选分析的 TOP 直接产生对应符号参数，而空集合仍为缺陷。自动发现只对栈深枚举；对于每个 `(pc,k,κ)`，先使用出口表达式中可直接确定的常量，遇到参数变化后统一概括为 `(None,None)`，保留已有已登记实例，后续不再展开变化常量链。每个 `(pc,k,κ)` 自动生成至多两个内存参数实例。不存在“把模型采样值当作全部参数域”的规则。整个栈深域最多 1025 种；资源预算耗尽仍是 inconclusive。

局部失败只增加未完成义务，继续处理其余已登记节点；没有完整执行结果的节点不能凭空生成后继，相关未探索块明确保留 `unvisited`。逐块诊断与证书签发分离：返回所有已完成局部结果、失败原因、排队状态和未访问块表。最终只有全部登记节点、H0、H2 和工作队列闭合均成功才签发证书。每条发现边立即执行一次闭包预检，便于早发现关系缺口；预检不能代替冻结集合后的最终证据。发现结果按实际表达式和 guard 作运行内缓存。

`BlockTheorem.required` 和独立重跑的查询清单从路径、入口 assumptions 和必需义务独立推导，不再从已记录查询抄写。`paired_transitions` 仅统计映射一致的 Continue 配对；证明后继状态属于关系的是 H2，不能把该计数报告成已证转移。

自动发现的 `κ` 只保留实际出口中已是字面常量、且属于编译产物返回 pad 集合的栈值；H0/H2 同时检查两侧实际栈槽等于该值。该集合仅是候选提议依据，不删除任何参考 JUMP 目标。havoc 在两侧对应栈槽写入相同常量，其他槽保持任意；若无法恢复字面值则不添加该谓词。返回地址上下文会增加实例数，仍受显式资源预算约束。

新增五个小型 EVM runtime 合约，IR 和 amd64 均由未修改的 `go-hpc-evm b3ddbdb553d776f74f8bb037a963d611037da16d` 实际编译；它们不是对已有机器码手改跳转的合成配对。生成过程核对 `gas_create` 基线 hex 完全一致、IR JSON 结构一致，并记录源码、依赖清单、生成器和产物哈希于 `tests/data/lockstep_loops_manifest.json`。

| 产物 | 循环行为 | 完整证据 |
| --- | --- | --- |
| `lockstep_counter_loop` | 每轮递增 256-bit 计数器，无源级退出条件 | 真实入口、TAG/OOG、局部定理与自回边 |
| `lockstep_fmp_loop` | 每轮读取并增加 `mem[0x40]`，再回跳 | 包含符号 m/f 实例、完整内存关系与回边闭包 |
| `lockstep_storage_loop` | 符号 calldata 控制循环，持续 SLOAD/SSTORE 更新，最后返回 slot 值 | storage、host gas 序号、正常返回与回边闭包 |
| `lockstep_return_loop` | 循环进入辅助块，再经动态 JUMP 返回循环头 | 返回地址谓词、真实动态 JUMP、回边闭包 |
| `lockstep_calldata_loop` | 以符号 calldata 的首个 word 为计数，逐轮递减至零并 RETURN | 条件回边、正常返回、OOG；输入长度与内容保持符号 |

这些样本在 FIXED_BUDGET 与 FULL 两种模式的测试中均取得完整证书。FULL 对任意初始 uint64 gas 验证；“无界循环”指验证不设置 EVM 循环迭代次数，也不按 gas 次数展开。真实有限 gas 会触发 OOG，证书同时覆盖这一终止行为；不宣称物理运行在有限 gas 下无限执行。

复现生成与验证：

```bash
poetry run python -m tools.generate_block_loop_fixtures --compiler-root /path/to/go-hpc-evm
poetry run pytest tests/integration/test_block_symbolic_loops.py -q
poetry run python -m tools.verify_block_lockstep tests/data/lockstep_fmp_loop \
  --gas-check full --timeout-ms 10000 --wall-seconds 180 --hard-wall-seconds 210
```

新的运行报告在 `reports/block-lockstep-symbolic-2026-09-14/`。小型循环证书证明该能力路径已经贯通，不能外推为 CErc20、Safe 或所有 TOP 块都会成功，也不能据此声称块级方案优于整程序模式。CErc20 的长预算评估必须单独报告实际已完成节点、未完成义务、分层耗时与完整证书状态。


### 14.6 长预算结果与当前缺口（2026-09-15）

两轮 CErc20 均使用 FULL 符号 gas、完整 uint64 calldata 长度、per-hit summary、单查询 5 秒、局部深度 400、最多 8192 个实例：

| 运行 | 软／硬预算 | 已返回局部实例／完整局部定理 | 整程序证书 |
| --- | --- | --- | --- |
| 符号 m/f、收集式编排 | 1800／1860 秒 | 172／162 | 无，硬超时 |
| 再加入返回地址谓词 | 600／660 秒 | 95／94 | 无，硬超时 |

两个运行绑定不同源码哈希，预算不同，期间也有其他测试／探针运行；这些是诊断材料，不能作为严格性能对比或“块级优于整程序”的证据。报告含全部 723 个源块的诊断状态，未访问和未完成节点不计为已证明或不可达。第二轮的复杂节点 `pc=13087` 消耗了大量时间；之后新增每节点软预算及 summary 期限传播。对该真实节点设置 15 秒软预算的定向运行在约 21.7 秒后返回 `ProofBudgetExceeded`，随后同一 prover 的 `pc=0` 局部证明成功，说明节点到期未污染后续证明。该实验也表明软预算不是硬墙钟保证。

对 `pc=792, k=3, m=160, f=128` 的复核确认失败查询 `pair_5_0` 为 **unknown**（5 秒查询预算），不能表述成已找到终态反例。另一个局部关系反例确实为 SAT：`pc=13087 → 12983` 的 CALLDATALOAD，在 `calldata_size=2^64−2, offset=2^64−32` 时，`offset+32` 在机器码中回绕并选择完整 word 读取，EVM 语义则要求最后两字节零填充。实际两侧 live stack 不一致；这首先是当前局部关系与模型域下的反例，尚非从 Init 可达的整合约反例。已添加真实机器码 summary 的反向测试，不能用摘要把该反例消掉。实际 Go slice 长度合法域与当前 uint64 模型域须单独论证，未自动追加长度上界或 no-overflow 假设。

重新运行候选分析得到：CErc20 的 723 个块有 404 个 MSize TOP、435 个 fmp TOP，深度候选共 1842 个；Safe 为 350／368 个 TOP，深度候选 1644 个；ENSRegistry 为 0／9 个 TOP，深度候选 161 个。各 PC、候选值、TOP 来源和源码／输入哈希在 `*-candidates.json`，可用 `tools.block_candidate_report` 重现。它们仍是未受信任的候选分析，不能替代真正局部定理和 H0/H2。

当前已验收的能力是完整块图证明包括符号参数、动态返回及无迭代次数界限的循环；大型合约仍有未完成的复杂终态查询、动态 copy／CALLDATALOAD 切片成本、模型域与局部不变式缺口。不得把小型循环成功外推为大型合约已经等价。

2026-09-15 的最终循环报告与验收汇总见 [reports/block-lockstep-2026-09-15/README.md](reports/block-lockstep-2026-09-15/README.md)，包含新增的持久存储循环。
