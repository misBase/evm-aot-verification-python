# 块级 lock-step 等价验证 —— 关键机制说明

本文回答四个问题，是对 [概要设计 §3.2](块级lockstep等价验证-概要设计.md) 的展开答疑：

1. `(k, m, f)` 三参数联合专门化，以一个块为例，以前是什么、现在是什么？
2. "一个块变成多条定理"是什么意思？以前全符号只用证一次，现在的多条定理弱在哪、靠什么补？
3. 全符号为什么证不出来？本质原因是什么？
4. 整程序（path observation）模式为什么没有这个问题？块变小了指令少了，为什么反而跑不出来？

文中所有数字标注了出处：`§12.x` 指 [块级lockstep等价验证方案.md](块级lockstep等价验证方案.md)，代码锚点给到行号。

---

## 1. 三参数联合专门化：以一个块为例

### 1.1 一句话

专门化 = **给切点关系 `R_cut` 加索引**。

- 以前：一个块 = 一条定理，"从任意满足 `R_cut` 的状态出发"。
- 现在：一个块 = 一族定理，每条带 `(k, m, f)` 的取值，"从任意满足 `R_cut` **且** `SP=3 ∧ MSize=0x80 ∧ mem[0x40]=0x80` 的状态出发"。

| 参数 | 含义 | 作用 |
|---|---|---|
| `k` | 绝对栈深（EVM `SP=k`，x86 `byte_offset=32k`） | 栈槽地址变字面量 |
| `m` | `MSize` | 内存扩展 gas、边界比较变字面量 |
| `f` | `mem[0x40:0x60]` 的 256-bit 值（free memory pointer） | 内存写地址变字面量 |
| `κ` | 可选：某栈槽是字面返回地址 | 动态 JUMP 目标可判定 |

### 1.2 样本块

典型 Solidity 块体（ENS 1455 那类，无 CALLDATALOAD / copy）：

```
TAG(pc=1455)          ; 切点在 TAG 之前（决策一）
PUSH1 0x40  MLOAD     ; f := mem[0x40]
DUP1  PUSH1 0x20 ADD  ; f+0x20
...   MSTORE          ; 写 mem[f]
...   JUMPI
```

x86 侧：栈槽在 `[r14 + byte_offset]`，内存在 `[r15 + addr]`。

### 1.3 以前：切点 havoc 成完全符号状态

| 分量 | 切点上的值 | 后果 |
|---|---|---|
| 栈深 | `byte_offset` 符号（老代码还套 `∈[k*0x20, 0x4000]` 的 envelope） | TAG 前缀的栈下溢/超限检查判不死，一进门就分叉 |
| `MSize` | `m_sym : BitVec(64)` | MSTORE 扩展 `max(m_sym, roundup32(a+32))` 是符号 ITE，后续 gas 比较全是活分支 |
| `mem[0x40]` | 快照数组里的符号字 `f_sym : 256-bit` | 写地址 `r15 + f_sym`，与字面量地址的别名不可判 |

块里每条 `jcc` 都判不死 → 路径指数增长 → timeout。

### 1.4 现在：登记实例 `(pc=1455, k=3, m=0x80, f=0x80)`

havoc 时把常量钉进状态（`verification/cutpoint_relation.py`）：

```python
byte_offset = BitVecVal(3 * 0x20, 64)                 # :648   k → 0x60
memory_snapshot = write_evm_word(snap, 0x40, 0x80)    # :696   f → mem[0x40] = 0x80
mem_size = BitVecVal(0x80, 64)                        # :710   m
```

同一个块体重走：

- `MLOAD 0x40` 直接读出 `0x80` → 写地址变 `r15 + 0x80`，Store 链可按地址分桶消解；
- `MSTORE` 扩展 `max(0x80, 0xa0) = 0xa0`，gas 是常量，相关 `jcc` 全部静态判死；
- TAG 前缀的栈深检查在 `0x60` 上直接可解。

实测（§12.2，ENS 1455）：timeout → **11 路径 / 3.0s / 判死率 93.5%**。

### 1.5 为什么必须"联合"

| 样本块 | 只固定 `m` | 只固定 `f` | 联合 |
|---|---|---|---|
| ENS 1455 | 80 路径 / 35.4s / 判死 47.5% | timeout / 78.3% | **11 路径 / 3.0s / 93.5%** |
| CErc20 5343 | timeout / 27.1% | timeout / 78.6% | **49 路径 / 42.5s / 94.3%** |
| Safe 6275 | 8 路径 / 4.8s / 95.1% | timeout / 85.5% | 8 路径 / 4.9s / 95.1% |

两个参数堵的是不同的洞：

- 只固定 `m`：gas 常量了，但写地址还是 `r15 + f_sym`，别名判不了，`f_sym + 32 vs 0x80` 的边界比较也判不了。
- 只固定 `f`：地址常量了，但 `max(m_sym, 0xa0)` 还是符号，每个扩展步都留 ITE 和活分支。

Safe 6275 只固定 `m` 就到 4.8s，**所以联合不是每块的正确性必需，只是主路径的工程默认**。

### 1.6 两个实现上的坑

1. **`f` 必须在建 x86 `Lambda` 视图之前写进快照**（`cutpoint_relation.py:694` 注释）。视图是 `Lambda(a, Select(snapshot, a - r15))`，捕获的是当时那个数组。先建视图再改 EVM 侧，两侧指向不同数组而 `memory` 分量等式仍"成立" —— 假绿。
2. **超界当场拒绝，不放宽**（`:713`）。超界的 assumption 会让 havoc 状态 unsat，那时任何义务都"证得过" —— 最危险的 vacuous 假绿。所以抛 `CutpointModelRangeError` 让调用方降级。

---

## 2. 一个块变成多条定理

### 2.1 具体是什么

节点身份就是 `BlockSpecialization(pc, k, m, f, stack_constants)`。同一个 `pc` 下可有多个 spec，每个走一次 `prover.prove(spec)`，产出独立的 `BlockTheorem`。

| 实例 | 来源 | 结果 |
|---|---|---|
| `(1455, k=3, m=0x80, f=0x80)` | 首次调用路径 | proved, 11 路径 3.0s |
| `(1455, k=3, m=0xc0, f=0xa0)` | 另一条前驱边 | proved |
| `(1455, k=5, m=None, f=None)` | 深度不同 + 参数被 widen | proved 或 timeout |

`result.diagnostics[pc]["instances"]` 就是这张表；`pc` 级 status 是所有实例的合取（`verification/block_program.py:322`）。

### 2.2 全符号那条定理确实更强

逻辑上 `∀k,m,f. P(k,m,f)` ⟹ `P(3,0x80,0x80)`。问题纯粹是**可得性**：那条强定理在 ENS 1455 / CErc20 5343 上都是 timeout（§12.2）。

所以这不是"用弱的换快的"，是"强的拿不到，退而求其次 + 把丢掉的那块显式补回来"。

丢掉的是反方向：实例定理的合取**不**蕴含强定理。缺口 = **"程序实际到达 1455 时，参数一定是这几组之一吗？"** 这就是覆盖义务。

### 2.3 覆盖义务：合理性的唯一来源

候选本身不可信。`verification/block_specialization.py` 文件 docstring 第一行：

> `Untrusted specialization candidates. This module proves no reachability/closure.`

真正的门在 `verification/block_program.py:355-368`：worklist 跑完后**冻结**实例集合 `ordered`，再对 `pending` 里每一条实际边（入口边 `source is None` → H0；块间边 → H2）重放一次 SMT 查询：

```python
targets = tuple(s for s in ordered if s.pc == pc)
goal = Or(*(And(*(g.condition for g in schema.relation_goals(e, x, s, ...))) for s in targets))
if not prover._check(name, And(joint, Not(goal)), edge_records):
    result.reasons += (f"{name} full successor relation not closed into pc={pc} ...",)
```

读法：**从实际到达该 pc 的两侧状态 `(e, x)` 和实际路径条件 `joint` 出发，证明它必然落进某个已登记实例的关系里。**

少登记一个 `m` 值 → 该查询 SAT 或 unknown → `reasons` 攒一笔 → 最后 `raise ValueError("certificate withheld")`（`:378`），证书不发。**fail-closed。**

两个配套细节：

- `propose` 里的 `closure_precheck`（`:293`）标了 `Optimistic precheck is diagnostic only`，因为那时集合还没冻结。**它不是门。** 晚发现的实例照样进 final goal，所以发现顺序不影响正确性。
- `ProgramCertificate.valid()`（`:57`）还要再查每个 Continue×Continue 结果对都有对应的已证边证书 —— 决策三说的"单块绿了什么都不代表"在这里闭合。

### 2.4 候选是怎么"指"出来的

`_discover`（`block_program.py:444`）：

- **`k` 是穷举，不是采样**：`solver.add(SP != depth)` 循环到 UNSAT（`:483`），穷尽该边所有可行栈深；超 `max_values_per_edge` 抛错。这一维完备。
- **`m` / `f` 不从 model 采样**：
  ```python
  parameters = tuple(v.as_long() if is_bv_value(v) else None for v in map(simplify, expressions[1:]))
  ```
  只有表达式 **simplify 后本身就是常量**才取值，否则 `None`（符号节点）。若写成 `model.eval(...)`，就会把"solver 恰好挑的一个值"钉成定理前提，覆盖义务随后必然 SAT —— 不假绿，但每条边都失败。
- **widening 保终止**：同一个 `(pc, depth, constants)` 上下文第二次带不同 `(m,f)` 来，直接塌成 `(None, None)`（`:478`）。否则循环每轮 msize 递增会无限发实例。旧的具体实例不删，final goal 是全体的 `Or`，覆盖仍成立。

### 2.5 结论

| | 依赖候选质量吗 |
|---|---|
| **健全性** | **不依赖**。指错、指漏、指了个到不了的值 —— 最坏是证书被扣留或多证一条没用的定理，不会假绿。 |
| **可完成性** | **完全依赖**。指太粗（全 `None`）→ 局部定理 timeout；指太细 → 实例爆炸撞 budget。 |

脆的地方：

1. widening 塌成 `(None, None)` 后符号节点很可能证不动 —— 退回"全符号"的困境。CErc20 **55.9%** 的块 MSize 是 TOP（§12.2），直接决定这条路线在该合约上成不成。
2. 预算耗尽（`max_instances` / `max_values_per_edge` / wall）全是 `raise`，fallback 是 `_independent_rerun` 整程序重跑，而整程序在 CErc20 / Safe 上 880s 跑不完（§12.1）。所以失败的实际形态是**"没结论"，不是"错结论"**。
3. `_discovery_cache` 的 key 是 `sexpr()` 字符串，语法不同就不命中 —— 只影响性能。

> **一句话**：具体值合不合理，不由发现算法保证，由 `H0_*`/`H2_*` 那批 SMT 查询保证；发现算法只决定跑不跑得完。

---

## 3. 全符号为什么证不出来

### 3.1 一句话

**剪枝器是语法级的 `simplify`，不是 solver。符号参数让语法判定失效，路径树从被砍 93.5% 变成被砍 47.5% —— 这在深度上是指数差。**

```python
# x86_64/cfg_executor.py:947
jump_condition = simplify(self._build_jump_condition(mnemonic, mstate))
fallthrough_condition = simplify(Not(jump_condition))
def _alive(cond):
    return (not self.use_reachability_check) or not is_false(cond)
```

整条流水线的吞吐全靠这个 `is_false`：拿掉它吞吐掉 10×，97.7% 的分支是被它静态判死的（见 `perf_jcc_simplify_load_bearing` 记录）。

### 3.2 select-over-store 的真实判定边界：同基 vs 异基

**判定边界不是"常量 vs 符号"，是"同基 vs 异基"。** 可复现实测：

```bash
poetry run python3 -c "
from z3 import *
m = Array('m', BitVecSort(64), BitVecSort(8)); f = BitVec('f', 64); g = BitVec('g', 64)
print('1)', simplify(Select(Store(m, f, BitVecVal(7,8)), f+0x20)))
print('2)', simplify(Select(Store(m, f, BitVecVal(7,8)), BitVecVal(0x40,64))))
print('3)', simplify(Select(Store(m, f, BitVecVal(7,8)), g)))
s = m
for i in range(4): s = Store(s, f+i, BitVecVal(i,8))
print('4)', simplify(Select(s, BitVecVal(0x40,64))))
"
```

| 表达式 | Z3 simplify 结果 | 能消吗 |
|---|---|---|
| `Select(Store(m, f, 7), f+0x20)` | `m[32 + f]` | ✅ Store 层被剥掉 |
| `Select(Store(m, f, 7), 0x40)` | `Store(m, f, 7)[64]` | ❌ 卡住 |
| `Select(Store(m, f, 7), g)` | `Store(m, f, 7)[g]` | ❌ 卡住 |
| 4 次写 `@f+i`，读 `@0x40` | 4 层 Store 原样堆着 | ❌ 卡住 |

`f` 与 `f+0x20` **同基**（非常量部分都是 `{f}`），常量差 `0x20 ≠ 0`，判异，直接下钻 —— 符号地址本身不是障碍。

项目自己的消解器 `common/store_forwarding.py:10` 把规则写死了：

> - 地址线性化为（非常量项多重集, 常量和 mod 2^64）；
> - 同基（非常量部分完全相同）⇒ 常量差直接判等/判异；
> - **异基 ⇒ 可能别名 ⇒ 放弃改写（fail-closed，留给求解器）**。

### 3.3 符号 `f` 真正卡在哪：Solidity 内存布局本来就是多基址的

| 区域 | 地址形式 |
|---|---|
| `0x00-0x40` scratch（keccak 用） | 字面量 |
| `0x40` free memory pointer 槽 | 字面量 |
| `0x60` zero slot | 字面量 |
| `f = mem[0x40]` 指向的动态区 | **符号** |

一个再普通不过的块：

```
PUSH1 0x40 MLOAD      ; f := mem[0x40]        读 字面量 0x40
DUP1 ... MSTORE       ; mem[f] := x           写 符号   f
PUSH1 0x40 MSTORE     ; mem[0x40] := f+0x20   写 字面量 0x40   ← 要穿过 Store(m, f, x)
PUSH1 0x40 MLOAD      ; 再取 fmp              读 字面量 0x40   ← 同上
```

第 3、4 行的字面量地址要穿过第 2 行的符号地址写 —— **异基，卡死**（即实测 2/4 的形状）。`f` 符号时，动态区与全部固定区之间的别名一律不可判，而这两类访问在同一个块里必然交替出现。

`f = 0x80` 之后所有地址都是字面量，全部同基（基址集为空 + 常量），两两比较纯语法判定，整条链塌成分桶后的标量。

### 3.4 判死失效 → 路径树指数展开

3.3 的产物不会安静待在内存里：它流进地址比较、流进 `max(m, roundup32(a+32))`、流进 gas 余额比较，最后流进 `cmp` 的标志位。`is_false` 面对一坨读不出值的 Store 链什么也判不出来 → 两支都活 → 各自继续堆链。

这是**正反馈**：判不死 → 状态变多 → 表达式更复杂 → 更判不死。

数字对得上（§12.2，ENS 1455）：深度 `d` 上活路径数 ≈ `(2(1-p))^d`。

| 判死率 `p` | 底数 `2(1-p)` | 行为 |
|---|---|---|
| 0.475（仅 msize） | 1.05 | 发散 |
| 0.935（联合） | 0.13 | 收敛 |

**93.5% 不是"更好"，是跨过了收敛/发散的分界线。**

### 3.5 退回 solver 也救不了

自然退路是判不出来就问 solver。§12.5 实测否决：ENS 1455 的 133 次可达性查询耗 46.5s，整体仍超时。因为要查的公式**正是**那坨卡住的 Store 链，每次查询都得重新面对整个历史 —— 符号化把 O(1) 的语法判定换成了 O(历史长度) 的语义判定，且每个分支付一次。

代码里的折中是 `reachability_timeout_ms=50`（`x86_64/cfg_executor.py:52`）：50ms 查不出来就当可达。**solver 在这里是捡漏的，不是主力。**

### 3.6 一条重要推论：区间不够，必须是常量

§12.5 试过"只把 MSize 区间加进 assumptions"，静态剪枝收益很小。因为剪枝器是语法 `simplify`，`m ∈ [0x80, 0x4000]` 这条 assumption 根本不参与 `is_false` 的判定 —— 只有 solver 看得见它，而 solver 已被 3.5 排除。

---

## 4. 整程序模式为什么没有这个问题

### 4.1 因为它的内存是从字面量长出来的

`state/evm_memory_state.py:34`：

```python
self.Memory = K(BitVecSort(64), BitVecVal(0, 8))   # 常量全 0 数组
self.MSize  = BitVecVal(0, 64)                      # 字面量 0
```

Solidity 前言 `PUSH1 0x80 PUSH1 0x40 MSTORE` 之后，`MLOAD 0x40` 经 store forwarding 拿到**字面量 `0x80`**。此后 fmp 每次更新都是 `字面量 + 常量`，永远是字面量。全程所有内存地址同基，`resolve_select_over_store` 全程可判，链底还是 `K(0)` 能直接 Select 出 0。

对照 havoc（`verification/cutpoint_relation.py:690`）：

```python
memory_snapshot = _Array(f"{prefix}_evm_mem0", BitVecSort(64), BitVecSort(8))  # 自由符号数组
```

链底从 `K(0)` 变成自由数组，`mem[0x40]` 从字面量变成符号。

> **整程序模式没有这个问题，是因为它没扔掉历史。**

### 4.2 指令少为什么反而跑不出来

因为 **SMT 代价几乎不是指令数的函数**，是「符号输入维度 × 分支可判性」的函数。

| | 指令数 | 初始状态 | 结果 |
|---|---|---|---|
| 整程序 ENS | 3000+ | **完全具体**（`K(0)` / `MSize=0` / 栈空 / gas 字面量），唯一符号源是 calldata | jcc 判死 86.5%（§12.1），跑得完 |
| 块级 havoc | ~40 | **15 个分量全符号** | 判死 47.5%（§12.2），timeout |

块级不是"把程序变短了"，是**把前面 2960 条指令算出来的结果扔了，换成"任意值"**。而"任意值"比任何一个具体值都难证 —— 它包含全部 2²⁵⁶ 种可能，其中绝大多数真实执行到不了，但每一种都要证（`f` 未 32 字节对齐、`f` 与 msize 区间交叠、`f = 2^256-1` …… 这些形状会激活 codegen 里真实执行永远走不到的溢出/边界分支）。

块级还额外多付两笔整程序不付的钱：

- **TAG 前缀**（决策一）：切点在 TAG 之前，R14 完全任意，每个块都要自己重走 gas 检查 + 栈深检查两条错误分支。整程序模式里这些在具体值上直接判死。
- **义务形态**：块级要证两侧 15 个分量的**关系**，外加每条边的 H2 闭包；整程序只要证终态投影一致。

### 4.3 那为什么还要做块级

整程序的瓶颈**不在内存别名**（那边很干净），在别处：路径数随深度指数增长，表达式随**内部函数调用链**线性膨胀（ENSRegistry ~35 节点/步，见 `perf_jcc_simplify_load_bearing` 记录）。结果是 ENS 跑得完，CErc20 / Safe 880s 跑不完（§12.1）。

所以这是一次交换：

| 模式 | 状态确定性 | 路径深度 |
|---|---|---|
| 整程序 | 高（地址全字面量） | 深 → 指数爆炸 |
| 块级全符号 | 低（地址全符号）→ 块内判不死 | 浅 |
| **块级 + (k,m,f)** | **高（重新注入）** | **浅** |

这也解释了**为什么恰好是这三个参数**：它们正好是决定"地址是不是字面量"的全部三个量 —— `k` 管栈槽地址，`f` 管内存写地址，`m` 管边界与扩展 gas 比较。

> **专门化的本质**：不是"切断当前块与历史的耦合"，而是**在不重放历史的前提下，把历史里唯一重要的那点信息（内存布局的形状）重新注入**。

---

## 5. 边界

这个注入在 CErc20 上有 **55.9%** 的块做不到（MSize 是 TOP，§12.2），那些块退回全符号 = 退回跑不出来。方案记录的"尾部 3-9% 的块不收敛"、"CErc20 / Safe 仍无证书"，根因都是这条。

**块级路线目前赢的是 ENS 那一类，不是全部。** 下一步的唯一主条目是 memory_size 在 havoc 下的不变式，不是 CALLDATALOAD。

## 6. 代码锚点

| 机制 | 位置 |
|---|---|
| 三参数注入 havoc | `verification/cutpoint_relation.py:648` / `:696` / `:710` |
| 专门化实例定义 | `verification/block_specialization.py` |
| 候选发现（k 穷举、m/f 非采样、widening） | `verification/block_program.py:444-483` |
| H0/H2 覆盖义务（唯一的门） | `verification/block_program.py:355-368` |
| 证书消费端 | `verification/block_program.py:57` `ProgramCertificate.valid` |
| jcc 语法剪枝 | `x86_64/cfg_executor.py:947-951` |
| select-over-store 保守消解 | `common/store_forwarding.py:65` |
| EVM 内存初值 `K(0)` | `state/evm_memory_state.py:34` |
