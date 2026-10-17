# 任务 K：PoolManager 三个 SAT 结论定性（poolmanager-sat）

基线：`cloud/inputs-poolmanager` = 冻结提交 caa01b1（+ 任务输入提交 45721a2）。
交付分支：`claude/poolmanager-sat-g29rni`（本会话被限定只能推送到这个分支；任务书写的是 `cloud/poolmanager-sat`，内容相同，本地拉取时请用这个名字）。

## 结论

三个 SAT 都是 **真实不等价**，属于 **go-hpc-evm 的 x86 codegen 缺陷**，与 IR 的 `immediate_set` 无关，验证器的判定是对的。

三处的根因相同：codegen 把某个栈槽的值（或其中一个 limb）**暂留在寄存器里，延迟写回**。紧接着的多路径内联指令（SAR / SGT / SDIV）内部有分支，**只在其中一个分支里补了写回（spill）**，另一个分支没有。汇合以后，后续代码一律认为“已经写回”，于是从栈内存读这个值，在没有 spill 的那条路径上读到的是旧值。

| 节点 | EVM 片段 | 丢失的值 | 触发条件 | 可观测后果 |
|---|---|---|---|---|
| 7132 | `SIGNEXTEND(15,A); SWAP1; SAR(128,T); SIGNEXTEND; SUB; …SGT/SLT…; JUMPI 7572` | ① `sext(A)` 的 limb0；② 差值 `d` 的 limb3 | ① `T ≥ 0`（SAR 走非负分支）；② `d < 0` | 跳转目标不同（7205 和 7572），栈槽 13 不同 |
| 7329 | Uniswap `tickSpacingToMaxLiquidityPerTick`：`sub(sdiv(MIN_TICK,ts), slt(smod(MIN_TICK,ts),0))` … | ① `slt(...)` 的结果（整字）；② `minTick`（整字） | ① 被除数 `MIN_TICK<0`：只要 `MIN_TICK % ts ≠ 0` 就触发；② `ts < 0` | `numTicks` 少 1，`maxLiquidityPerTick` 偏大。`tickSpacing=60, liquidity=max+1` 时 EVM 跳 7528，x86 落到 7456 |
| 7024 | `POP; DUP14; SIGNEXTEND(15); SWAP1; SAR(128); JUMP 15674` | `sext(A)` 的 limb0 | `T ≥ 0` | 出口栈槽 17 的 limb0 变成 `T.z0`，因此 H2 的 `live_stack_prefix[17]` 为 SAT |

7329 的后果最严重：tickSpacing 为 10、60、200 这些标准值时都会触发（887272 = 2³·110909，它们都不整除 887272）。x86 算出的每 tick 流动性上限略高于 EVM，所以 EVM 上应当 revert（TickLiquidityOverflow）的 modifyLiquidity，在 AOT 上会成功。这是共识分歧。

**没有改验证器代码**：不存在需要修的验证器问题。本次只提交了报告和离线复现脚本。

## 1. 复现与反例

复现方式（与普查同一套配方，在进程内调用 `BlockEquivalenceProver`）：

```
echo '[{"pc": 7132, "stack_depth": 16}]' > /tmp/n.json
PYTHONPATH=. poetry run python tools/probe_block_obligations.py cloud-inputs/poolmanager/PoolManager /tmp/n.json \
    --output /tmp/probe.json --timeout-ms 30000 --node-seconds 600 --formula-dir /tmp/formulas
```

- 7132：约 46 秒复现，结果为 `outcome mismatch x86_maps_0_0: x86 path 0 implies conjunct 0 of evm path 1 (solver=sat)`。EVM 有 3 条路径（0→7205，1→7572，2→终止），x86 有 14 条。x86 path 0 的出口是 0x53362，就是 pc 7572 的地址。公式落盘为 `pc7132_d16_x86_maps_0_0_*.sexpr`。
- 7329：同一配方可以复现（普查中该查询用了 560 秒）。求解器模型见第 3 节。
- 7024：节点本身的局部定理是 **proved**；SAT 出在 H2。复现时先跑 `verification.block_parallel.discover` 得到冻结集，结果与普查一致：5052 个 context、3718 个 proof instance。然后对 k=π(c) 的四条出口边，逐个目标、逐个合取项检查 `base ∧ ¬conjunct`（见第 4 节）。

具体执行：`cloud-inputs/reports/poolmanager-sat/concrete_replay.py` 用一个小型 EVM 解释器（按 IR 操作逐条执行）对照 **Unicorn 上运行的真实机器码**。它按 callEngine 布局摆好栈和内存，builtin（status 5）按 Go runtime 语义代为执行，然后比较两边的跳转目标和整个栈。该脚本只作离线证据，依赖 `pip install unicorn`，没有加入项目依赖。

```
PYTHONPATH=. .venv/bin/python cloud-inputs/reports/poolmanager-sat/concrete_replay.py
```

输出（节选）：

```
pc=7132 solver model (T>=0)               EVM->7205 x86->[7572] MISMATCH
    slot 13: evm=0x…7fffffffffffffff78ec753061e631f9   x86=0x…80000000000000002f4b2cb53842b000
pc=7132 minimal: T=0, A=1                 EVM->7205 x86->[7205] MISMATCH   slot 13: evm=-1  x86=0
pc=7132 T<0 (spill taken)                 EVM->7205 x86->[7205] MISMATCH   slot 13 limb3 = 栈上旧值
pc=7132 T<0, d<0, stale slot-13 limb 3    EVM->7205 x86->[7572] MISMATCH
pc=7329 tickSpacing=60                    EVM->7456 x86->[7456] MISMATCH   slot 12: evm=0x23741fda…  x86=0x23746e6a…
pc=7329 tickSpacing=60, liquidity=max+1   EVM->7528 x86->[7456] MISMATCH
pc=7329 tickSpacing=1 (MIN_TICK % ts == 0) AGREE
pc=7024 H2 model: T>=0, A.z0=2^64-1       EVM->15674 x86->[15674] MISMATCH  slot 17: evm=0xffffffffffffffff  x86=0
pc=7024 T<0 (spill taken)                 AGREE
```

## 2. pc=7132

求解器模型（`premise ∧ x86_0 ∧ ¬c0(evm_1)`，sat，0.08 秒）：

```
stack_15 (T, 栈顶)   = z3..z0 = 0x4000000000000000 0x2ff1f1196502b000 0x0 0x00a6c4642cc00000
stack_4  (A, DUP12)  = z1,z0  = 0xc000000000000000 0xb7057be9031c7e07
gas = 0x20000000，其余栈槽不影响结果
```

EVM 语义：`d = sext128(T >>s 128) − sext128(A) = 0x7fffffffffffffff78ec753061e631f9 ≤ INT128_MAX`，不溢出，落到 7205。
x86：`d' = 0x80000000000000002f4b2cb53842b000 > INT128_MAX`，跳到 7572。差别正好是 `A.z0` 被换成了 `T.z0`。

指令级证据（地址为 base 0x1000 时的地址，块入口 0x4e01e）：

- `SIGNEXTEND(15, A)` 的结果留在 `rsi:rdi:r8:r9`（0x4e1c6–0x4e1fb），没有写回栈。
- `SWAP1`（0x4e1fe–0x4e21c）把 T 从 `[r14-0x20]` 复制到 `[r14]`，codegen 记账为“`[r14-0x20]` 槽的值在 rsi..r9 中”。
- `SAR(128)` 在 0x4e220 检查符号（`shr rax,0x3f; jne 0x4e42b`）：
  - 负分支 0x4e42b 在 **0x4e452 `mov [r14-0x20], rsi`** 写回 limb0，因为它在 0x4e4b0 要用 rsi 做掩码；
  - 非负分支 0x4e231–0x4e426 **没有这条写回**。
- 两条分支在 0x4e6ad 汇合。下一个 SIGNEXTEND 改写了 rsi（如 0x4e776 `mov rsi,0`），随后 **0x4e806 `sub rax, [r14-0x20]`** 按“已写回”读取 limb0；`sbb rdx,rdi / rbx,r8 / rsi,r9` 用寄存器中的 limb1–3。在非负路径上读到的是 `T.z0`。

同一块里的第二处：SUB 的结果 d 在 0x4e833–0x4e841 只写回了 limb0–2。limb3（rsi）的写回 **0x4e885 `mov [r14-0x48], rsi`** 位于 `SGT(INT128_MAX, d)` 内联分支的一侧：`d<0` 时从 0x4e84f 和 0x4e883 跳到 0x4e8b5，跳过了这条写回。随后 `SLT(d, INT128_MIN)` 在 0x4e8d2 读 `[r14-0x48]`，读到的是旧值。例如旧值最高位为 1 时，x86 误判溢出跳到 7572（见上面输出的 “stale slot-13 limb 3” 一行）。

## 3. pc=7329

EVM 片段就是 Uniswap v4 的 `tickSpacingToMaxLiquidityPerTick`（`ts = signextend(2, mload(e1+128))`、`L = mload(e8+32) & uint128max`，最后 `JUMPI 7528 if L > maxLiquidityPerTick`）。

- 第一处：`SLT(smod(MIN_TICK,ts),0)` 的结果在 rax（0x511bf/0x511c8）。之后内联的 `SDIV(MIN_TICK, ts)` 只在“被除数非负”分支的 **0x5128f `mov [r14+0x80], rax`** 写回它。被除数是常量 −887272，0x51249 总是跳到 0x5156e，所以这条写回永远执行不到。`[r14+0x80]` 停留在 0x50eda 写入的 0，于是 **0x51964 `sub rax, [r14+0x80]`** 算出 `minTick = sdiv − 0`。结果是：只要 `MIN_TICK % ts ≠ 0`，`numTicks` 就少 1。
  - Unicorn 跟踪 ts=60：0x51141 时 smod = −52；0x511cf 时 rax = 1（slt 正确）；0x5195d 时 `[r14+0x80]` = 0，即丢失。
- 第二处：`minTick`（rax..rbx）只在第二个 `SDIV(887272, ts)` 的“除数非负”分支 **0x51a5d–0x51a69** 写回 `[r14+0x60]`。`ts<0` 时 0x5211d 读到的是旧值 ts。跟踪 ts=−887272：0x5211d 时 `[r14+0x60]` = ts。tickSpacing 为负在协议上非法，但语义上仍然不一致。
- 普查/求解器层面：7329 的 SAT 是 `x86_maps_0_0`，即 x86 path 0 没有蕴含 evm path 1 的跳转条件。具体执行给出了跳转确实分叉的输入：`tickSpacing=60, L=⌊(2¹²⁸−1)/29576⌋+1` 时 EVM 跳 7528，x86 落到 7456。
- 随机差分测试：3000 组随机输入中 2648 组不一致。

求解器模型（单独重跑 `premise ∧ x86_0 ∧ ¬c0(evm_1)`，sat；Z3 的两次运行给出的模型不同，这里列第二次的，因为它读出了内存）：

```
stack_1 (e1) = 0x198822c7a0   -> mload(0x198822c820) = 0xe0…e0ebab180   => tickSpacing = signextend(2, 0xbab180) = -4542080
stack_8 (e8) = 0x1894929200   -> mload(0x1894929220) = 0xe0…e090e082b2…19a06 => L = 0x90e082b25950f65b18b270402119a06
gas = 0x7cb45800000400，memory_size = 0
```

把这两个内存字搬到映射窗口内具体重放（`concrete_replay.py` 的 `compare`）：EVM 端 `minTick = 0 − slt(smod(MIN_TICK,ts),0) = −1`，`maxTick = 0`，`numTicks = 2`，`max = 2¹²⁷−1 ≥ L`，不跳转，到 7456。x86 端丢失了 minTick（第二处写回缺失，ts<0），读到旧值 ts，算成 `numTicks = 0 − ts + 1 = 4542081`，`max = 0x3b19838221b2acd0eab694c369b < L`，跳到 7528。与求解器结论一致：x86 path 0 出口 7528，EVM 走 path 0（7456）。第一次运行的模型给出的栈值（`stack_8 = −20` 等）属于同一类反例，只是没有导出内存。

## 4. pc=7024 的 H2

- 实例与 context：普查中的 `k=(7024,19,None,None,())`，其 context 为 `c=(…, ((2,7038),))`；`k=(7024,19,768,768,())`，其 context 为 `c=(…, ((2,7038),(7,0),(8,320),(10,640),(16,160),(17,448)))`。两个 k 的局部定理都已证出（EVM 2 条路径，x86 5 条：0–3 出口到 0x9dd9d = pc 15674，4 为终止）。
- 冻结集中 pc=15674 的目标有 4 个：深度 12 的两个、`(15674,19,None,None,((2,7038),))`、`(15674,19,768,768,((2,7038),(7,0),(8,320),(10,640),(16,160),(17,448)))`。
- 逐合取项检查 `base ∧ ¬conjunct`（`base = premise_k ∧ E_c ∧ e_0 ∧ x_j`）：
  - 边 (0,1)、(0,3)（SAR 负分支）对“正确目标”**全部 UNSAT**，能闭合。正确目标指：symbolic context 对应深度 19、常量 (2,7038) 的实例；768 context 对应深度 19、768/768、同一组常量的实例。
  - 边 (0,0)、(0,2)（SAR 非负分支）对正确目标 **只有 `live_stack_prefix[17]` 一个合取项 SAT**。也就是出口栈从底数第 17 槽（自顶第 2 槽，`sext(A)`）的 x86 值 ≠ EVM 值。模型示例：`stack_17.z3 = 0`（T≥0），`stack_4.z0 = 0xffffffffffffffff`，`stack_17.z0 = 0`。此时 EVM 槽值为 `0xffffffffffffffff`，x86 为 `T.z0 = 0`。
  - 其他目标失败在 `stack_geometry`（深度 12 ≠ 19）或 `memory_size` / `free_memory_pointer` / `stack_constant_predicate`（768 和常量对不上），失败原因合理。
- **目标实例的选择是正确的**：失败只出在栈内容这一个分量上，换成任何目标都无法闭合。
- 指令级：SAR 的负分支在 **0x4c9e1 `mov [r14-0x40], rsi`** 写回 limb0，非负分支没有。块出口 **0x4cc53–0x4cc5b** 只把 rdi/r8/r9 写到 `[r14-0x38..-0x28]`，认定 limb0 已在 `[r14-0x40]`；而那里还是 SWAP1（0x4c78a）之前留下的 T.z0。随后 `jmp 0x9dd9d`（pc 15674）。

## 5. 健全性交叉检查（验证器没有漏报）

为排除“同类 codegen 缺陷在别的块上被误证”的可能，用 `concrete_replay.py --fuzz 300` 对普查中尝试过的、且全部操作都在解释器支持范围内的块，每个实例做 300 组随机差分执行（带符号字、int24、128 位、小指针等分布）。结果：

| 普查结论 | 实例数 | 块数 | 有效比较次数 | 不一致的实例 |
|---|---|---|---|---|
| proved | 163 | 86 | 43,395 | **0** |
| inconclusive / split（7024×2、7132×2、7329×2） | 6 | 3 | 1,256 | **6**（全部不一致） |

已证实例在具体执行中没有出现反例；三个 SAT 块在随机输入下大比例不一致，与求解器的结论吻合。
（7329 的有效次数较少，是因为随机指针多数让 MLOAD 越出映射窗口，这类运行被跳过。专门构造的输入见第 3 节。）

注：抽样不能证明验证器健全，只是没有找到反例。

## 6. 测试

- 全量快测 `poetry run pytest tests/unit -q -m "not slow" -p no:cacheprovider`：（待补）
- 本次没有改 `verification/ state/ x86_64/ evm_ir/ common/`，`model_sources_sha256` 与 caa01b1 相同，Safe/ENS 证书不受影响。

## 7. 给编译器侧的建议（不改 Go，仅供参考）

在 `evm/aot/impl_amd64.go` 里检查 SAR、SGT/SLT（与常量比较）、SDIV/SMOD 的内联模板：寄存器缓存栈槽的“写回 / 驱逐”应当在 **分支之前** 统一完成，或者在每个分支末尾都做。目前是在某个分支中、某个寄存器即将被改写时才就地 spill，这样汇合点的寄存器分配状态在各分支间不一致。修复后可用上面的命令回归：三个节点应当证出，`concrete_replay.py` 应全部 AGREE。

## 8. 未解决的问题

- 用 unicorn 做的具体执行依赖手工建模的 callEngine 布局和 builtin 协议，只作为证据，不进入证书。
- 不能访问 go-hpc-evm 源码，无法指到 Go 源码的具体行，只能给出机器码地址。
