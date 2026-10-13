# 测试数据说明

验证管线消费的 fixture。每条程序通常是 **IR JSON**（`load_ir_from_json` 的输入）配 **amd64 机器码 hex**（Capstone 反汇编的输入）；少数还带同名 **`.txt`** 的 x86-64 反汇编文本——仅供人工审阅 hex，无测试读取。

## 概览

| 类别 | 文件 | 来源 | 再生 |
| --- | --- | --- | --- |
| gas 基线 | `gas_*.{json,hex}` | go-hpc-evm 编译 | `TestGenGasFixtures`（见下） |
| 真实合约 | `ext_contracts/` | 主网合约 runtime bytecode 编译 | `ext_contracts/README.md` |
| 多块 / 控制流样本 | `muti_block*`、`jumpi*`、`perf_erc20_lite` 等 | go-hpc-evm 编译 | 无（手动重编） |
| 手写 IR 小样 | `add_*`、`*_bounded` | 手写 IR JSON | — |

## gas 基线 `gas_*.{json,hex}`

go-hpc-evm 真实编译产出：同一段 EVM 字节码同时导出 IR JSON 与 amd64 hex，两者必须来自同一次编译。四类中唯一带再生脚本，维护细节如下。

### 绑定的上游版本

当前基线 **`b3ddbdb`**（`fix(aot): correct SIGNEXTEND jump targets and add fuzz test`），仓库 `$GOPATH/src/github.com/bcds/go-hpc-evm`。这段文字**就是**事实源——没有测试去核对它，见下。

绑定的东西有两类：

1. 机器码是该版本 codegen 的产物，IR 的 `static_gas` / host `Param` 索引也是；
2. `state/host_gas.HOST_GAS_UPPER_BOUNDS` 的数值来自对该版本 `evm/host.go`、`evm/aot/*`、`params/protocol_params.go` 的人工审计（**不是** `evm/gas_table.go`——那是解释器的 gas 表，AOT 从不调用）。

第 2 条是**手工同步项，没有任何自动提醒**：上界写小了是**静默缩域**（两侧仍共享同一个 UF、仍相消、仍 UNSAT），Python 侧任何测试都看不见。数值没有可执行的 oracle——每条上界取自哪个 Go 函数的哪条分支、常量在哪一行，都记在 `HOST_GAS_UPPER_BOUNDS` 的注释里，照行号读源码复核。

这里曾有一条比对本地 go-hpc-evm HEAD 的测试（`tests/support/go_revision.py`），已删：它绑的是**开发机工作区状态**，而决定健全性的是产出这批 checked-in fixture 的编译器版本，两者没有因果关系；上游任何无关改动都会让它变红，而消红最省事的做法恰好是它想阻止的"不复核直接改基线"。

所以换编译器版本时**只能靠流程**：复核上界 → 重新生成 fixture → **最后**才更新上面那行基线。完整流程见 `docs/关键问题记录.md` #20。

### 重新生成

生成器 `TestGenGasFixtures` 是 go-hpc-evm 仓库 `evm/aot` 包内的 in-package 测试（依赖同包的 `registerBuiltinHostsInOrder` / `NewEnginEVM` / `engineEVM` / `dealWithEvmHostFunc`）。

**它不是上游的 tracked 文件，而且反复消失**：2026-08-07 补 `gas_returndatacopy` / `gas_log0` / `gas_log4` 时是第一次（`grep TestGenGasFixtures` 全仓库零命中），2026-08-28 补 `gas_create_same_args` 时又一次。所以**再生前先确认该文件是否还在**，不在就照下面重建。

重建时有两个必须踩对的点，都不会给出有意义的报错：

1. **`MarshalJSON` 必须排在 `compileEvmFunction` 之后**（详见下一节第 2 条）。
2. **`hostIndex` 要自己建**。它只在 `CompileEVM`（`engine_evm.go:305` 起）里构建，而生成器为了拿到 `irResult` 指针必须自己调 `ir.CompileEVM` + `compileEvmFunction`、绕过了它，结果是 host op 在 `setHostParam` 处报 `predefined host "log" is not registered`。照上游那段逐字复制即可——遍历 `DefaultHostSpecs()` 这个预定义 catalog 而非 map，以固定 host id（in-package 的 `registerBuiltinHostsInOrder` 可直接复用来建 `EvmHosts`）。注意**非 host op 的 fixture 不受影响**，只生成 RETURNDATACOPY 这类指令时不会暴露，容易漏。

**重建后先做一次自校验**：让生成器顺带重新生成一条**已 checked-in** 的 fixture（如 `gas_create`），与仓库里的 `.json`/`.hex` 逐字节比对。相同才说明重建版走的是与基线同一条 codegen 路径；不同就先查生成器，别急着拷贝新产物。校验通过后**只拷新增的那条**，不覆盖既有 fixture。

**必须 `GOARCH=amd64`**：开发机是 darwin/arm64，直接 `go test` 会写进 ARM64 机器码，而 Python 侧用 x86 反汇编器读它，表现为乱码指令或 `ADD only supports 64-bit operands`，且**不会**有任何 arch 错误提示（这个坑真实发生过，fixture 被静默覆盖成 arm64）。交叉编译安全——生成器只导出 `codeSegment` bytes，从不执行编译产物。

```bash
cd "$GOPATH/src/github.com/bcds/go-hpc-evm"
OUT=$(mktemp -d)   # 新目录：避免上一次的残留产物冒充本次输出
GAS_FIXTURE_OUT="$OUT" GOARCH=amd64 go test ./evm/aot/ -run TestGenGasFixtures -v
# 校验：**每份** hex 都要查，不能只抽一份
for f in "$OUT"/*.hex; do printf '%s %s\n' "$(head -c 8 "$f")" "$f"; done
# 期望全部是 4d8b7538（arm64 是 011c40f9）
```

### 加一条新 fixture

1. **操作数取互不相同的可辨识值**。全 0 的退化实例会同时掩盖槽位交换（如 `calcMemSize64` 的 `Back(1)`/`Back(3)` 搞反）与 host-gas UF 的参数顺序错误——旧版 `gas_create` 的 value/offset/size 全 0 且 `size==0`，内存扩展 fee 与 word gas 双双为 0，等于什么都没验。

   取值时注意 **`calcMemSize64` 是 `offset + size`、对称**：offset/size 对调后内存扩展 fee 不变（`0x20+0x11` 与 `0x11+0x20` 同样是 2 words），槽位错误只能靠**非对称**费用项检出——LOG 的 `size*LogDataGas`、COPY 系的 `toWordSize(length)*CopyGas`。所以要挑能让这些项变号的值（`gas_log0` 的 `0x11*8=136` vs 对调后 `0x20*8=256`）。
2. **IR 的 `MarshalJSON` 必须在 `compileEvmFunction` 之后**——后者原地填 host op 的 `Param` 为 host function index；先 marshal 会导出 `Param=0` 的残缺 IR，Python 侧解析出的 host 调用点全部错位。
3. **要验 host-gas 调用序号就得用完全相同的实参调两次**。`gas_two_sload` 读的是两个**不同** slot，两次调用本来就是不同 UF term，验不到序号机制。真正管用的是同参重复：`gas_sload_same_key`（同 slot 读两次 → 真实 cold 2100 然后 warm 100）与 `gas_create_same_args`（同实参 CREATE 两次 → 真实成本因 `gas − gas/64` 递减而不同）。两者对应 §7.1 收录判据的两类非纯来源——判据是「cost 是否为 UF 实参的纯函数」，**不是**旧版的「碰不碰 access list」（CREATE 就是照旧判据漏掉的）。

### 2026-08-07 新增的三条

补的是 `_DYNAMIC_GAS_KINDS`（`verification/program_verifier.py`）里两处「verifier 认为已建模、却没有任何 IR↔x86 对照」的缺口。

| fixture | EVM bytecode | 覆盖点 |
| --- | --- | --- |
| `gas_returndatacopy` | length=0x04, dataOffset=0x07, destOffset=0x20 | RETURNDATACOPY 的内存扩展 + `CopyGas`(3)。x86 前言 `makeCalcCopyIns(0, 2, 2)` 与 CALLDATACOPY/CODECOPY 逐字同构 |
| `gas_log0` | size=0x11, offset=0x20 | LOG n=0：topic gas 项整个消失 |
| `gas_log4` | topics=0x54/0x53/0x52/0x51, size=0x11, offset=0x20 | LOG n=4：topic gas 取最大值 |

两个 LOG fixture 的价值不在 `LogTopicGas` 常量本身（`gas_log1` 已经在验），而在 **topic 数的读取链**：把 EVM 侧 n 写死成常量 1 这类错误在 n=1 上没有任何差别，`gas_log1` 结构上抓不到。配上 n=0/4 后 0/1/4 三点还能钉死 `gas = 常量 + n*TopicGas` 的线性关系。

### 2026-08-28 新增的一条

`gas_create_same_args`：`PUSH 0x20/0x40/0x07 → CREATE → POP` 重复两遍。两次实参**刻意完全相同**——这正是触发条件。CREATE 的 host cost 是 `gas − gas/64`，取决于 gas ledger 而非实参，不带调用序号时两次会折成同一个 UF term 被强制等价（详见 `docs/Gas一致性验证设计.md` §7.1 的判据更正）。第二次内存不再扩展，可见 fee 天然不同，host UF 是唯一被考察的量。

`gas_returndatacopy` 一份 fixture 覆盖两条终止路径，靠 `SMTState.create_initial_state(return_data_size_bytes=...)` 切换：默认 0 时 length=4 必然越界（status 7 `ReturnDataOutOfBounds`），给 0x100 才走到正常复制后的 STOP（status 2）。两格都验 gas——x86 的 gas 前言（`impl_amd64.go:3124`）排在 `popUint256` 与越界 errPoint（`:3148`）**之前**，所以越界退出时 gas 也已经扣过了。

## 真实合约 `ext_contracts/`

7 个主网合约（ENSRegistry、CErc20、Safe、Aave V3 Pool、Uniswap Permit2 / V4 PoolManager、DABEManager）：runtime bytecode → go-hpc-evm IR + amd64 hex。规模最大的一类，来源、编译标志（`solc --optimize`、部分 `--via-ir`）与各合约 loop 统计见 **`ext_contracts/README.md`**。

## 多块 / 控制流样本

`muti_block`、`muti_block_08`、`two_block`、`three_block`、`jumpi_2block{,_ok,_err}`、`mstore_return`、`sstore_load`、`perf_erc20_lite`（json + hex，部分带 `.txt`）。go-hpc-evm 针对特定控制流 / 存储 / 内存特性编译的靶向小程序，驱动程序级等价性检查 与 gas/stage 集成测试；注释自述为 AOT 编译产出，但**未维护再生脚本**，上游变动后需手动重编。

几个有专门语义的：

- `jumpi_2block_err`、`mstore_return`（篡改版）作**负例**——前者验 JUMPI return 不一致被检出，后者是 R13/R14 内存别名 bug 的 ground truth。
- `perf_erc20_lite` 是真实 ERC20（13 block、全符号 calldata），项目的规模 / 性能基准。
- `perf_erc20_lite_bug.hex` 是 `perf_erc20_lite.hex` 的人工位翻转（`sbb`→`sub`），配**原始的** `perf_erc20_lite.json` IR 验 256-bit SUB borrow 传播错误被抓到——**只有 hex、无 json**。

## 手写 IR 小样（纯 json，无 hex）

`add_raw.json`、`add_with_push.json` 是 ADD 基线（x86 hex 内联在测试里，故无 `.hex` 文件）；`static_bounded.json` / `dynamic_bounded.json` / `unbounded.json` 手写，只在 EVM 侧驱动循环检测的三种场景——正常终止，以及两种应抛 `UnsupportedLoopError` 的循环。

## 相关

- `docs/Gas一致性验证设计.md` §9 — gas fixture 清单与每条覆盖点
- `tests/integration/test_gas_consistency_*.py` — 消费 `gas_*` 的测试
- `ext_contracts/README.md` — 真实合约 fixture 的来源与编译


## 块级无界循环验收

`lockstep_{counter,fmp,calldata,return,storage}_loop.{json,hex}` 是 go-hpc-evm 同次生成的成对产物；输入 runtime 字节码、编译器版本、生成器及产物哈希见 `lockstep_loops_manifest.json`。分别覆盖无源级退出条件的计数循环、动态自由内存指针循环、符号 calldata 决定次数后正常返回的循环，辅助块经动态 JUMP 返回的循环，以及持续执行 SLOAD/SSTORE 的数据相关循环。

再生：`poetry run python -m tools.generate_block_loop_fixtures --compiler-root /path/to/go-hpc-evm`。生成器使用 Go overlay，不改编译器工作区；强制 `GOARCH=amd64`，先比对既有 `gas_create` 基线再写入循环样本。Go 可能需要联网及可写缓存，在 Codex 沙箱中按实际需要申请脱沙箱执行。

验收：`poetry run pytest tests/integration/test_block_symbolic_loops.py -q`。没有 EVM 迭代次数上限；局部机器码段的有限推进和完整整程序 H0/H2 证书仍为必需。

### Block environment and host-memory regressions (2026-09-20)

`block_environment.{json,hex}` returns NUMBER/TIMESTAMP/GASLIMIT.
`block_host_memory.{json,hex}` writes nonempty memory, executes STATICCALL and
returns the success word. Both are real go-hpc-evm amd64 outputs. Generator,
runtime bytecodes, compiler revision/source hashes and reproducible overlay
driver are in `docs/reports/block-lockstep-directed-2026-09-18/`. Their FULL-mode
certificate tests include one-sided field, call-site and memory-coordinate
mutations. They are small-program evidence, not CErc20/Safe certificates.
