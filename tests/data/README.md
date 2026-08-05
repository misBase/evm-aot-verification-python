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

生成器（`TestGenGasFixtures`）位于 go-hpc-evm 仓库的 `evm/aot` 包内（in-package 测试，依赖同包的 `registerBuiltinHostsInOrder` / `NewEnginEVM` / `engineEVM`）。

**必须 `GOARCH=amd64`**：开发机是 darwin/arm64，直接 `go test` 会写进 ARM64 机器码，而 Python 侧用 x86 反汇编器读它，表现为乱码指令或 `ADD only supports 64-bit operands`，且**不会**有任何 arch 错误提示（这个坑真实发生过，fixture 被静默覆盖成 arm64）。交叉编译安全——生成器只导出 `codeSegment` bytes，从不执行编译产物。

```bash
cd "$GOPATH/src/github.com/bcds/go-hpc-evm"
GOARCH=amd64 go test ./evm/aot/ -run TestGenGasFixtures -v
# 校验：每个 hex 都应以 amd64 preamble 开头
head -c 8 gas_create2.hex   # 期望 4d8b7538（arm64 是 011c40f9）
```

### 加一条新 fixture

1. **操作数取互不相同的可辨识值**。全 0 的退化实例会同时掩盖槽位交换（如 `calcMemSize64` 的 `Back(1)`/`Back(3)` 搞反）与 host-gas UF 的参数顺序错误——旧版 `gas_create` 的 value/offset/size 全 0 且 `size==0`，内存扩展 fee 与 word gas 双双为 0，等于什么都没验。
2. **IR 的 `MarshalJSON` 必须在 `compileEvmFunction` 之后**——后者原地填 host op 的 `Param` 为 host function index；先 marshal 会导出 `Param=0` 的残缺 IR，Python 侧解析出的 host 调用点全部错位。
3. **要验 host-gas 调用序号就得用同一个 key/地址调两次**。`gas_two_sload` 读的是两个**不同** slot，两次调用本来就是不同 UF term，验不到序号机制；`gas_sload_same_key` 才是那条（同 slot 读两次 → 真实 cold 2100 然后 warm 100，见 `docs/Gas一致性验证设计.md` §7.1）。

## 真实合约 `ext_contracts/`

7 个主网合约（ENSRegistry、CErc20、Safe、Aave V3 Pool、Uniswap Permit2 / V4 PoolManager、DABEManager）：runtime bytecode → go-hpc-evm IR + amd64 hex。规模最大的一类，来源、编译标志（`solc --optimize`、部分 `--via-ir`）与各合约 loop 统计见 **`ext_contracts/README.md`**。

## 多块 / 控制流样本

`muti_block`、`muti_block_08`、`two_block`、`three_block`、`jumpi_2block{,_ok,_err}`、`mstore_return`、`sstore_load`、`perf_erc20_lite`（json + hex，部分带 `.txt`）。go-hpc-evm 针对特定控制流 / 存储 / 内存特性编译的靶向小程序，驱动程序级 refinement 与 gas/stage 集成测试；注释自述为 AOT 编译产出，但**未维护再生脚本**，上游变动后需手动重编。

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
