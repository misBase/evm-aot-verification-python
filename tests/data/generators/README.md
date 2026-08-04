# gas fixture 生成器

`tests/data/gas_*.json` / `gas_*.hex` 不是手写的，而是由 go-hpc-evm 的真实编译链路
产出：同一段 EVM 字节码同时导出 **IR JSON**（Python 侧 `load_ir_from_json` 的输入）
与 **amd64 机器码 hex**（Python 侧 Capstone 反汇编的输入）。两者必须来自同一次编译，
否则验证的就不是同一个程序。

生成器源码 `gas_fixture_gen_test.go` 存在这里，是因为它**曾经只存在于 Go 工作树里、
从未提交，结果丢失**——fixture 随之变得不可复现。请不要把它挪回去。

## 绑定的上游版本

| | |
| --- | --- |
| 仓库 | `$GOPATH/src/github.com/bcds/go-hpc-evm` |
| commit | **`b3ddbdb`**（`fix(aot): correct SIGNEXTEND jump targets and add fuzz test`） |

fixture 的可信度绑定在这个 SHA 上：机器码是该版本 codegen 的产物，IR 的 `static_gas`
/ host `Param` 索引也是。上游变动后重新生成时，请一并更新这里的 SHA。

## 用法

```bash
# 1. 拷到 go-hpc-evm 的 aot 包内（它是 package aot 的 in-package 测试，
#    要用到同包的 registerBuiltinHostsInOrder / NewEnginEVM / engineEVM）
cp tests/data/generators/gas_fixture_gen_test.go \
   "$GOPATH/src/github.com/bcds/go-hpc-evm/evm/aot/"

# 2. 生成（必须 GOARCH=amd64，见下）
cd "$GOPATH/src/github.com/bcds/go-hpc-evm"
GOARCH=amd64 go test ./evm/aot/ -run TestGenGasFixtures -v

# 3. 校验：每个新 hex 都应以 amd64 preamble 开头
head -c 8 "$OLDPWD/tests/data/gas_create2.hex"   # 期望 4d8b7538
```

输出目录默认由生成器相对推导（`<go-hpc-evm>/evm/aot/../../../../../../evm-aot-verification-python/tests/data`），
可用环境变量覆盖：

```bash
GAS_FIXTURE_OUT=/path/to/evm-aot-verification-python/tests/data \
  GOARCH=amd64 go test ./evm/aot/ -run TestGenGasFixtures -v
```

## ⚠️ 必须 `GOARCH=amd64`

开发机是 darwin/arm64。Go 按文件名后缀（`impl_amd64.go` / `impl_arm64.go`）隐式选择
后端，直接 `go test` 会生成 **ARM64** 机器码写进 `.hex`，而 Python 侧用 x86 反汇编器
读它——表现为乱码指令或 `ADD only supports 64-bit operands` 之类的报错，且**不会**有
任何提示说 fixture 的 arch 错了。这个坑真实发生过（fixture 被静默覆盖成 arm64）。

防线有两道：生成器开头断言 `runtime.GOARCH == "amd64"`；写文件前校验机器码以 amd64
preamble `4d8b7538`（`mov r14,[r13+0x38]`）开头，arm64 是 `011c40f9`。

交叉编译是安全的：生成器只把 `codeSegment` 导出成 bytes，从不执行编译出来的机器码
（amd64 测试二进制本身经 Rosetta 运行）。

## 加一条新 fixture

在 `gasFixtures()` 里追加一项即可，注意两点：

1. **操作数取互不相同的可辨识值**。全 0 的退化实例会同时掩盖槽位交换（例如
   `calcMemSize64` 的 `Back(1)`/`Back(3)` 搞反）与 host-gas UF 的参数顺序错误——
   旧版 `gas_create` 的 value/offset/size 全是 0 且 `size==0`，内存扩展 fee 与 word
   gas 双双为 0，等于什么都没验。
2. **IR 的 `MarshalJSON` 必须在 `compileEvmFunction` 之后**（生成器已保证）。后者会
   原地把 host op 的 `Param` 填成 host function index；先 marshal 会导出 `Param=0`
   的残缺 IR，Python 侧解析出的 host 调用点全部错位。

字节码常量直接用 `common.PUSH1` 等（`evm/common/opcodes.go`）。

## 相关

- `docs/Gas一致性验证设计.md` §9 — fixture 清单与每条的覆盖点
- `tests/integration/test_gas_consistency_*.py` — 消费这些 fixture 的测试
