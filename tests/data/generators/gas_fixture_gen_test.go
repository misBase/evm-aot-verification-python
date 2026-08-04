package aot

// gas_fixture_gen_test.go —— 为 Python 侧 gas 一致性验证生成 fixture。
//
// 从 EVM 字节码编译出「真实 IR JSON + 真实 amd64 机器码 hex」，写进
// evm-aot-verification-python 的 tests/data/。这是 gas 验证唯一的纯净 fixture 来源：
// single_ins 的 core 剥掉了 gas 前言，真实大合约又掺着未建模的 host op。
//
// **本文件的家在 Python 仓库**（tests/data/generators/），使用时拷贝到
//     $GOPATH/src/github.com/bcds/go-hpc-evm/evm/aot/
// 再运行。上一版只存在于 Go 工作树里、从未提交，已经丢失过一次，fixture 因此无法复现。
// 用法与前置条件见同目录 README.md。
//
// 运行（**必须交叉编译到 amd64**）：
//     cd $GOPATH/src/github.com/bcds/go-hpc-evm
//     GOARCH=amd64 go test ./evm/aot/ -run TestGenGasFixtures -v
//
// 这台开发机是 darwin/arm64，Go 按文件名后缀（impl_amd64.go / impl_arm64.go）隐式选
// arch：直接 `go test` 会生成 **ARM64** 机器码，Python 侧 x86 反汇编器只会得到乱码或
// 报错。TestGenGasFixtures 开头对 runtime.GOARCH 做了硬断言，宁可 fail 也不写出错 arch
// 的 fixture（曾经静默覆盖过一次）。生成器只导出 codeSegment 的 bytes、从不执行它，
// 所以交叉编译是安全的（amd64 测试二进制本身经 Rosetta 运行）。

import (
	"encoding/hex"
	"encoding/json"
	"os"
	"path/filepath"
	"runtime"
	"testing"

	"github.com/bcds/go-hpc-common/types"
	"github.com/bcds/go-hpc-evm/evm/aot/ir"
	"github.com/bcds/go-hpc-evm/evm/common"

	"github.com/stretchr/testify/require"
)

// 输出目录：从工作目录逐级向上找到 Python 仓库的 tests/data，可用 GAS_FIXTURE_OUT
// 覆盖。不硬编码任何个人绝对路径，也不写死"向上几层"——两个仓库的相对深度取决于
// GOPATH 布局，数层数很容易差一级（第一版就差了一级）。
const pythonRepoFixtureSubPath = "evm-aot-verification-python/tests/data"

func gasFixtureOutDir(t *testing.T) string {
	t.Helper()
	if out := os.Getenv("GAS_FIXTURE_OUT"); out != "" {
		return out
	}
	dir, err := os.Getwd() // = <go-hpc-evm>/evm/aot
	require.NoError(t, err)
	for i := 0; i < 12; i++ {
		candidate := filepath.Join(dir, pythonRepoFixtureSubPath)
		if info, err := os.Stat(candidate); err == nil && info.IsDir() {
			return candidate
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			break
		}
		dir = parent
	}
	t.Fatalf("没能从 %s 向上找到 %s，请用 GAS_FIXTURE_OUT 显式指定输出目录",
		dir, pythonRepoFixtureSubPath)
	return ""
}

func op(c common.OpCode) byte { return byte(c) }

// gasFixture 是一条 fixture 的定义：EVM 字节码 + 输出文件名。
type gasFixture struct {
	name string
	code []byte
	// note 只用于日志，说明这条 fixture 存在的理由。
	note string
}

// 操作数取**互不相同的可辨识值**：全 0 的退化实例会同时掩盖槽位交换（例如把
// calcMemSize64 的 Back(1)/Back(3) 搞反）和 host-gas UF 的参数顺序错误——旧的
// gas_create（value/offset/size 全 0、size==0）就是因此没有验证价值。
func gasFixtures() []gasFixture {
	return []gasFixture{
		{
			name: "gas_create",
			// size=0x20, offset=0x40, value=0x07（push 顺序 = 栈底→栈顶；
			// CREATE 依次弹出 value/offset/size）
			code: []byte{
				op(common.PUSH1), 0x20,
				op(common.PUSH1), 0x40,
				op(common.PUSH1), 0x07,
				op(common.CREATE),
				op(common.STOP),
			},
			note: "内存扩展 fee + InitCodeWordGas；三个槽位互不相同",
		},
		{
			name: "gas_create_returngas",
			// 同上，但 CREATE 之后还有静态 gas 指令 ⇒ returnGas = Blk.StaticGas -
			// Immediate ≠ 0，才验得到 dealWithAddGas/SubGas 窗口内的可见 fee。
			code: []byte{
				op(common.PUSH1), 0x20,
				op(common.PUSH1), 0x40,
				op(common.PUSH1), 0x07,
				op(common.CREATE),
				op(common.POP),
				op(common.PUSH1), 0x01,
				op(common.PUSH1), 0x02,
				op(common.ADD),
				op(common.POP),
				op(common.STOP),
			},
			note: "returnGas != 0：可见 fee 落在 add/sub 窗口内的端到端证据",
		},
		{
			name: "gas_create2",
			// salt=0x7b, size=0x20, offset=0x40, value=0x07
			code: []byte{
				op(common.PUSH1), 0x7b,
				op(common.PUSH1), 0x20,
				op(common.PUSH1), 0x40,
				op(common.PUSH1), 0x07,
				op(common.CREATE2),
				op(common.STOP),
			},
			note: "CREATE2_WORD_GAS(=InitCodeWordGas+Sha3WordGas) 与 CREATE 的常量区分",
		},
		{
			name: "gas_extcodecopy",
			// size=0x04, offset=0x07, destOffset=0x20, addr=0x01
			// 四个值互不相同 ⇒ calcMemSize64(Back(1),Back(3)) 选错槽位会被抓到。
			code: []byte{
				op(common.PUSH1), 0x04,
				op(common.PUSH1), 0x07,
				op(common.PUSH1), 0x20,
				op(common.PUSH1), 0x01,
				op(common.EXTCODECOPY),
				op(common.STOP),
			},
			note: "calcMemSize64(Back(1),Back(3)) 槽位 + CopyGas(3)",
		},

		// --- 符号操作数：让 memoryGasCost 的 cap 支、makeSafeMul/SafeAdd 的溢出支、
		//     动态 OOG 在**端到端**层面真实可达（常量 fixture 只能证明正常路径）。
		{
			name: "gas_create_sym",
			code: []byte{
				op(common.PUSH1), 0x20, op(common.CALLDATALOAD), // size   = calldata[0x20:0x40]
				op(common.PUSH1), 0x00, op(common.CALLDATALOAD), // offset = calldata[0x00:0x20]
				op(common.PUSH1), 0x07, // value
				op(common.CREATE),
				op(common.STOP),
			},
			note: "符号 size/offset：cap / SafeMul / SafeAdd / 动态 OOG 分支可达",
		},
		{
			name: "gas_extcodecopy_sym",
			code: []byte{
				op(common.PUSH1), 0x00, op(common.CALLDATALOAD), // size
				op(common.PUSH1), 0x07, // offset
				op(common.PUSH1), 0x20, op(common.CALLDATALOAD), // destOffset
				op(common.PUSH1), 0x01, // addr
				op(common.EXTCODECOPY),
				op(common.STOP),
			},
			note: "符号 size/destOffset：copy 系的同类边界分支",
		},
	}
}

// TestGenGasFixtures 生成 <name>.json（IR）与 <name>.hex（amd64 机器码）。
func TestGenGasFixtures(t *testing.T) {
	require.Equalf(t, "amd64", runtime.GOARCH,
		"fixture 必须是 x86-64 机器码，当前 GOARCH=%s。请用 "+
			"`GOARCH=amd64 go test ./evm/aot/ -run TestGenGasFixtures -v` 交叉编译；"+
			"否则会写出 arm64 codegen 并静默破坏 Python 侧的 x86 反汇编",
		runtime.GOARCH)

	outDir := gasFixtureOutDir(t)
	require.DirExistsf(t, outDir, "输出目录不存在：%s（用 GAS_FIXTURE_OUT 指定）", outDir)

	for _, fx := range gasFixtures() {
		fx := fx
		t.Run(fx.name, func(t *testing.T) {
			irJSON, codeHex := compileGasFixture(t, fx.code)

			// amd64 的 compilePreamble 固定以 `mov r14,[r13+0x38]` 开头（4d8b7538），
			// arm64 是 011c40f9。这是 arch 写错时最后一道防线。
			require.Truef(t, len(codeHex) >= 8 && codeHex[:8] == "4d8b7538",
				"%s: 机器码不像 amd64 preamble（前 8 字符 %q），拒绝写出",
				fx.name, codeHex[:min(8, len(codeHex))])

			jsonPath := filepath.Join(outDir, fx.name+".json")
			hexPath := filepath.Join(outDir, fx.name+".hex")
			require.NoError(t, os.WriteFile(jsonPath, irJSON, 0o644))
			require.NoError(t, os.WriteFile(hexPath, []byte(codeHex+"\n"), 0o644))
			t.Logf("wrote %s (%d bytes code) — %s", fx.name, len(codeHex)/2, fx.note)
		})
	}
}

// compileGasFixture 走真实编译链路：IR 编译 → 机器码编译 → 导出。
//
// 关键顺序：**IR 的 MarshalJSON 必须在 compileEvmFunction 之后**——后者会原地把
// host op 的 Param 填成 host function index，先 marshal 会导出 Param=0 的残缺 IR，
// Python 侧解析出来的 host 调用点全部错位。
func compileGasFixture(t *testing.T, code []byte) ([]byte, string) {
	t.Helper()

	hosts := registerBuiltinHostsInOrder(DefaultHostSpecs())
	engine, ok := NewEnginEVM(hosts, types.TxVersion10).(*engineEVM)
	require.True(t, ok, "NewEnginEVM 应返回 *engineEVM")

	// 手动建立 host name → index 映射。完整的 CompileEVM 会顺带做这件事，但它同时
	// 编译所有 host function 且不返回 IR；这里只取 EVM 主体。缺这步时含 host op 的
	// 字节码会在 setHostParam 处报 `predefined host "xxx" is not registered`。
	for _, spec := range DefaultHostSpecs() {
		engine.hostIndex[spec.Name] = spec.ID
	}

	irResult, err := ir.CompileEVM(code)
	require.NoError(t, err, "ir.CompileEVM 失败")

	fn, err := engine.compileEvmFunction(irResult)
	require.NoError(t, err, "compileEvmFunction 失败")

	irJSON, err := json.MarshalIndent(irResult, "", "  ")
	require.NoError(t, err, "IR marshal 失败")

	return irJSON, hex.EncodeToString(fn.codeSegment)
}
