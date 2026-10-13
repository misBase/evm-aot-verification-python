package aot

// Paired EVM IR and amd64 fixtures for block lockstep, including four loops.
// Invoked via tools/generate_block_loop_fixtures.py using a Go overlay.
// The gas_create control must match the checked-in baseline before installation.
// Marshal only AFTER codegen; host IDs follow DefaultHostSpecs catalog order.
// MUST use GOARCH=amd64. The generated AOT machine code is never executed.

import (
	"encoding/hex"
	"encoding/json"
	"os"
	"path/filepath"
	"sort"
	"testing"

	"github.com/bcds/go-hpc-common/types"
	"github.com/bcds/go-hpc-evm/evm/aot/ir"
	"github.com/bcds/go-hpc-evm/evm/common"

	"github.com/stretchr/testify/require"
)

type gasFixture struct {
	name string
	code []byte
}

func push1(v byte) []byte { return []byte{byte(common.PUSH1), v} }

// Deliberately small: the checked-in fixtures are a compiler-version baseline,
// so rebuilding this generator must not casually overwrite all of them.
var gasFixtures = []gasFixture{

	{
		// Self-check: diffing this against the checked-in bytes proves the rebuilt
		// generator hits the same codegen path as the one that made the baseline.
		name: "gas_create",
		code: concat(
			push1(0x20), push1(0x40), push1(0x07),
			[]byte{byte(common.CREATE), byte(common.STOP)},
		),
	},
	{
		// Two CREATEs with *identical* operands on one path. Without a sequence
		// number in the host-gas UF signature both collapse to one Z3 term, forcing
		// cost1 == cost2 while the real costs differ (host.go Create does
		// gas -= gas/64, so the second sees a smaller ledger). Mirrors
		// gas_sload_same_key's role for the access-list case.
		name: "gas_create_same_args",
		code: concat(
			push1(0x20), push1(0x40), push1(0x07),
			[]byte{byte(common.CREATE), byte(common.POP)},
			push1(0x20), push1(0x40), push1(0x07),
			[]byte{byte(common.CREATE), byte(common.POP)},
			[]byte{byte(common.STOP)},
		),
	},
}

func concat(parts ...[]byte) []byte {
	var out []byte
	for _, p := range parts {
		out = append(out, p...)
	}
	return out
}

// newFixtureEngine returns an engine whose hostIndex is populated exactly like
// CompileEVM does, so host op Params match the ones the runtime would assign.
func newFixtureEngine() *engineEVM {
	specs := DefaultHostSpecs()
	e := NewEnginEVM(registerBuiltinHostsInOrder(specs), types.TxVersion10).(*engineEVM)
	e.hostIndex = make(map[string]int64, len(specs))
	for _, spec := range specs {
		if _, ok := e.hosts.Hosts[spec.Name]; !ok {
			continue
		}
		e.hostIndex[spec.Name] = spec.ID
	}
	return e
}

func TestGenGasFixtures(t *testing.T) {
	outDir := os.Getenv("GAS_FIXTURE_OUT")
	if outDir == "" {
		t.Skip("set GAS_FIXTURE_OUT to a fresh directory to regenerate gas fixtures")
	}

	// The Python driver is the single source of the runtime bytecodes.
	var bytecodes map[string]string
	require.NoError(t, json.Unmarshal([]byte(os.Getenv("BLOCK_LOOP_RUNTIMES")), &bytecodes))
	require.NotEmpty(t, bytecodes)
	names := make([]string, 0, len(bytecodes))
	for name := range bytecodes {
		names = append(names, name)
	}
	sort.Strings(names)
	fixtures := append([]gasFixture(nil), gasFixtures...)
	for _, name := range names {
		code, err := hex.DecodeString(bytecodes[name])
		require.NoError(t, err)
		fixtures = append(fixtures, gasFixture{name: name, code: code})
	}

	for _, fx := range fixtures {
		fx := fx
		t.Run(fx.name, func(t *testing.T) {
			e := newFixtureEngine()

			irResult, err := ir.CompileEVM(fx.code)
			require.NoError(t, err, "ir.CompileEVM")

			// Fills host op Params in place — must precede MarshalJSON.
			compiled, err := e.compileEvmFunction(irResult)
			require.NoError(t, err, "compileEvmFunction")

			irJSON, err := json.Marshal(irResult)
			require.NoError(t, err, "MarshalJSON")

			require.NoError(t, os.WriteFile(
				filepath.Join(outDir, fx.name+".json"), irJSON, 0o644))
			require.NoError(t, os.WriteFile(
				filepath.Join(outDir, fx.name+".hex"),
				[]byte(hex.EncodeToString(compiled.codeSegment)), 0o644))

			t.Logf("%s: %d IR bytes, %d code bytes, head=%.8s",
				fx.name, len(irJSON), len(compiled.codeSegment),
				hex.EncodeToString(compiled.codeSegment))
		})
	}
}
