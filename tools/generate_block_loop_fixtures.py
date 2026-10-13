"""Regenerate paired IR/amd64 loop fixtures without editing the compiler checkout.

Run with the project Python toolchain. Go may need access to its module/build
cache; on macOS the amd64 test binary runs under Rosetta but executes no AOT code.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import tempfile

RUNTIMES = {
    "lockstep_storage_loop": "6000355b8015601957600054600101600055600190036003565b5060005460005260206000f3",
    "lockstep_return_loop": "5b60006006565b56",
    "lockstep_counter_loop": "60005b600101600256",
    "lockstep_fmp_loop": "60806040525b604051602001604052600556",
    "lockstep_calldata_loop": "6000355b8015601057600190036003565b60005260206000f3",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler-root", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    compiler = args.compiler_root.resolve()
    generator = root / "tools/fixtures/generate_block_loops_test.go"
    run = lambda *cmd: subprocess.check_output(cmd, cwd=compiler, text=True).strip()
    with tempfile.TemporaryDirectory(prefix="block-loop-fixtures-") as temporary:
        work = Path(temporary)
        overlay = work / "overlay.json"
        # Replace the historical local generator, or virtually add it if absent.
        overlay.write_text(json.dumps({"Replace": {
            str(compiler / "evm/aot/gen_gas_fixtures_test.go"): str(generator)}}))
        env = dict(os.environ, GOARCH="amd64", GAS_FIXTURE_OUT=str(work),
                   BLOCK_LOOP_RUNTIMES=json.dumps(RUNTIMES))
        subprocess.run(["go", "test", "-overlay=" + str(overlay), "./evm/aot/",
                        "-run", "^TestGenGasFixtures$", "-count=1", "-v"],
                       cwd=compiler, env=env, check=True)
        # Compiler path sanity check BEFORE writing any checked-in fixture.
        for suffix in (".hex", ".json"):
            actual = (work / ("gas_create" + suffix)).read_text()
            expected = (root / "tests/data" / ("gas_create" + suffix)).read_text()
            equal = (json.loads(actual) == json.loads(expected) if suffix == ".json"
                     else actual.strip() == expected.strip())
            if not equal:
                raise RuntimeError("gas_create baseline differs: " + suffix)
        records = {}
        for name, bytecode in RUNTIMES.items():
            records[name] = {"evm_runtime_hex": bytecode, "sha256": {}}
            for suffix in (".json", ".hex"):
                data = (work / (name + suffix)).read_bytes()
                if suffix == ".hex" and not data.startswith(b"4d8b7538"):
                    raise RuntimeError("unexpected architecture/prologue")
                (root / "tests/data" / (name + suffix)).write_bytes(data)
                records[name]["sha256"][suffix] = sha256(data).hexdigest()
        manifest = dict(compiler_revision=run("git", "rev-parse", "HEAD"),
            compiler_tracked_diff_sha256=sha256(run("git", "diff", "HEAD", "--").encode()).hexdigest(),
            compiler_go_mod_sha256=sha256((compiler / "go.mod").read_bytes()).hexdigest(),
            compiler_go_sum_sha256=sha256((compiler / "go.sum").read_bytes()).hexdigest(),
            generator_sha256=sha256(generator.read_bytes()).hexdigest(),
            generator_driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
            go_version=run("go", "version"), GOARCH="amd64",
            baseline_check="gas_create hex identical; IR JSON structurally identical",
            fixtures=records)
        (root / "tests/data/lockstep_loops_manifest.json").write_text(
            json.dumps(manifest, indent=2) + "\n")


if __name__ == "__main__":
    main()
