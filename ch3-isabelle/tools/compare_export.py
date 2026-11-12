"""Check that the packaged validator still produces the expressions certified in smt/.

Re-exports every operation from the validator configured in config/paths.local.json (../ch4-5-validator) and
compares, operation by operation, the SMT expression and the generated Isabelle theory with the checked-in files.
Provenance fields of the manifest (source commit, file hashes, Python and Z3 versions) are reported but not
compared: they identify the checkout the files were exported from, not the expressions.

Usage (from ch3-isabelle/): python tools/compare_export.py      exit status 0 iff every expression matches
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from export_evm_smt import production_artifacts, resolve_python_repo  # noqa: E402

EXPRESSION_KEYS = ("raw_expression_sha256", "smt_sha256", "raw_dag_nodes", "root", "operands", "result_width",
                   "uf_symbols", "hol_root", "method")


def main():
    smt = HERE.parent / "smt"
    fresh = production_artifacts(resolve_python_repo(None, None))
    shipped = json.loads((smt / "generated/manifest.json").read_text())
    exported = json.loads(fresh["generated/manifest.json"])
    bad = []
    for op, entry in sorted(shipped["operations"].items()):
        new = exported["operations"].get(op, {})
        diff = [k for k in EXPRESSION_KEYS if entry.get(k) != new.get(k)]
        if diff or fresh.get(entry["smt_file"]) != (smt / entry["smt_file"]).read_text():
            bad.append(op)
        print(f"{op:<11} {'matches' if op not in bad else 'DIFFERS ' + ', '.join(diff)}")
    theory_same = fresh["Generated_EVM_Arithmetic.thy"] == (smt / "Generated_EVM_Arithmetic.thy").read_text()
    print(f"Generated_EVM_Arithmetic.thy {'matches' if theory_same else 'DIFFERS'}")
    print("provenance of the checked-in files:", json.dumps({k: shipped.get(k) for k in
          ("source_git_commit", "python_version", "z3_version")}))
    return 0 if not bad and theory_same else 1


if __name__ == "__main__":
    sys.exit(main())
