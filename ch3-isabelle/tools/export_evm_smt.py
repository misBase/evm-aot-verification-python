#!/usr/bin/env python3
"""Export production EVM arithmetic Z3 ASTs as data for Isabelle's SMT_BV.

This serializer is a small, deliberately unverified boundary. It never invokes
Z3 simplification or solving. Unknown operators, variables, and sorts fail
closed. The generated HOL theorems certify the imported expression, not Python
or this serializer. Source hashes and raw SMT queries bind the reviewed artifact
to the production constructor and make drift detectable with --check.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys
from typing import Any

import z3


DEFAULT_CONFIG = Path(__file__).resolve().parents[1] / "config" / "paths.local.json"


OPERATIONS = {
    "ADD": ("add_semantics", 2),
    "SUB": ("sub_semantics", 2),
    "EQ": ("eq_semantics", 2),
    "ISZERO": ("iszero_semantics", 1),
    "AND": ("and_semantics", 2),
    "OR": ("or_semantics", 2),
    "XOR": ("xor_semantics", 2),
    "NOT": ("not_semantics", 1),
    "MUL": ("mul_semantics", 2),
    "LT": ("lt_semantics", 2),
    "GT": ("gt_semantics", 2),
    "SLT": ("slt_semantics", 2),
    "SGT": ("sgt_semantics", 2),
    "BYTE": ("byte_semantics", 2),
    "SIGNEXTEND": ("signextend_semantics", 2),
    "SHL": ("shl_semantics", 2),
    "SHR": ("shr_semantics", 2),
    "SAR": ("sar_semantics", 2),
    "MULMOD": ("mulmod_semantics", 3),
    "DIV": ("div_semantics", 2),
    "MOD": ("mod_semantics", 2),
    "SDIV": ("sdiv_semantics", 2),
    "SMOD": ("smod_semantics", 2),
    "ADDMOD": ("addmod_semantics", 3),
}

ARITHMETIC_UFS = {
    "holiman_udiv": "HolimanUDiv",
    "holiman_udivrem": "HolimanURem",
}


class ExportError(ValueError):
    """The input lies outside the supported, reviewed SMT fragment."""


class MissingConfigurationError(ExportError):
    """No production checkout was selected and no default config exists."""


def resolve_python_repo(python_repo: Path | None = None,
                        config: Path | None = None) -> Path:
    """Resolve CLI, environment, or local JSON configuration in that order.

    Paths in JSON are relative to the configuration file. CLI and environment
    paths are relative to the current directory. All paths support ``~``.
    """
    override = python_repo if python_repo is not None else os.environ.get("EVM_PYTHON_REPO")
    if override is not None:
        if not str(override).strip():
            raise ExportError("the production checkout override must not be empty")
        return Path(override).expanduser().resolve()

    selected = config if config is not None else os.environ.get("EVM_SMT_CONFIG")
    if selected is not None and not str(selected).strip():
        raise ExportError("the configuration path must not be empty")
    config_path = Path(selected).expanduser().resolve() if selected is not None else DEFAULT_CONFIG
    try:
        settings = json.loads(config_path.read_text(encoding="utf-8"))
    except FileNotFoundError as error:
        if selected is None:
            raise MissingConfigurationError(
                "no production checkout configured: copy config/paths.example.json "
                "to config/paths.local.json and set python_repo, or use "
                "--python-repo / EVM_PYTHON_REPO"
            ) from error
        raise ExportError(f"configuration file not found: {config_path}") from error
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise ExportError(f"cannot read configuration {config_path}: {error}") from error

    if not isinstance(settings, dict):
        raise ExportError(f"configuration must be a JSON object: {config_path}")
    value = settings.get("python_repo")
    if not isinstance(value, str) or not value.strip():
        raise ExportError(f"configuration needs a nonempty python_repo string: {config_path}")
    repo = Path(value).expanduser()
    if not repo.is_absolute():
        repo = config_path.parent / repo
    return repo.resolve()


@dataclass(frozen=True)
class Node:
    op: str
    sort: tuple[str, int | None]
    args: tuple[int, ...] = ()
    params: tuple[int | bool | str, ...] = ()


@dataclass(frozen=True)
class Artifact:
    nodes: tuple[Node, ...]
    root: int


_BINARY_BV = {
    z3.Z3_OP_BADD: "BVAdd",
    z3.Z3_OP_BSUB: "BVSub",
    z3.Z3_OP_BMUL: "BVMul",
    z3.Z3_OP_BAND: "BVAnd",
    z3.Z3_OP_BOR: "BVOr",
    z3.Z3_OP_BXOR: "BVXor",
}
_COMPARISONS = {
    z3.Z3_OP_ULT: "BVUlt",
    z3.Z3_OP_ULEQ: "BVUle",
    z3.Z3_OP_UGT: "BVUgt",
    z3.Z3_OP_UGEQ: "BVUge",
    z3.Z3_OP_SLT: "BVSlt",
    z3.Z3_OP_SLEQ: "BVSle",
    z3.Z3_OP_SGT: "BVSgt",
    z3.Z3_OP_SGEQ: "BVSge",
}
_WIDE_BV = {
    z3.Z3_OP_BUDIV: "BVUDiv",
    z3.Z3_OP_BUREM: "BVURem",
    z3.Z3_OP_BSHL: "BVShl",
    z3.Z3_OP_BLSHR: "BVLshr",
    z3.Z3_OP_BASHR: "BVAshr",
}


def _sort(expr: z3.ExprRef) -> tuple[str, int | None]:
    if z3.is_bool(expr):
        return ("Bool", None)
    if z3.is_bv(expr) and expr.size() > 0:
        return ("BV", expr.size())
    raise ExportError(f"unsupported sort: {expr.sort()}")


def reify(expr: z3.ExprRef, variables: dict[str, tuple[int, int]]) -> Artifact:
    """Capture a raw AST DAG in deterministic child-before-parent order.

    variables maps allowed Z3 names to (numeric HOL variable, bit width).
    No variable discovered in a formula is implicitly admitted.
    """
    declared_ids: set[int] = set()
    for name, (index, width) in variables.items():
        if index < 0 or width <= 0:
            raise ExportError(f"invalid variable declaration: {name}")
        if index in declared_ids:
            raise ExportError(f"aliased variable declaration: {name}")
        declared_ids.add(index)
    nodes: list[Node] = []
    seen: dict[int, int] = {}

    def visit(term: z3.ExprRef) -> int:
        if term.get_id() in seen:
            return seen[term.get_id()]
        sort = _sort(term)
        if not z3.is_app(term):
            raise ExportError("quantifiers and binders are not supported")
        kind = term.decl().kind()
        children = tuple(term.children())
        params: tuple[int | bool | str, ...] = ()
        if z3.is_bv_value(term):
            op, params = "BVConst", (term.size(), term.as_long())
        elif z3.is_true(term) or z3.is_false(term):
            op, params = "BoolConst", (z3.is_true(term),)
        elif kind == z3.Z3_OP_UNINTERPRETED:
            name = str(term.decl().name())
            if children:
                if name not in ARITHMETIC_UFS:
                    raise ExportError(f"uninterpreted function is not supported: {name}")
                if len(children) != 2 or sort != ("BV", 256) or any(
                    _sort(child) != ("BV", 256) for child in children
                ):
                    raise ExportError(f"wrong signature for arithmetic function: {name}")
                op, params = "BVUF", (ARITHMETIC_UFS[name],)
            else:
                if name not in variables:
                    raise ExportError(f"undeclared variable: {name}")
                index, width = variables[name]
                if sort != ("BV", width):
                    raise ExportError(f"wrong width/sort for variable {name}: {sort}")
                if index < 0 or width <= 0:
                    raise ExportError(f"invalid variable declaration: {name}")
                op, params = "BVVar", (width, index)
        elif kind in _BINARY_BV:
            op = _BINARY_BV[kind]
            if len(children) != 2:
                raise ExportError(f"{op} expects exactly two raw AST children")
        elif kind in _COMPARISONS:
            op = _COMPARISONS[kind]
            if len(children) != 2:
                raise ExportError(f"{op} expects exactly two children")
        elif kind in _WIDE_BV:
            op = _WIDE_BV[kind]
            if len(children) != 2:
                raise ExportError(f"{op} expects exactly two children")
        elif kind == z3.Z3_OP_BNOT:
            op = "BVNot"
        elif kind == z3.Z3_OP_CONCAT:
            op = "BVConcat"
            if len(children) != 2:
                raise ExportError("BVConcat expects exactly two raw AST children")
        elif kind == z3.Z3_OP_EXTRACT:
            op = "BVExtract"
            hi, lo = term.params()
            if not 0 <= lo <= hi < children[0].size():
                raise ExportError("invalid extract bounds")
            params = (hi, lo)
        elif kind == z3.Z3_OP_ZERO_EXT:
            op = "BVZeroExt"
            params = (term.params()[0],)
        elif kind == z3.Z3_OP_EQ:
            op = "SMTEq"
        elif kind == z3.Z3_OP_DISTINCT:
            if len(children) != 2:
                raise ExportError("only binary Distinct is supported")
            op = "SMTDistinct"
        elif kind == z3.Z3_OP_NOT:
            op = "SMTNot"
        elif kind == z3.Z3_OP_AND:
            op = "SMTAnd"
        elif kind == z3.Z3_OP_OR:
            op = "SMTOr"
        elif kind == z3.Z3_OP_ITE:
            op = "SMTIte"
        else:
            raise ExportError(f"unsupported operator {term.decl()} (kind {kind})")
        arities = {"BVNot": 1, "BVExtract": 1, "BVZeroExt": 1,
                   "SMTEq": 2, "SMTNot": 1, "SMTIte": 3}
        if op in arities and len(children) != arities[op]:
            raise ExportError(f"unexpected arity for {op}")
        child_ids = tuple(visit(child) for child in children)
        node_id = len(nodes)
        nodes.append(Node(op, sort, child_ids, params))
        seen[term.get_id()] = node_id
        return node_id

    root = visit(expr)
    return Artifact(tuple(nodes), root)


def hol_node(node: Node, names: list[str]) -> str:
    args = [names[i] for i in node.args]
    if node.op == "BVConst":
        width, value = node.params
        return f"BVConst {width} {value}"
    if node.op == "BVVar":
        width, index = node.params
        return f"BVVar {width} {index}"
    if node.op == "BoolConst":
        return "BoolConst " + ("True" if node.params[0] else "False")
    if node.op in _BINARY_BV.values():
        return f"BVBin {node.op} {args[0]} {args[1]}"
    if node.op in _WIDE_BV.values():
        return f"BVWide {node.op} {args[0]} {args[1]}"
    if node.op in _COMPARISONS.values():
        return f"BVCmp {node.op} {args[0]} {args[1]}"
    if node.op == "SMTDistinct":
        return f"SMTNot (SMTEq {args[0]} {args[1]})"
    if node.op in ("SMTAnd", "SMTOr"):
        # SMT-LIB Boolean and/or are n-ary. Preserve argument order and encode
        # their fold using the binary HOL constructors, including identities.
        if not args:
            return "BoolConst " + ("True" if node.op == "SMTAnd" else "False")
        result = args[0]
        for arg in args[1:]:
            result = f"({node.op} {result} {arg})"
        return result
    params = " ".join(str(p) for p in node.params)
    return " ".join(part for part in (node.op, params, *args) if part)


def render_theory(artifacts: dict[str, Artifact]) -> str:
    lines = [
        "(* Generated by tools/export_evm_smt.py. Do not edit by hand. *)",
        "theory Generated_EVM_Arithmetic",
        "  imports SMT_BV",
        "begin",
        "",
        "text \\<open>Raw production Z3 expressions. Variables 0, 1, and 2 are the",
        "first, second, and third operands. Boolean n-ary nodes use ordered",
        "binary folds. No solver simplification is used during export.\\<close>",
        "",
    ]
    for opcode, artifact in artifacts.items():
        lower = opcode.lower()
        input_ids = sorted({node.params[1] for node in artifact.nodes if node.op == "BVVar"} | {0, 1})
        input_set = ", ".join(f"({index}, 256)" for index in input_ids)
        uf_symbols = sorted({str(node.params[0]) for node in artifact.nodes if node.op == "BVUF"})
        uf_set = ", ".join(uf_symbols)
        names = [f"generated_{lower}_node_{i}" for i in range(len(artifact.nodes))]
        for i, node in enumerate(artifact.nodes):
            lines.extend([
                f'definition {names[i]} :: "smt_expr" where',
                f'  "{names[i]} = {hol_node(node, names)}"',
                "",
            ])
        lines.extend([
            f'definition exported_{lower} :: "smt_expr" where',
            f'  "exported_{lower} = {names[artifact.root]}"',
            "",
            f"lemmas generated_{lower}_defs =",
            f"  exported_{lower}_def",
            *[f"  {name}_def" for name in names],
            "",
            f"lemma exported_{lower}_type:",
            f'  "smt_type exported_{lower} = Some (SBV 256)"',
            f"  by (simp add: generated_{lower}_defs)",
            "",
            f"lemma exported_{lower}_inputs:",
            f'  "smt_inputs exported_{lower} \\<subseteq> {{{input_set}}}"',
            f"  by (simp add: generated_{lower}_defs)",
            "",
            f"lemma exported_{lower}_ufs:",
            f'  "smt_ufs exported_{lower} = {{{uf_set}}}"',
            f"  by (simp add: generated_{lower}_defs)",
            "",
        ])
    lines.extend(["end", ""])
    return "\n".join(lines)


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_dependencies(repo: Path) -> list[Path]:
    """Imported local source closure, including lazy constructor imports."""
    dependencies: set[Path] = set()
    local_packages = {"evm_ir", "common", "state", "utils", "verification", "x86_64"}
    for loaded in tuple(sys.modules.values()):
        filename = getattr(loaded, "__file__", None)
        if filename:
            path = Path(filename).resolve()
            package = getattr(loaded, "__name__", "").split(".")[0]
            if package in local_packages and not path.is_relative_to(repo):
                raise ExportError(f"production dependency imported from another checkout: {path}")
            if path.is_relative_to(repo) and path.suffix == ".py":
                dependencies.add(path)
    return sorted(dependencies)


def load_production(repo: Path) -> tuple[Any, list[Path]]:
    repo = repo.expanduser().resolve()
    source = repo / "evm_ir" / "semantics.py"
    if not source.is_file():
        raise ExportError(f"production source not found: {source}")
    # Do not create or update __pycache__ in the audited, read-only source repo.
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(repo))
    module = importlib.import_module("evm_ir.semantics")
    if Path(module.__file__).resolve() != source:
        raise ExportError("evm_ir.semantics was already imported from another checkout")
    return module.EVMOperationSemantics(), source_dependencies(repo)


def production_artifacts(repo: Path) -> dict[str, str]:
    """Generate all checked-in outputs in memory before writing any file."""
    repo = repo.expanduser().resolve()
    semantics, _ = load_production(repo)
    a, b, c = z3.BitVecs("a b c", 256)
    variables = {"a": (0, 256), "b": (1, 256), "c": (2, 256)}
    artifacts: dict[str, Artifact] = {}
    files: dict[str, str] = {}
    operation_metadata: dict[str, Any] = {}
    for opcode, (method, arity) in OPERATIONS.items():
        operands = (a, b, c)[:arity]
        expression = getattr(semantics, method)(*operands)
        if not z3.is_bv(expression) or expression.size() != 256:
            raise ExportError(f"{opcode} did not return BV256")
        artifact = reify(expression, variables)
        artifacts[opcode] = artifact
        relative = f"generated/{opcode.lower()}.smt2"
        declarations = [f"(declare-fun {str(arg)} () (_ BitVec 256))" for arg in operands]
        uf_symbols = sorted({str(node.params[0]) for node in artifact.nodes if node.op == "BVUF"})
        uf_names = [name for name, symbol in ARITHMETIC_UFS.items() if symbol in uf_symbols]
        declarations.extend(
            f"(declare-fun {name} ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
            for name in uf_names
        )
        query = "\n".join([
            f"(set-logic {'QF_UFBV' if uf_names else 'QF_BV'})", *declarations,
            "(declare-fun result () (_ BitVec 256))",
            f"(assert (= result {expression.sexpr()}))",
            "(check-sat)", "",
        ])
        files[relative] = query
        operation_metadata[opcode] = {
            "method": f"evm_ir.semantics.EVMOperationSemantics.{method}",
            "operands": [{"name": str(arg), "index": i, "width": 256}
                         for i, arg in enumerate(operands)],
            "result_width": 256,
            "raw_dag_nodes": len(artifact.nodes),
            "root": artifact.root,
            "smt_file": relative,
            "smt_sha256": _sha256(query.encode()),
            "raw_expression_sha256": _sha256(expression.sexpr().encode()),
            "hol_root": f"exported_{opcode.lower()}",
            "uf_symbols": uf_names,
        }
    theory = render_theory(artifacts)
    files["Generated_EVM_Arithmetic.thy"] = theory
    dependencies = source_dependencies(repo)
    result = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo,
                            check=True, capture_output=True, text=True)
    manifest = {
        "format_version": 1,
        "scope": "pure EVMOperationSemantics arithmetic results, symbolic BV256 inputs",
        "excluded": ["stack effects", "gas", "exceptions", "CFG", "EXP", "unregistered UF operators"],
        "uf_contract": {
            "holiman_udiv": "unsigned mathematical quotient on the guarded long-division branch",
            "holiman_udivrem": "unsigned mathematical remainder on the guarded long-division branch",
            "status": "explicit HOL interpretation, not axioms asserted by the production solver",
        },
        "source_git_commit": result.stdout.strip(),
        "python_version": ".".join(map(str, sys.version_info[:3])),
        "z3_version": z3.get_version_string(),
        "source_files": {str(path.relative_to(repo)): _sha256(path.read_bytes())
                         for path in dependencies},
        "theory_sha256": _sha256(theory.encode()),
        "operations": operation_metadata,
        "trust_boundary": "Python AST capture and HOL serialization are not formally verified",
        "normalization": "structural lowering only: n-ary Bool and/or to binary folds, binary Distinct to negated equality",
    }
    files["generated/manifest.json"] = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    return files


def check_or_write(files: dict[str, str], output: Path, check: bool) -> list[str]:
    mismatches = []
    for relative, content in files.items():
        path = output / relative
        data = content.encode("utf-8")
        if check:
            if not path.is_file() or path.read_bytes() != data:
                mismatches.append(relative)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
    return mismatches


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--python-repo", type=Path,
                        help="override the configured Python verification checkout")
    parser.add_argument("--config", type=Path,
                        help="path configuration JSON (default: config/paths.local.json)")
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parents[1] / "smt")
    parser.add_argument("--check", action="store_true",
                        help="fail if checked-in artifacts differ, without writing")
    args = parser.parse_args()
    try:
        files = production_artifacts(resolve_python_repo(args.python_repo, args.config))
        mismatches = check_or_write(files, args.output_dir, args.check)
    except (ExportError, ImportError, subprocess.CalledProcessError) as error:
        parser.exit(2, f"export failed: {error}\n")
    if mismatches:
        print("Generated artifacts differ:", *mismatches, sep="\n  ", file=sys.stderr)
        return 1
    print(f"{'Checked' if args.check else 'Exported'} {len(OPERATIONS)} operations, {len(files)} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
