"""Regression checks for the untrusted AST serialization boundary.

These checks complement the Isabelle proofs. They are not proof certificates.
Run from the repository root with:
  python3 -m unittest discover -s tools -p 'test_export_evm_smt.py' -v
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import z3

from export_evm_smt import (
    Artifact, ExportError, MissingConfigurationError, OPERATIONS,
    check_or_write, hol_node, load_production, production_artifacts, reify,
    resolve_python_repo,
)


VARIABLES = {"a": (0, 256), "b": (1, 256), "c": (2, 256)}


def reconstruct(artifact: Artifact, inputs: dict[int, z3.ExprRef]) -> z3.ExprRef:
    """Independent round trip from captured nodes to Z3, without simplify."""
    values: list[z3.ExprRef] = []
    for node in artifact.nodes:
        args = [values[i] for i in node.args]
        binary = {
            "BVAdd": lambda a, b: a + b,
            "BVSub": lambda a, b: a - b,
            "BVMul": lambda a, b: a * b,
            "BVAnd": lambda a, b: a & b,
            "BVOr": lambda a, b: a | b,
            "BVXor": lambda a, b: a ^ b,
            "BVUlt": z3.ULT,
            "BVUle": z3.ULE,
            "BVUgt": z3.UGT,
            "BVUge": z3.UGE,
            "BVSlt": lambda a, b: a < b,
            "BVSle": lambda a, b: a <= b,
            "BVSgt": lambda a, b: a > b,
            "BVSge": lambda a, b: a >= b,
            "BVUDiv": z3.UDiv,
            "BVURem": z3.URem,
            "BVShl": lambda a, b: a << b,
            "BVLshr": z3.LShR,
            "BVAshr": lambda a, b: a >> b,
        }
        if node.op == "BVVar":
            value = inputs[node.params[1]]
        elif node.op == "BVConst":
            value = z3.BitVecVal(node.params[1], node.params[0])
        elif node.op == "BVUF":
            name = {"HolimanUDiv": "holiman_udiv", "HolimanURem": "holiman_udivrem"}[node.params[0]]
            value = z3.Function(name, z3.BitVecSort(256), z3.BitVecSort(256), z3.BitVecSort(256))(*args)
        elif node.op == "BoolConst":
            value = z3.BoolVal(node.params[0])
        elif node.op in binary:
            value = binary[node.op](*args)
        elif node.op == "BVNot":
            value = ~args[0]
        elif node.op == "BVConcat":
            value = z3.Concat(*args)
        elif node.op == "BVExtract":
            value = z3.Extract(*node.params, args[0])
        elif node.op == "BVZeroExt":
            value = z3.ZeroExt(node.params[0], args[0])
        elif node.op == "SMTEq":
            # Python's reflected __eq__ can reverse a numeral equality. Use
            # the raw constructor to test AST identity, not just equivalence.
            value = z3.BoolRef(z3.Z3_mk_eq(args[0].ctx_ref(), args[0].as_ast(), args[1].as_ast()),
                               args[0].ctx)
        elif node.op == "SMTNot":
            value = z3.Not(args[0])
        elif node.op == "SMTDistinct":
            value = z3.Distinct(*args)
        elif node.op == "SMTAnd":
            value = z3.And(*args)
        elif node.op == "SMTOr":
            value = z3.Or(*args)
        elif node.op == "SMTIte":
            value = z3.If(*args)
        else:
            raise AssertionError(f"unexpected reified operator {node.op}")
        values.append(value)
    return values[artifact.root]


class PathConfigurationTests(unittest.TestCase):
    def setUp(self):
        self.addCleanup(patch.stopall)
        patch.dict(os.environ).start()
        os.environ.pop("EVM_PYTHON_REPO", None)
        os.environ.pop("EVM_SMT_CONFIG", None)
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.directory = Path(directory.name)
        self.config = self.directory / "settings" / "paths.json"
        self.config.parent.mkdir()
        patch("export_evm_smt.DEFAULT_CONFIG", self.config).start()

    def write_config(self, value):
        self.config.write_text(json.dumps(value), encoding="utf-8")

    def test_relative_checkout_is_anchored_to_config_not_working_directory(self):
        self.write_config({"python_repo": "../verification checkout"})
        expected = self.directory / "verification checkout"
        self.assertEqual(resolve_python_repo(), expected)
        self.assertEqual(resolve_python_repo(config=self.config), expected)

    def test_checkout_override_precedence_ignores_unused_config(self):
        os.environ["EVM_PYTHON_REPO"] = str(self.directory / "env checkout")
        missing = self.directory / "missing.json"
        self.assertEqual(resolve_python_repo(config=missing), self.directory / "env checkout")
        explicit = self.directory / "cli checkout"
        self.assertEqual(resolve_python_repo(explicit, missing), explicit)

    def test_config_selection_precedence(self):
        self.write_config({"python_repo": "../default checkout"})
        alternative = self.directory / "alternative.json"
        alternative.write_text(json.dumps({"python_repo": "alternative checkout"}), encoding="utf-8")
        os.environ["EVM_SMT_CONFIG"] = str(alternative)
        self.assertEqual(resolve_python_repo(), self.directory / "alternative checkout")
        self.assertEqual(resolve_python_repo(config=self.config), self.directory / "default checkout")

    def test_home_expansion_in_config_and_overrides(self):
        self.write_config({"python_repo": "~/verification checkout"})
        expected = Path.home() / "verification checkout"
        self.assertEqual(resolve_python_repo(), expected)
        os.environ["EVM_PYTHON_REPO"] = "~/verification checkout"
        self.assertEqual(resolve_python_repo(), expected)
        self.assertEqual(resolve_python_repo(Path("~/verification checkout")), expected)

    def test_missing_default_is_distinct_from_explicit_missing_config(self):
        with self.assertRaises(MissingConfigurationError):
            resolve_python_repo()
        with self.assertRaisesRegex(ExportError, "configuration file not found"):
            resolve_python_repo(config=self.config)
        os.environ["EVM_SMT_CONFIG"] = str(self.config)
        with self.assertRaisesRegex(ExportError, "configuration file not found"):
            resolve_python_repo()

    def test_malformed_and_incomplete_config_fail(self):
        for value in ([], {}, {"python_repo": 7}, {"python_repo": "  "}):
            with self.subTest(value=value):
                self.write_config(value)
                with self.assertRaises(ExportError) as caught:
                    resolve_python_repo()
                self.assertNotIsInstance(caught.exception, MissingConfigurationError)
        self.config.write_text("{invalid json}", encoding="utf-8")
        with self.assertRaisesRegex(ExportError, "cannot read configuration"):
            resolve_python_repo()

    def test_empty_environment_overrides_fail(self):
        self.write_config({"python_repo": "../checkout"})
        for name in ("EVM_PYTHON_REPO", "EVM_SMT_CONFIG"):
            with self.subTest(name=name), patch.dict(os.environ, {name: ""}):
                with self.assertRaisesRegex(ExportError, "must not be empty"):
                    resolve_python_repo()

    def test_configured_checkout_without_semantics_fails(self):
        self.write_config({"python_repo": "../missing checkout"})
        with self.assertRaisesRegex(ExportError, "production source not found"):
            load_production(resolve_python_repo())


class FragmentRejectionTests(unittest.TestCase):
    def test_reject_aliased_input_declarations(self):
        a, b = z3.BitVecs("a b", 256)
        with self.assertRaisesRegex(ExportError, "aliased variable"):
            reify(a - b, {"a": (0, 256), "b": (0, 256)})

    def test_fail_closed_on_uninterpreted_function(self):
        a = z3.BitVec("a", 256)
        f = z3.Function("evm_exp", a.sort(), a.sort())
        with self.assertRaisesRegex(ExportError, "uninterpreted function"):
            reify(f(a), VARIABLES)

    def test_reject_undeclared_variable(self):
        with self.assertRaisesRegex(ExportError, "undeclared variable"):
            reify(z3.BitVec("extra", 256), VARIABLES)

    def test_registered_arithmetic_function_preserves_symbol_and_signature(self):
        a, b = z3.BitVecs("a b", 256)
        for name in ("holiman_udiv", "holiman_udivrem"):
            f = z3.Function(name, a.sort(), b.sort(), a.sort())
            expression = f(a,b)
            artifact = reify(expression, VARIABLES)
            self.assertTrue(z3.eq(reconstruct(artifact, {0:a, 1:b}), expression))
            bad = z3.Function(name, a.sort(), a.sort())
            with self.assertRaisesRegex(ExportError, "wrong signature"):
                reify(bad(a), VARIABLES)

    def test_reject_wrong_variable_width(self):
        with self.assertRaisesRegex(ExportError, "wrong width"):
            reify(z3.BitVec("a", 64), VARIABLES)

    def test_reject_non_bv_sorts_and_bool_variables(self):
        for expr in (z3.Int("a"), z3.Array("a", z3.IntSort(), z3.IntSort()), z3.Bool("a")):
            with self.subTest(sort=expr.sort()), self.assertRaises(ExportError):
                reify(expr, VARIABLES)

    def test_reject_unsupported_signed_division_and_binders(self):
        a, b = z3.BitVecs("a b", 256)
        for expr in (a / b, z3.ForAll([a], a == a)):
            with self.subTest(expr=expr), self.assertRaises(ExportError):
                reify(expr, VARIABLES)

    def test_unsigned_division_remainder_and_shifts_roundtrip(self):
        a, b = z3.BitVecs("a b", 256)
        for expr in (z3.UDiv(a, b), z3.URem(a, b), a << b, z3.LShR(a, b), a >> b):
            with self.subTest(expr=expr):
                self.assertTrue(z3.eq(reconstruct(reify(expr, VARIABLES), {0:a, 1:b}), expr))

    def test_binary_distinct_lowering_is_explicit(self):
        a, b, c = z3.BitVecs("a b c", 256)
        artifact = reify(a != b, VARIABLES)
        self.assertTrue(z3.eq(reconstruct(artifact, {0:a, 1:b}), a != b))
        self.assertEqual(hol_node(artifact.nodes[-1], ["a", "b"]), "SMTNot (SMTEq a b)")
        with self.assertRaisesRegex(ExportError, "binary Distinct"):
            reify(z3.Distinct(a,b,c), VARIABLES)

    def test_raw_ast_roundtrip_preserves_sharing_and_extract_bounds(self):
        a = z3.BitVec("a", 256)
        common = z3.Extract(127, 64, a)
        expr = z3.Concat(common + common, common)
        artifact = reify(expr, VARIABLES)
        self.assertTrue(z3.eq(reconstruct(artifact, {0: a}), expr))
        self.assertEqual(sum(node.op == "BVExtract" for node in artifact.nodes), 1)
        extract = next(node for node in artifact.nodes if node.op == "BVExtract")
        self.assertEqual(extract.params, (127, 64))
        names = [f"n{i}" for i in range(len(artifact.nodes))]
        self.assertEqual(hol_node(extract, names), "BVExtract 127 64 n0")

    def test_nary_boolean_encoding_retains_every_operand(self):
        a, b = z3.BitVecs("a b", 256)
        expr = z3.And(a == b, a == 0, b == 1)
        artifact = reify(expr, VARIABLES)
        self.assertTrue(z3.eq(reconstruct(artifact, {0: a, 1: b}), expr))
        node = artifact.nodes[artifact.root]
        rendered = hol_node(node, [f"n{i}" for i in range(len(artifact.nodes))])
        self.assertEqual(rendered.count("SMTAnd"), 2)
        for child in node.args:
            self.assertIn(f"n{child}", rendered)


class ProductionExportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        try:
            cls.repo = resolve_python_repo()
        except MissingConfigurationError as error:
            raise unittest.SkipTest(str(error)) from error
        cls.semantics, _ = load_production(cls.repo)
        cls.files = production_artifacts(cls.repo)

    def test_all_production_raw_dags_roundtrip_without_simplification(self):
        a, b, c = z3.BitVecs("a b c", 256)
        for opcode, (method, arity) in OPERATIONS.items():
            with self.subTest(opcode=opcode):
                expression = getattr(self.semantics, method)(*(a, b, c)[:arity])
                before = expression.sexpr()
                artifact = reify(expression, VARIABLES)
                self.assertTrue(z3.eq(reconstruct(artifact, {0: a, 1: b, 2: c}), expression))
                self.assertEqual(before, expression.sexpr())
                # The raw SMT artifact must carry the same expression, not an
                # optimized surrogate or a hand-written specification.
                query = self.files[f"generated/{opcode.lower()}.smt2"]
                assertion, = z3.parse_smt2_string(query)
                # Z3's SMT-LIB pretty-printer flattens associative additions,
                # so reparsing can change their raw binary association. The
                # printed expression must nevertheless round-trip exactly.
                self.assertEqual(assertion.arg(1).sexpr(), expression.sexpr())

    def test_deterministic_artifacts_and_checked_in_provenance(self):
        self.assertEqual(self.files, production_artifacts(self.repo))
        manifest = json.loads(self.files["generated/manifest.json"])
        for relative, digest in manifest["source_files"].items():
            self.assertEqual(hashlib.sha256((self.repo / relative).read_bytes()).hexdigest(), digest)
            self.assertTrue(relative.endswith(".py"))
            self.assertNotIn("__pycache__", relative)
        for entry in manifest["operations"].values():
            self.assertEqual(hashlib.sha256(self.files[entry["smt_file"]].encode()).hexdigest(),
                             entry["smt_sha256"])

    def test_check_detects_mutated_or_missing_artifact_without_rewriting(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            check_or_write(self.files, output, check=False)
            self.assertEqual(check_or_write(self.files, output, check=True), [])
            changed = output / "generated/add.smt2"
            changed.write_text("corrupted export\n")
            missing = output / "generated/sub.smt2"
            missing.unlink()
            self.assertEqual(set(check_or_write(self.files, output, check=True)),
                             {"generated/add.smt2", "generated/sub.smt2"})
            self.assertEqual(changed.read_text(), "corrupted export\n")
            self.assertFalse(missing.exists())


if __name__ == "__main__":
    unittest.main()
