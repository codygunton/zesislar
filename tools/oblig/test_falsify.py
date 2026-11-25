"""Falsity check: assignment list, record parsing, and real Rocq runs on small statements."""
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import falsify  # noqa: E402

ROOT = HERE.parents[1]
STDPP_HEADER = ("From Coq Require Import ZArith.ZArith.\nRequire Import stdpp.bitvector.definitions.\n"
                "Local Open Scope Z_scope.\n")
SLOT = "(* PROOF-SLOT: replace this line and the Admitted below with the proof script and Qed. *)\nAdmitted.\n"


def find_coqc():
    """coqc from ZESU_COQC, else the first argument of a bank's ARGS.json in the main checkout."""
    if os.environ.get("ZESU_COQC"):
        return os.environ["ZESU_COQC"]
    proc = subprocess.run(["git", "rev-parse", "--git-common-dir"], cwd=ROOT, capture_output=True, text=True)
    main = (ROOT / proc.stdout.strip()).resolve().parent if proc.returncode == 0 else ROOT
    for args in sorted((main / "_build/banks").glob("*/ARGS.json"), reverse=True):
        coqc = json.loads(args.read_text())[0]
        if Path(coqc).exists():
            return coqc
    return None


def goal_file(directory, statement, header=STDPP_HEADER, name="residual_demo_0001"):
    path = Path(directory) / "goal.v"
    path.write_text("%s\nLemma %s :\n  %s.\nProof.\n%s" % (header, name, statement, SLOT))
    return path


class AssignmentTests(unittest.TestCase):
    BINDERS = [dict(name="x", kind="Z"), dict(name="H0", kind="prop"), dict(name="b", kind="bv", width=8),
               dict(name="l", kind="bytes"), dict(name="n", kind="nat"), dict(name="f", kind="bool")]

    def test_literals_cover_decimal_hex_constructors_and_unary(self):
        text = "(Z.le (40)%Z x) /\\ y = Zpos (xO (xI xH)) /\\ z = Zneg (xO xH) /\\ w = 0x1f /\\ n = S (S (S O))"
        self.assertTrue({40, 6, -2, 31, 3} <= falsify.literals(text))

    def test_the_list_is_bounded_deterministic_and_typed(self):
        rows = falsify.assignments(self.BINDERS, "x < 77")
        self.assertEqual(len(rows), falsify.LIMIT)
        self.assertEqual(rows, falsify.assignments(self.BINDERS, "x < 77"))
        values = [r["values"] for r in rows]
        self.assertEqual(len({json.dumps(v, sort_keys=True) for v in values}), len(values))
        self.assertTrue(any(v["x"] == 77 for v in values) and any(v["x"] == 78 for v in values))
        self.assertTrue(all(0 <= v["b"] < 256 and 0 <= v["n"] <= falsify.NAT_MAX for v in values))
        self.assertTrue({v["l"]["bytes"] for v in values} <= {0, 1, 55, 56})
        self.assertTrue(all("H0" not in v for v in values))
        self.assertTrue(any(v["x"] == 0xa0000000 for v in values))

    def test_no_data_binders_give_one_assignment(self):
        self.assertEqual([r["values"] for r in falsify.assignments([dict(name="H", kind="prop")], "1 = 2")], [{}])

    def test_values_print_as_closed_terms(self):
        self.assertEqual(falsify.coq_value(dict(kind="bv", width=8), 300),
                         "(stdpp.bitvector.definitions.Z_to_bv (8)%N (44)%Z)")
        self.assertEqual(falsify.coq_value(dict(kind="Z"), -3), "(-3)%Z")
        self.assertIn("Coq.Lists.List.repeat", falsify.coq_value(dict(kind="bytes"), dict(bytes=56, fill="ff")))

    def test_records_parse(self):
        log = "1.0 @@ZF B x Z\n1.1 @@ZF B b bv 64\n1.2 @@ZF B l list_bv 8\n1.3 @@ZF B m list_bv 16\n1.4 @@ZF E\n"
        binders, ended = falsify.parse_binders(falsify.records(log))
        self.assertTrue(ended)
        self.assertEqual([b["kind"] for b in binders], ["Z", "bv", "bytes", "other"])
        outcomes = falsify.search_outcomes(["try 0", "concl", "miss 0", "try 1", "nodec", "miss 1",
                                            "try 2", "concl", "hit 2"])
        self.assertEqual([outcomes[k]["hit"] for k in range(3)], [False, False, True])
        self.assertTrue(outcomes[1]["nodec"] and outcomes[0]["concl"])

    def test_snapshot_values_map_register_binders(self):
        with tempfile.TemporaryDirectory() as root:
            d = Path(root) / "exec" / "in1"
            d.mkdir(parents=True)
            (d / "STATE-00c4.json").write_text(json.dumps({"regs": {"a0": 7, "s1": "0x10", "pc": 1}}))
            snaps = falsify.snapshots(Path(root) / "exec", "00c4")
        self.assertEqual(snaps[0][0], "in1")
        binders = [dict(name="call3_kept_x10", kind="Z"), dict(name="x9", kind="bv", width=64),
                   dict(name="y", kind="Z")]
        rows = falsify.assignments(binders, "True", snaps)
        self.assertEqual(rows[0]["origin"], "snapshot:in1")
        self.assertEqual(rows[0]["values"], {"call3_kept_x10": 7, "x9": 16, "y": 0})

    def test_leftover_goals_are_read_without_a_preamble(self):
        with tempfile.TemporaryDirectory() as root:
            path = Path(root) / "Goal01.v"
            path.write_text('(* final goal *)\nGoal (@Coq.ZArith.BinInt.Z.le (40)%Z (0)%Z).\n')
            self.assertEqual(falsify.read_goal(path), (None, "(@Coq.ZArith.BinInt.Z.le (40)%Z (0)%Z)", "Goal01"))


class RecordTests(unittest.TestCase):
    """Record binders: the registry's records are projected to fields named by projection path."""

    def test_a_record_line_keeps_its_type(self):
        binders, _ = falsify.parse_binders(["B args record TxAccessListArgs", "B q record M.Q", "E"])
        self.assertEqual(binders, [dict(name="args", kind="record", type="TxAccessListArgs"),
                                   dict(name="q", kind="record", type="M.Q")])

    def test_registered_records_project_to_fields(self):
        registry = falsify.load_records()
        binders, reason = falsify.project_records(
            [dict(name="args", kind="record", type="TxAccessListArgs"), dict(name="H0", kind="prop")], registry)
        self.assertIsNone(reason)
        leaves = falsify.leaves(binders)
        self.assertEqual(len(leaves), 24)
        self.assertEqual(leaves[4], dict(name="txInputPointer", kind="bv", width=64))
        self.assertEqual(leaves[6], dict(name="txInputBytes", kind="bytes"))
        self.assertEqual(binders[0]["ctor"], "@ZesuSsz.Contracts.TxAccessListContract.Build_TxAccessListArgs")
        nested, _ = falsify.project_records([dict(name="a", kind="record", type="KeysToOwnedSliceBlockArgs")],
                                            registry)
        names = [leaf["name"] for leaf in falsify.leaves(nested)]
        self.assertIn("keysBase_toOwnedList_arrayListLength", names)

    def test_other_records_are_unscreened(self):
        registry = dict(Pt=dict(ctor="Build_Pt", fields=[("px", "Z"), ("pk", "Kind")]),
                        Two=dict(ctor="Build_Two", fields=[("x", "Z")]))
        self.assertEqual(falsify.project_records([dict(name="q", kind="record", type="M.Q")], registry)[1],
                         "unscreened: record binder q : M.Q")
        self.assertEqual(falsify.project_records([dict(name="p", kind="record", type="Pt")], registry)[1],
                         "unscreened: record binder p : Pt (field pk : Kind)")
        self.assertEqual(falsify.project_records([dict(name="t", kind="record", type="Two"),
                                                  dict(name="x", kind="Z")], registry)[1],
                         "unscreened: record fields collide with other binders: x")

    def test_a_projected_record_is_built_by_its_constructor(self):
        registry = dict(Pt=dict(ctor="Build_Pt", fields=[("px", "Z"), ("pw", "bv 8")]))
        binders, _ = falsify.project_records([dict(name="p", kind="record", type="Pt")], registry)
        self.assertEqual(falsify.steps(binders, dict(px=3, pw=300)),
                         "zf_step zf_H (Build_Pt (3)%Z (stdpp.bitvector.definitions.Z_to_bv (8)%N (44)%Z)); "
                         "zf_finish zf_H")


@unittest.skipUnless(find_coqc(), "no coqc (set ZESU_COQC or keep a bank in _build/banks)")
class RocqTests(unittest.TestCase):
    """Real compiles: plain coqc arguments, direct route (the guard refuses its live ledger to tests)."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(dir=os.environ.get("TMPDIR"))
        bank = Path(cls.tmp.name) / "bank"
        bank.mkdir()
        (bank / "ARGS.json").write_text(json.dumps([find_coqc()]))
        cls.route = falsify.Route(bank, direct=True)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def run_check(self, statement, name, **kwargs):
        d = Path(self.tmp.name) / name
        d.mkdir()
        return falsify.check(goal_file(d, statement), self.route, **kwargs), d

    def test_a_false_statement_is_refuted_by_a_kernel_checked_lemma(self):
        report, d = self.run_check(
            "forall (x : Z) (b : bv 64) (H0 : 0 <= x) (H1 : bv_unsigned b = x), x < 256", "false")
        self.assertEqual(report["verdict"], "false", report.get("reason"))
        self.assertEqual(report["hit"]["assignment"]["x"], report["hit"]["assignment"]["b"])
        self.assertGreaterEqual(report["hit"]["assignment"]["x"], 256)
        self.assertEqual(report["kernel"]["assumptions"], "Closed under the global context")
        refute = (d / "refute.v").read_text()
        self.assertIn("Lemma zf_refute : ~ zf_stmt.", refute)
        self.assertIn("Qed.", refute)
        self.assertEqual(json.loads((d / "FALSIFY.json").read_text())["verdict"], "false")

    def test_a_proved_residual_lemma_passes(self):
        # The statement of a closed bridge lemma, copied from the residual module.
        module = (ROOT / "ZesuSsz/Residuals/DecodeItemBridges.v").read_text()
        statement = re.search(r"^Lemma decodeItem_bridge_byte_mask :\n(.*?)\.\nProof\.", module, re.S | re.M)[1]
        report, _ = self.run_check(statement.strip(), "true")
        self.assertEqual(report["verdict"], "passed", report.get("reason"))
        self.assertGreater(report["conclusion_tested"], 0)
        self.assertEqual(report["tried"], report["assignments"])

    def test_a_binder_outside_the_supported_types_is_unchecked(self):
        report, d = self.run_check("forall (f : nat -> nat) (x : Z), f 0%nat = f 0%nat", "unchecked")
        self.assertEqual(report["verdict"], "unchecked")
        self.assertIn("f", report["reason"])
        self.assertFalse((d / "search.v").exists())

    def test_a_snapshot_value_refutes(self):
        with tempfile.TemporaryDirectory(dir=os.environ.get("TMPDIR")) as root:
            d = Path(root) / "exec" / "input7"
            d.mkdir(parents=True)
            (d / "STATE-0040.json").write_text(json.dumps({"regs": {"a0": 123457}}))
            report, _ = self.run_check("forall (x10 : Z), x10 <> 123457", "snapshot",
                                       exec_dir=Path(root) / "exec", offset="0040", limit=5)
        self.assertEqual(report["verdict"], "false", report.get("reason"))
        self.assertEqual(report["hit"]["origin"], "snapshot:input7")

    RECORD_HEADER = STDPP_HEADER + ("Record Pt := { px : Z; pw : bv 8 }.\nRecord Q := { qx : Z }.\n"
                                    "Inductive Kind := KA | KB.\nDefinition Bytes := list (bv 8).\n")
    REGISTRY = dict(Pt=dict(ctor="Build_Pt", fields=[("px", "Z"), ("pw", "bv 8")]))

    def run_record(self, statement, name):
        d = Path(self.tmp.name) / name
        d.mkdir()
        return falsify.check(goal_file(d, statement, header=self.RECORD_HEADER), self.route, registry=self.REGISTRY)

    def test_a_registered_record_binder_is_searched_through_its_fields(self):
        report = self.run_record("forall (p : Pt) (b : Bytes), px p < 77", "record")
        self.assertEqual(report["verdict"], "false", report.get("reason"))
        self.assertEqual(report["hit"]["assignment"]["px"], 77)
        self.assertEqual([b["kind"] for b in report["binders"]], ["record", "bytes"])

    def test_an_unregistered_record_binder_is_unscreened(self):
        report = self.run_record("forall (q : Q) (k : Kind), qx q = qx q", "unregistered")
        self.assertEqual(report["verdict"], "unchecked")
        self.assertEqual(report["reason"], "unscreened: record binder q : Q")
        report = self.run_record("forall (k : Kind), k = k", "enum")
        self.assertEqual(report["reason"], "binder type outside Z, nat, N, bv n, list byte, bool: k")


@unittest.skipUnless(os.environ.get("ZESU_FALSIFY_BANK"), "set ZESU_FALSIFY_BANK (and ZESU_FALSIFY_OCAMLPATH)")
class BankTests(unittest.TestCase):
    def test_a_residual_module_lemma_with_its_own_header_passes(self):
        route = falsify.Route(os.environ["ZESU_FALSIFY_BANK"], os.environ.get("ZESU_FALSIFY_OCAMLPATH"),
                              direct=True)
        with tempfile.TemporaryDirectory(dir=os.environ.get("TMPDIR")) as out:
            report = falsify.check(ROOT / "ZesuSsz/Residuals/DecodeItemBridges.v", route, out,
                                   lemma="decodeItem_bridge_byte_range")
        self.assertEqual(report["verdict"], "passed", report.get("reason"))


if __name__ == "__main__":
    unittest.main()
