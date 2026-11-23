"""Address literals back to symbol notations (tools/oblig/symbolize.py) and their use by package.py:
a goal whose only address literals are symbols gets a prover task; a kernel refusal or a literal that
is no symbol keeps it class ADDRESS. No Rocq: the kernel check is a fake route."""
import json
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[1] / "tools/block"))
import package  # noqa: E402
import symbolize  # noqa: E402
import residual_loop as rl  # noqa: E402
from test_package import HEADER, SLOT, positive  # noqa: E402

# Addresses are built at run time, so that this file names none (plan A9).
VTABLE = (1 << 31) + 0x1136d8
MEMCPY = (1 << 31) + 0xe06c0
SYMBOLS = [(MEMCPY, "sym_memcpy"), (VTABLE, "sym_alt_fl_alloc_vtable")]


class Route:
    def __init__(self, returncode=0):
        self.returncode, self.compiled = returncode, []

    def compile(self, path, tag):
        self.compiled.append(Path(path).read_text())
        return dict(returncode=self.returncode), "" if self.returncode == 0 else "Error: not convertible"


class SymbolizeTests(unittest.TestCase):
    def test_exact_offset_and_ambiguous_values(self):
        self.assertEqual(symbolize.name_of(VTABLE, SYMBOLS), "sym_alt_fl_alloc_vtable")
        self.assertEqual(symbolize.name_of(VTABLE + 8, SYMBOLS), "(sym_alt_fl_alloc_vtable + 8)")
        self.assertIsNone(symbolize.name_of(VTABLE + 0x2000, SYMBOLS))
        self.assertIsNone(symbolize.name_of(1 << 31, [(1 << 31, "sym_entry")]))
        self.assertIsNone(symbolize.name_of((1 << 32) - 1, [((1 << 32) - 16, "sym_top")]))

    def test_statement_rewrites_only_z_typed_literals(self):
        text = "f (%#x)%%Z = (%d)%%Z /\\ g (%d)%%N = Zpos %s" % (VTABLE, MEMCPY, VTABLE, positive(VTABLE + 16))
        rewritten, found = symbolize.statement(text, SYMBOLS)
        self.assertEqual(rewritten, "f (sym_alt_fl_alloc_vtable)%%Z = (sym_memcpy)%%Z /\\ g (%d)%%N = "
                         "((sym_alt_fl_alloc_vtable + 16))" % VTABLE)
        self.assertEqual([name for _, name in found],
                         ["sym_alt_fl_alloc_vtable", "sym_memcpy", "(sym_alt_fl_alloc_vtable + 16)"])

    def test_display_and_header(self):
        self.assertEqual(symbolize.display("w = %d H" % VTABLE, SYMBOLS), "w = sym_alt_fl_alloc_vtable H")
        header = ["Require Import A.", "From Coq Require Import ZArith.", "Local Open Scope Z_scope."]
        self.assertEqual(symbolize.with_require(header),
                         header[:2] + [symbolize.REQUIRE] + header[2:])

    def test_table_reads_the_generated_module(self):
        rows = dict((name, value) for value, name in symbolize.table())
        self.assertIn("sym_alt_fl_alloc_vtable", rows)
        self.assertEqual(rows["sym_alt_fl_alloc_vtable"], VTABLE)


class PackageSymbolTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.saved = symbolize.table
        symbolize.table = lambda path=None: SYMBOLS

    def tearDown(self):
        symbolize.table = self.saved
        self.tmp.cleanup()

    def run_with(self, statement, readable, route):
        run = Path(self.tmp.name) / "run"
        name = "residual_keys_00d8_%016x" % 1
        d = run / "goals" / "00d8-1"
        d.mkdir(parents=True)
        (d / "goal.v").write_text("%s\n\nLemma %s :\n  %s.\nProof.\n%s" % (HEADER, name, statement, SLOT))
        goal = dict(id="00d8-1", name=name, statement=statement, reparse="exact", readable=readable, counts={})
        manifest = dict(block="00d8", bank="/nonexistent", goals=[goal])
        (run / "MANIFEST.json").write_text(json.dumps(manifest))
        record = package.package_goal(run, manifest, goal, "keys", "haiku-low", 12000, None, None,
                                      symbol_route=route)
        return run, d, record

    def test_symbol_literal_goal_gets_a_task(self):
        route = Route()
        statement = "forall (w : Z), w = (%#x)%%Z -> w > 0" % VTABLE
        run, d, record = self.run_with(statement, "w : Z\nH : w = %d\n====\nw > 0" % VTABLE, route)
        self.assertIsNone(record["class"])
        self.assertEqual(record["next"], "prover")
        self.assertEqual(record["symbols"], [dict(literal="%#x" % VTABLE, notation="sym_alt_fl_alloc_vtable")])
        goal_v = (d / "goal.v").read_text()
        self.assertIn(symbolize.REQUIRE, goal_v)
        self.assertIn("w = (sym_alt_fl_alloc_vtable)%Z", goal_v)
        self.assertEqual(package.address_matches(goal_v), [])
        self.assertIn("%#x" % VTABLE, (d / "goal-literal.v").read_text())
        self.assertIn("(%s) =\n  (%s)" % (statement, statement.replace("%#x" % VTABLE, "sym_alt_fl_alloc_vtable")),
                      route.compiled[0])
        task = Path(record["task"]).read_text()
        self.assertIn("H : w = sym_alt_fl_alloc_vtable", task)
        self.assertEqual(package.address_matches(task), [])
        # The residual loop's proof.v and the rendered module keep the notation.
        self.assertTrue(goal_v.startswith(rl.goal_head(goal_v)))
        self.assertIn(symbolize.REQUIRE, rl.symbolized_goal_text(d, HEADER.split("\n"), "n", statement))

    def test_kernel_refusal_keeps_the_address_class(self):
        statement = "forall (w : Z), w = (%#x)%%Z -> w > 0" % VTABLE
        _, d, record = self.run_with(statement, "", Route(returncode=1))
        self.assertEqual((record["class"], record["next"]), ("ADDRESS", "decision"))
        self.assertNotIn(symbolize.REQUIRE, (d / "goal.v").read_text())

    def test_literal_that_is_no_symbol_stays_address(self):
        statement = "forall (w : Z), w = (%#x)%%Z -> w = (%#x)%%Z" % (VTABLE, VTABLE + 0x10000)
        _, d, record = self.run_with(statement, "", Route())
        self.assertEqual(record["class"], "ADDRESS")
        self.assertEqual([row["hex"] for row in record["addresses"] if row["source"] == "literal"],
                         ["%#x" % (VTABLE + 0x10000)])
        self.assertIn("sym_alt_fl_alloc_vtable", (d / "goal.v").read_text())


if __name__ == "__main__":
    unittest.main()
