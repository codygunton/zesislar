"""Definitions context (defs.py): candidate ranking, About/Print parsing, the cache, and a deterministic
selection within the byte budget. Rocq is replaced by FakeRocq, which answers the query files the
resolver writes with recorded `About` / `Print` output of the bank (coqc 8.19)."""
import re
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import defs  # noqa: E402

REJECTED_ABOUT = """DecodeItemReturnFacts.decodeItemRejectedFacts : DecodeItemArgs → Prop

DecodeItemReturnFacts.decodeItemRejectedFacts is not universe polymorphic
Arguments DecodeItemReturnFacts.decodeItemRejectedFacts args
DecodeItemReturnFacts.decodeItemRejectedFacts is transparent
Expands to: Constant ZesuSsz.Contracts.DecodeItemReturnFacts.decodeItemRejectedFacts"""
REJECTED_PRINT = """DecodeItemReturnFacts.decodeItemRejectedFacts =
λ args : DecodeItemArgs,
  RlpDecodeItem.candidateDecodeItem (decodeItemInputBytes args) = RlpDecodeItem.candidateError
     : DecodeItemArgs → Prop"""
LENGTH_ABOUT = """decodeItemInputLength : DecodeItemArgs → Z

decodeItemInputLength is not universe polymorphic
decodeItemInputLength is transparent
Expands to: Constant ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemInputLength"""
LENGTH_PRINT = """decodeItemInputLength =
λ d : DecodeItemArgs,
  let (_, _, decodeItemInputLength, _, _, _, _, _, _) := d in decodeItemInputLength
     : DecodeItemArgs → Z"""
EMPTY_ABOUT = """decodeItemEmptyInputRejected :
∀ args : DecodeItemArgs,
  decodeItemInputBytes args = [] → DecodeItemReturnFacts.decodeItemRejectedFacts args

decodeItemEmptyInputRejected is not universe polymorphic
decodeItemEmptyInputRejected is opaque
Expands to: Constant
ZesuSsz.Compliance.DecodeItemMeaningPorted.PortedSemanticIntroduction.decodeItemEmptyInputRejected"""
TOBV_ABOUT = """Z_to_bv : ∀ n : N, Z → bv n

Z_to_bv is not universe polymorphic
Z_to_bv is transparent
Expands to: Constant stdpp.bitvector.definitions.Z_to_bv"""
ABOUT = {"DecodeItemReturnFacts.decodeItemRejectedFacts": REJECTED_ABOUT, "decodeItemInputLength": LENGTH_ABOUT,
         "decodeItemEmptyInputRejected": EMPTY_ABOUT, "Z_to_bv": TOBV_ABOUT}
PRINT = {"DecodeItemReturnFacts.decodeItemRejectedFacts": REJECTED_PRINT, "decodeItemInputLength": LENGTH_PRINT}
STATEMENT = ("forall (args : DecodeItemArgs), (decodeItemInputLength args = 0) -> (0 < 1) -> "
             "(Z_to_bv 64 (decodeItemInputLength args) = 0%bv) -> (DecodeItemReturnFacts.decodeItemRejectedFacts args)")
HEADER = ["Require Import ZesuSsz.Automation2.All.", "Local Open Scope Z_scope."]
ROOTS = {"ZesuSsz", "ZesuStock"}


class FakeRocq:
    """compile(path, tag) for defs.Resolver: answers About and Print lines from ABOUT / PRINT, with the
    time stamps of rl.scoped; an unknown About prints "not a defined object" as coqc does."""

    def __init__(self, about=ABOUT, printed=PRINT, reject=()):
        self.about, self.printed, self.reject, self.calls = about, printed, set(reject), []

    def __call__(self, path, tag):
        self.calls.append(Path(path).read_text())
        out = []
        for line in Path(path).read_text().split("\n"):
            mark = re.match(r'Goal True\. idtac "(@@D [^"]+)"\. Abort\.', line)
            if mark:
                out.append(mark.group(1))
                continue
            command = re.match(r"(About|Print) (\S+)\.$", line)
            if command:
                if command.group(2) in self.reject:
                    out.append("Error: Syntax error: [smart_global] expected after 'About'.")
                    text = "".join("0.100 %s\n" % l for block in out for l in block.split("\n"))
                    return dict(returncode=1), text
                table = self.about if command.group(1) == "About" else self.printed
                out.append(table.get(command.group(2), "%s not a defined object." % command.group(2)))
        text = "".join("0.100 %s\n" % l for block in out for l in block.split("\n"))
        return dict(returncode=0), text


class RankTests(unittest.TestCase):
    def test_conclusion_head_first_then_sharing_premises_then_the_rest(self):
        names = defs.ranked_names(STATEMENT)
        self.assertEqual(names[0], "DecodeItemReturnFacts.decodeItemRejectedFacts")
        self.assertEqual(names[1:3], ["decodeItemInputLength", "Z_to_bv"])
        self.assertNotIn("args", names)
        self.assertNotIn("forall", names)

    def test_bound_names_at_any_depth(self):
        self.assertEqual(defs.bound_names("forall (a b : Z) (c : nat), exists d : Z, (fun e => e) a = d"),
                         {"a", "b", "c", "d", "e"})

    def test_asked_names_are_code_like(self):
        needs = ["The definition of `DecodeItemReturnFacts.decodeItemRejectedFacts` and the lemma",
                 "decodeItemEmptyInputRejected, or a lemma about Z_to_bv. Also args."]
        self.assertEqual(defs.asked_names(needs, exclude={"args"}),
                         ["DecodeItemReturnFacts.decodeItemRejectedFacts", "decodeItemEmptyInputRejected", "Z_to_bv"])


class ParseTests(unittest.TestCase):
    def test_about_records(self):
        r = defs.parse_about("x", REJECTED_ABOUT)
        self.assertEqual((r["status"], r["kind"], r["opaque"]), ("resolved", "constant", False))
        self.assertEqual(r["full"], "ZesuSsz.Contracts.DecodeItemReturnFacts.decodeItemRejectedFacts")
        e = defs.parse_about("y", EMPTY_ABOUT)
        self.assertTrue(e["opaque"])
        self.assertTrue(e["full"].endswith("PortedSemanticIntroduction.decodeItemEmptyInputRejected"))
        self.assertEqual(defs.parse_about("z", "z not a defined object.")["status"], "unresolved")


class ResolverTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.rocq = FakeRocq()

    def tearDown(self):
        self.tmp.cleanup()

    def resolver(self):
        return defs.Resolver(Path(self.tmp.name) / "defs", HEADER, self.rocq, ROOTS)

    def test_print_only_transparent_project_names_and_cache(self):
        names = defs.ranked_names(STATEMENT)
        records = self.resolver().resolve(names)
        self.assertTrue(records["DecodeItemReturnFacts.decodeItemRejectedFacts"]["project"])
        self.assertFalse(records["Z_to_bv"]["project"])
        self.assertEqual(len(self.rocq.calls), 2)
        self.assertNotIn("Print Z_to_bv.", self.rocq.calls[1])
        self.assertIn("Print decodeItemInputLength.", self.rocq.calls[1])
        self.resolver().resolve(names)
        self.assertEqual(len(self.rocq.calls), 2)

    def test_selection_is_deterministic_ranked_and_within_budget(self):
        names = defs.ranked_names(STATEMENT)
        found = defs.items(self.resolver().resolve(names), names)
        self.assertEqual([n for n, _ in found], ["DecodeItemReturnFacts.decodeItemRejectedFacts", "decodeItemInputLength"])
        self.assertIn("field of record `DecodeItemArgs`", found[1][1])
        full, used = defs.section(found, 10000)
        self.assertEqual(used, [n for n, _ in found])
        self.assertIn("candidateDecodeItem", full)
        first = len((defs.HEAD + found[0][1] + "\n").encode())
        text, used = defs.section(found, first)
        self.assertEqual(used, ["DecodeItemReturnFacts.decodeItemRejectedFacts"])
        self.assertLessEqual(len(text.encode()), first)
        # A budget below the first item skips it and keeps the next one that fits.
        small = len((defs.HEAD + found[1][1] + "\n").encode())
        text, used = defs.section(found, small)
        self.assertEqual(used, ["decodeItemInputLength"])
        self.assertEqual(defs.section(found, small), (text, used))
        self.assertEqual(defs.section(found, 10), ("", []))

    def test_a_name_about_rejects_is_unresolved_and_the_rest_still_answered(self):
        self.rocq = FakeRocq(reject={"Lemma_x"})
        records = self.resolver().resolve(["decodeItemInputLength", "Lemma_x", "Z_to_bv"])
        self.assertEqual([records[n]["status"] for n in ("decodeItemInputLength", "Lemma_x", "Z_to_bv")],
                         ["resolved", "unresolved", "resolved"])
        self.assertEqual(len([c for c in self.rocq.calls if "About" in c]), 2)

    def test_lemma_statement_never_its_proof_and_exclusion(self):
        records = self.resolver().resolve(["decodeItemEmptyInputRejected", "nosuch_name"])
        found = defs.items(records, ["decodeItemEmptyInputRejected", "nosuch_name"], project_only=False)
        self.assertEqual([n for n, _ in found], ["decodeItemEmptyInputRejected"])
        self.assertIn("statement", found[0][1])
        self.assertIn("decodeItemInputBytes args = []", found[0][1])
        self.assertEqual(defs.items(records, ["decodeItemEmptyInputRejected"], project_only=False,
                                    exclude={"decodeItemEmptyInputRejected"}), [])


if __name__ == "__main__":
    unittest.main()
