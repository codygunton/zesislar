"""Similar-lemma index: keys, nearest by Jaccard, prompt bound, later closed goals."""
import json
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import similar  # noqa: E402

PROOF_V = """Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Lemma residual_0040_00000000000000aa :
  forall (x : Z) (H0 : 0 <= x), Z.lt x (Z.add x 1).
Proof.
intros. lia.
Qed.
"""


class KeyTests(unittest.TestCase):
    def test_binders_numerals_and_constructors_are_not_keys(self):
        head, names = similar.keys("forall (x y : Z) (b : bv (Npos (xO xH))) (H0 : Z.le Z0 x), Z.lt (bv_unsigned b) y")
        self.assertEqual(head, "Z.lt")
        self.assertEqual(names, ["Z", "Z.le", "Z.lt", "bv", "bv_unsigned"])

    def test_heads_look_past_lets_premises_and_infix(self):
        self.assertEqual(similar.keys("forall (x : Z), let y := x in (0 <= y -> y < 5)")[0], "<")
        self.assertEqual(similar.keys("(forall (a : Z), (forall (H : a = 1), (@eq Z a 1)))")[0], "eq")


class IndexTests(unittest.TestCase):
    def test_the_tree_index_holds_the_residual_and_bridge_lemmas(self):
        index = similar.build_index()
        sources = {Path(e["source"]).name for e in index["entries"]}
        self.assertIn("DecodeItemBridges.v", sources)
        self.assertEqual(len([s for s in sources if s.startswith("Block800d")]), 15)
        bridges = [e for e in index["entries"] if e["name"].startswith("decodeItem_bridge_")]
        self.assertEqual(len(bridges), 10)
        self.assertTrue(all(e["proof"].endswith("Qed.") for e in index["entries"]))

    def test_nearest_skips_the_query_itself_and_respects_the_byte_bound(self):
        index = similar.build_index()
        target = next(e for e in index["entries"] if e["name"] == "decodeItem_bridge_byte_range")
        found = similar.nearest(index, target["statement"], 3)
        self.assertEqual(len(found), 3)
        self.assertNotIn(target["name"], [e["name"] for _, e in found])
        self.assertEqual([s for s, _ in found], sorted([s for s, _ in found], reverse=True))
        self.assertEqual(found[0][1]["name"], "decodeItem_bridge_byte_mask")
        small = similar.nearest(index, target["statement"], 3, max_bytes=700)
        self.assertLessEqual(sum(len(similar.render(e).encode()) for _, e in small), 700)
        self.assertEqual(similar.nearest(index, target["statement"], 3, max_bytes=10), [])

    def test_closed_goals_of_a_run_join_the_index(self):
        with tempfile.TemporaryDirectory() as root:
            for gid, result in (("0040-1", "PASS"), ("0040-2", "FAIL")):
                d = Path(root) / "goals" / gid
                d.mkdir(parents=True)
                (d / "STATUS.json").write_text(json.dumps({"result": result}))
                (d / "proof.v").write_text(PROOF_V.replace("aa", gid[-1] * 2))
            index = similar.build_index(residuals=Path(root) / "none", runs=[root])
        self.assertEqual([e["name"] for e in index["entries"]], ["residual_0040_0000000000000011"])
        self.assertEqual(index["entries"][0]["head"], "Z.lt")


HIST = ("(forall (x : Z), (forall (H3 : (@ZesuSsz.Automation2.Hist.zesu_hist "
        "(@ZesuSsz.Generated.%s.fp_machineAt%s_ForwardA0N0_Hist x))), (forall (H4 : (@Coq.ZArith.BinInt.Z.le (0)%%Z x)), "
        "(@Coq.ZArith.BinInt.Z.lt (@ZesuSsz.Contracts.%s x) (1)%%Z))))")


class PremiseTests(unittest.TestCase):
    def test_premise_shapes_normalise_names_and_offsets(self):
        statement = HIST % ("Keys", "0170", "keysRead")
        self.assertEqual(similar.premise_shapes(statement), ["le", "zesu_hist(fp_machineAt#_ForwardA0N0_Hist)"])
        self.assertEqual(similar.premise_shapes(statement, "intros. unfold X in H3. lia."),
                         ["zesu_hist(fp_machineAt#_ForwardA0N0_Hist)"])
        self.assertEqual(similar.premise_shapes("forall (x : Z) (H0 : 0 <= x) (H1 : x < 5), x < 6", "lia"), [])

    def test_a_lemma_of_another_region_using_the_history_premise_ranks_first(self):
        hist_proof = "intros. unfold fp_machineAt01ac_ForwardA0N0_Hist in H3. rewrite zesu_hist_eq in H3. lia.\nQed."
        index = dict(entries=[
            similar.entry("other_region", HIST % ("Entries", "01ac", "entriesRead"), hist_proof, "a"),
            similar.entry("same_region_plain", HIST % ("Keys", "0170", "keysWrite"), "intros. lia.\nQed.", "b"),
        ] + [similar.entry("filler_%d" % n, "forall (y : Z) (H0 : 0 <= y), y < y + %d" % n, "intros. lia.\nQed.", "c")
             for n in range(1, 4)])
        found = similar.nearest(index, HIST % ("Keys", "0170", "keysRead"), 2)
        self.assertEqual([e["name"] for _, e in found], ["other_region", "same_region_plain"])

    def test_sibling_runs_cover_every_region_of_the_run_root(self):
        with tempfile.TemporaryDirectory() as root:
            for region in ("keys", "entries"):
                (Path(root) / region).mkdir()
                (Path(root) / region / "OBLIGATIONS.jsonl").write_text("")
                run = Path(root) / region / "resid-r1" / "0170"
                (run / "goals").mkdir(parents=True)
                (run / "MANIFEST.json").write_text("{}")
            (Path(root) / "keys" / "bank-r1" / "x" / "goals").mkdir(parents=True)
            (Path(root) / "keys" / "bank-r1" / "x" / "MANIFEST.json").write_text("{}")
            found = similar.sibling_runs(Path(root) / "keys" / "resid-r1" / "0170")
            self.assertEqual([p.relative_to(Path(root).resolve()).parts[0] for p in found], ["entries", "keys"])
            lone = Path(root) / "lone"
            lone.mkdir()
            self.assertEqual(similar.sibling_runs(lone), [lone.resolve()])


if __name__ == "__main__":
    unittest.main()
