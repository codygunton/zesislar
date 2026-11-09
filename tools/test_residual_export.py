"""Tests for the residual goal export (tools/residuals)."""

import contextlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "residuals"))
import export_block  # noqa: E402
import guarded  # noqa: E402
import residual_package as pkg  # noqa: E402

PREFIX = "Require Import ZesuSsz.Automation2.All.\nLocal Open Scope Z_scope.\n"
CALLER = PREFIX + "\nLemma DesignedBoundary_x : True.\nProof.\n  zesu_block2.\nQed.\n"


def hyp(name, prop, n, vars_, typ):
    return ["CENSUS RES-HYP %s d=0 prop=%d n=%d v= %s ::" % (name, prop, n, " ".join(vars_)),
            "CENSUS RES-TYPE %s" % typ]


def goal(concl_vars, concl, hyps):
    lines = []
    for h in hyps:
        lines += hyp(*h)
    return lines + ["CENSUS RES-CONCL n=3 v= %s ::" % " ".join(concl_vars), "CENSUS RES-TEXT %s" % concl]


X = ("x", 0, 1, [], "Z")
Y = ("y", 0, 1, [], "Z")
HX = ("H1", 1, 5, ["x"], "Z.le 0 x")
HY = ("H2", 1, 5, ["y"], "Z.le 0 y")
BIG = ("H3", 1, 9000, ["x"], "big x")


def census_log():
    """A residual log in census_solver order (E before FAIL-BEGIN): one solved try, one spatial goal, one open pure goal, and
    three failure dumps (one nested inside another dump layer, one duplicate)."""
    body = ["CENSUS BLOCK-BEGIN"]
    body += ["CENSUS B tactics.bv_solve h=2 p=1 g=3 c=4 goal=<large>",
             "CENSUS E tactics.bv_solve fail",
             "CENSUS FAIL-BEGIN tactics.bv_solve"] + goal(["x"], "Z.le 0 (x + 1)", [X, HX, BIG]) + [
             "CENSUS FAIL-END"]
    # Nested: Lia.lia inside an open bv_solve call is skipped; the outer call dumps its own goal.
    body += ["CENSUS B tactics.bv_solve h=2 p=1 g=3 c=4 goal=<large>",
             "CENSUS B Lia.lia h=2 p=1 g=3 c=4 goal=<large>",
             "CENSUS E Lia.lia fail",
             "CENSUS FAIL-BEGIN Lia.lia"] + goal(["y"], "nested", [Y, HY]) + [
             "CENSUS FAIL-END", "CENSUS E tactics.bv_solve ok"]
    # A duplicate of the first dump merges into it.
    body += ["CENSUS B Lia.lia h=2 p=1 g=3 c=4 goal=<large>",
             "CENSUS E Lia.lia fail",
             "CENSUS FAIL-BEGIN Lia.lia"] + goal(["x"], "Z.le 0 (x + 1)", [X, HX, BIG]) + [
             "CENSUS FAIL-END"]
    body += ["CENSUS STAGE prove-done", "CENSUS RES-TRY solved", "CENSUS RES-TRY open reason=spatial",
             "CENSUS RES-TRY open reason=failed", "CENSUS STAGE try-done"]
    for p in ("readable", "robust"):
        body += ["CENSUS RES-BEGIN pass=%s kind=spatial" % p,
                 "CENSUS RES-CONCL n=9 v= ::", "CENSUS RES-TEXT envs_entails Δ\tP", "CENSUS RES-END",
                 "CENSUS RES-BEGIN pass=%s kind=pure" % p] + goal(["y"], "Z.le 0 (y * 2)", [X, Y, HX, HY]) + [
                 "CENSUS RES-END"]
    body += ["CENSUS STAGE dump-done"]
    return "".join("%.3f %s\n" % (i * 0.01, line) for i, line in enumerate(body))


class Packaging(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)
        self.log = self.dir / "census.log"
        self.log.write_text(census_log())

    def tearDown(self):
        self.tmp.cleanup()

    def test_candidates_are_open_pure_goals_and_outermost_failures(self):
        tries, spatial, uniq = pkg.candidates(self.log, "6960", 1500, {"args"})
        self.assertEqual(tries, ["solved", "spatial", "failed"])
        self.assertEqual([(r["kind"], r["reason"]) for r in spatial], [("spatial", "spatial")])
        self.assertEqual([c["id"] for c in uniq], ["6960-1", "6960-2"])
        self.assertEqual(uniq[0]["source"], "left open at the end (failed)")
        self.assertEqual(uniq[1]["source"], "failed tactics.bv_solve call during the proof")
        self.assertEqual(uniq[1]["copies"], 2)

    def test_selection_keeps_linked_facts_and_drops_big_ones(self):
        _, _, uniq = pkg.candidates(self.log, "6960", 1500, {"args"})
        names = lambda c: [c["dump"]["hyps"][i]["id"] for i in c["keep"]]
        self.assertEqual(names(uniq[0]), ["y", "H2"])
        self.assertEqual(names(uniq[1]), ["x", "H1"])

    def test_same_log_gives_same_ids_and_digests(self):
        a = pkg.candidates(self.log, "6960", 1500, {"args"})[2]
        b = pkg.candidates(self.log, "6960", 1500, {"args"})[2]
        self.assertEqual([(c["id"], c["sha"]) for c in a], [(c["id"], c["sha"]) for c in b])

    def test_pass_mismatch_is_an_error(self):
        self.log.write_text("0.0 CENSUS RES-TRY open reason=failed\n")
        with self.assertRaises(ValueError):
            pkg.parse_residual(self.log)

    def test_goal_dir_layout_and_unknown_goals_stay(self):
        _, spatial, uniq = pkg.candidates(self.log, "6960", 1500, {"args"})
        out = self.dir / "out"
        out.mkdir()
        pkg.write_spatial(out, spatial)
        args = ["/opt/coqc", "-Q", "/bank/ZesuSsz", "ZesuSsz"]
        for c, status in zip(uniq, ("pass", "fail")):
            stage = self.dir / "stage" / c["id"]
            pkg.stage_files(c, "6960", PREFIX, stage)
            res = dict(control=dict(status=status, seconds=1.5), goal=dict(status="pass", seconds=0.5))
            pkg.write_goal_dir(out, c, "6960", stage, res, args, "/repo/tools/resource_guard.sh", "/opt:/usr/bin", 1500,
                               "/out/_findlib")
        for gid in ("6960-1", "6960-2"):
            self.assertEqual(sorted(p.name for p in (out / gid).iterdir()),
                             ["CONTROL", "FACTS.md", "check.sh", "goal.v", "goal_full.v"])
        goal_v = (out / "6960-1" / "goal.v").read_text()
        self.assertTrue(goal_v.startswith(PREFIX))
        self.assertIn(pkg.SLOT, goal_v)
        self.assertTrue(goal_v.rstrip().endswith("Admitted."))
        self.assertIn("forall (y : Z) (H2 : Z.le 0 y),", goal_v)
        self.assertNotIn("H1", goal_v)
        self.assertIn("(H1 : Z.le 0 x)", (out / "6960-1" / "goal_full.v").read_text())
        self.assertIn("truth: true", (out / "6960-1" / "CONTROL").read_text())
        self.assertIn("truth: unknown", (out / "6960-2" / "CONTROL").read_text())
        self.assertIn("may be false", (out / "6960-2" / "FACTS.md").read_text())
        check = (out / "6960-1" / "check.sh").read_text()
        self.assertIn("ZESU_MODULE_CLAIM_BYTES=1073741824", check)
        self.assertIn("OCAMLPATH='/out/_findlib'", check)
        self.assertEqual(check.count("scope residual-check-"), 1)
        self.assertIn("'/repo/tools/resource_guard.sh' scope residual-check-6960-1 -- timeout 600 '/opt/coqc'", check)
        self.assertTrue(goal_v.endswith("Proof.\n" + pkg.SLOT + "\nAdmitted.\n"))
        self.assertEqual((out / "spatial.tsv").read_text().splitlines(),
                         ["block\tn\tkind\treason\tgoal_head", "6960\t0\tspatial\tspatial\tenvs_entails Δ P"])

    def test_check_sh_refuses_admitted_and_changed_statements(self):
        _, _, uniq = pkg.candidates(self.log, "6960", 1500, {"args"})
        d = self.dir / "g"
        stage = self.dir / "stage"
        pkg.stage_files(uniq[0], "6960", PREFIX, stage)
        out = self.dir / "out"
        out.mkdir()
        res = dict(control=dict(status="pass", seconds=1), goal=dict(status="pass", seconds=1))
        # The guard is never reached: a refused proof stops at the token check.
        d = pkg.write_goal_dir(out, uniq[0], "6960", stage, res, ["/bin/false"], "/bin/false", "/usr/bin:/bin", 1500,
                               "/out/_findlib")
        head = (d / "goal.v").read_text().split("(* PROOF-SLOT")[0]
        for proof in (head + "Admitted.\n", head.replace("Z.le 0 y", "True") + "Qed.\n",
                      head + "  timeout 5 lia.\nQed.\n"):
            (d / "proof.v").write_text(proof)
            r = subprocess.run(["bash", str(d / "check.sh")], capture_output=True, text=True)
            self.assertEqual(r.stdout.strip(), "FAIL")
            self.assertEqual((d / "check.log").read_text().strip(), "statement or token check failed")


class Manifest(unittest.TestCase):
    def manifest(self, **over):
        m = dict(block="6960", main_sha="f89336849", goal_list=["6960-1:aa", "6960-2:bb"],
                 controls={"6960-1": "pass", "6960-2": "fail"},
                 goals=[dict(id="6960-1", sha="aa", control="pass", truth="true", control_seconds=3.0,
                             goal_seconds=1.0)],
                 run_times=dict(total=100.0), started_utc="2026-11-09T00:00:00Z", finished_utc="2026-11-09T00:01:00Z")
        m.update(over)
        return m

    def test_run_times_do_not_count(self):
        a = self.manifest()
        b = self.manifest(run_times=dict(total=5.0), started_utc="x", finished_utc="y",
                          goals=[dict(a["goals"][0], control_seconds=9.0, goal_seconds=2.0)])
        self.assertEqual(pkg.compare(a, b), [])

    def test_goal_list_and_control_changes_count(self):
        a = self.manifest()
        self.assertEqual(pkg.compare(a, self.manifest(goal_list=["6960-1:aa"])), ["goal_list"])
        self.assertEqual(pkg.compare(a, self.manifest(controls={"6960-1": "pass", "6960-2": "pass"})),
                         ["controls"])

    def test_compare_command(self):
        with tempfile.TemporaryDirectory() as tmp:
            p1, p2 = Path(tmp) / "a.json", Path(tmp) / "b.json"
            p1.write_text(json.dumps(self.manifest()))
            p2.write_text(json.dumps(self.manifest(run_times=dict(total=1.0))))
            with contextlib.redirect_stdout(io.StringIO()) as printed:
                self.assertEqual(export_block.main(["--compare", str(p1), str(p2)]), 0)
                p2.write_text(json.dumps(self.manifest(goal_list=[])))
                self.assertEqual(export_block.main(["--compare", str(p1), str(p2)]), 1)
            self.assertIn('"differences": ["goal_list"]', printed.getvalue())

    def test_truth_marks(self):
        self.assertEqual(pkg.truth_of("pass"), "true")
        for status in ("fail", "timeout", "killed", "error"):
            self.assertEqual(pkg.truth_of(status), "unknown")


class Guarded(unittest.TestCase):
    def test_limit_sits_inside_the_scope(self):
        cmd = guarded.command("t", ["coqc", "-Q", "a", "b"], "f.v", limit_s=300)
        self.assertEqual(cmd[1:], ["scope", "t", "--", "timeout", "300", "coqc", "-Q", "a", "b", "f.v"])

    def test_classify(self):
        self.assertEqual(guarded.classify(0, ""), "pass")
        self.assertEqual(guarded.classify(124, ""), "timeout")
        self.assertEqual(guarded.classify(137, ""), "killed")
        self.assertEqual(guarded.classify(1, 'File "./a.v", line 1\nError: no'), "fail")
        self.assertEqual(guarded.classify(1, "live-memory admission: refused"), "error")


if __name__ == "__main__":
    unittest.main()
