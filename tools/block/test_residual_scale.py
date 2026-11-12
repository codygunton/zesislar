"""The residual step at scale: plan, block states, bundles, pacing, report."""
from contextlib import redirect_stdout
from pathlib import Path
import io
import sys
import tempfile
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import residual_scale as scale  # noqa: E402


# A fake residual_loop.py: `export` writes a manifest whose shape the block name
# selects; `register` and `rerun` record their call; `collect` marks every goal PASS.
FAKE_LOOP = r'''
import json, sys
from pathlib import Path
args = sys.argv[1:]
cmd = args[0]
opt = {args[i]: args[i + 1] for i in range(1, len(args) - 1) if args[i].startswith("--")}
if cmd == "export":
    out = Path(opt["--out"]); block = opt["--block"]
    (out / "goals").mkdir(parents=True)
    goals = []
    if block == "open":
        goals = [dict(id="open-1", name="residual_open_a", reparse="exact", source="final", binders=[])]
        (out / "goals" / "open-1").mkdir()
        (out / "goals" / "open-1" / "STATUS.json").write_text(json.dumps(dict(result="OPEN", attempts=[])))
    rc = 0 if block == "shut" else 1
    manifest = dict(block=block, goals=goals, skipped=[], reruns=[],
                    exports=[dict(returncode=rc, stopped=False, seconds=1.0)])
    (out / "MANIFEST.json").write_text(json.dumps(manifest))
    (out / "RESULTS.txt").write_text("".join("RESULT %s OPEN\n" % g["id"] for g in goals))
    print("export", block, "|".join(sys.argv[1:]))
elif cmd == "collect":
    run = Path(opt["--run"])
    for d in (run / "goals").iterdir():
        (d / "STATUS.json").write_text(json.dumps(dict(result="PASS", attempts=[dict(sha256="x", result="PASS")])))
elif cmd in ("register", "rerun"):
    run = Path(opt["--run"])
    calls = run.parent / "CALLS"
    calls.write_text((calls.read_text() if calls.exists() else "") + cmd + "\n")
    if cmd == "rerun":
        m = json.loads((run / "MANIFEST.json").read_text())
        m["reruns"].append(dict(closed=True, seconds=2.0, round=2))
        (run / "MANIFEST.json").write_text(json.dumps(m))
'''


def manifest(goals=(), skipped=(), returncode=1, stopped=False, reruns=()):
    return dict(goals=list(goals), skipped=list(skipped), reruns=list(reruns),
                exports=[dict(returncode=returncode, stopped=stopped, seconds=10.0)])


def make_block(run, block, data, statuses=None):
    loop = scale.loop_dir(run, block)
    (loop / "goals").mkdir(parents=True)
    scale.write_json(loop / "MANIFEST.json", data)
    for gid, status in (statuses or {}).items():
        (loop / "goals" / gid).mkdir()
        scale.write_json(loop / "goals" / gid / "STATUS.json", status)


class PlanTests(unittest.TestCase):
    def test_plan_copies_each_caller_and_records_the_bank(self):
        with tempfile.TemporaryDirectory() as root:
            root = Path(root)
            (root / "callers").mkdir()
            for b in ("62b8", "6274"):
                (root / "callers" / ("Caller%s.v" % b)).write_text("Lemma DesignedBoundary_800d%s : True.\n" % b)
            (root / "callers" / "CALLERS.json").write_text("{}")
            with redirect_stdout(io.StringIO()):
                scale.main(["plan", "--function", "nextUint64", "--callers", str(root / "callers"),
                            "--bank", str(root), "--out", str(root / "run")])
            plan = scale.read_json(root / "run" / "PLAN.json")
            self.assertEqual([b["block"] for b in plan["blocks"]], ["6274", "62b8"])
            self.assertTrue((root / "run" / "blocks" / "62b8" / "caller.v").exists())
            self.assertTrue((root / "run" / "residuals").is_dir())

    def test_unknown_block_is_refused(self):
        with tempfile.TemporaryDirectory() as root:
            (Path(root) / "Caller1234.v").write_text("")
            with self.assertRaises(scale.ScaleError):
                scale.callers_of(root, ["9999"])


class ModuleAndBankTests(unittest.TestCase):
    def test_module_names_come_from_the_function_symbol(self):
        self.assertEqual(scale.module_for("rlp.decodeItem", "6960"), "Residual_rlp_decodeItem_6960")
        self.assertEqual(scale.module_for("berlinGasCalc", "39b8"), "Residual_berlinGasCalc_39b8")

    def test_export_takes_a_later_bank_and_refreshes_a_rerendered_caller(self):
        with tempfile.TemporaryDirectory() as root:
            root = Path(root)
            (root / "callers").mkdir()
            (root / "callers" / "Caller1234.v").write_text("old\n")
            (root / "fake_loop.py").write_text(FAKE_LOOP)
            with redirect_stdout(io.StringIO()):
                scale.main(["plan", "--function", "f", "--callers", str(root / "callers"),
                            "--bank", str(root / "later"), "--out", str(root / "run")])
                self.assertEqual(scale.read_json(root / "run" / "PLAN.json")["blocks"][0]["module"],
                                 "Residual_f_1234")
                with self.assertRaises(SystemExit):  # the planned bank does not exist yet
                    scale.main(["export", "--run", str(root / "run")])
                (root / "bank").mkdir()
                (root / "bank" / "ARGS.json").write_text("[]")
                (root / "callers" / "Caller1234.v").write_text("new\n")
                saved = scale.LOOP
                scale.LOOP = root / "fake_loop.py"
                try:
                    scale.main(["export", "--run", str(root / "run"), "--bank", str(root / "bank")])
                finally:
                    scale.LOOP = saved
            plan = scale.read_json(root / "run" / "PLAN.json")
            copy = (root / "run" / "blocks" / "1234" / "caller.v").read_text()
        self.assertEqual(plan["bank"], str((root / "bank").resolve()))
        self.assertEqual(copy, "new\n")


class BankTargetTests(unittest.TestCase):
    def test_targets_are_the_switch_and_the_callers_zesussz_imports(self):
        with tempfile.TemporaryDirectory() as root:
            caller = Path(root) / "Caller39b8.v"
            caller.write_text("Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot39b8Entries.\n"
                              "Require Import isla.riscv64.riscv64.\n"
                              "Require Import ZesuSsz.Contracts.BerlinGasCalcSelected.\n")
            targets = scale.bank_targets(dict(blocks=[dict(block="39b8", caller=str(caller))]))
        self.assertEqual(targets[0], "@install")
        self.assertIn("ZesuSsz/Automation2/ResidualExportOn.vo", targets)
        self.assertIn("ZesuSsz/Generated/BerlinGasCalc/FP301/Pilot39b8Entries.vo", targets)
        self.assertIn("ZesuSsz/Contracts/BerlinGasCalcSelected.vo", targets)
        self.assertFalse(any("isla" in target for target in targets))


class BankArgsTests(unittest.TestCase):
    def test_bank_args_map_the_build_tree(self):
        with tempfile.TemporaryDirectory() as root:
            (Path(root) / "build" / "default" / "ZesuSsz").mkdir(parents=True)
            with redirect_stdout(io.StringIO()):
                scale.main(["bank-args", "--build-dir", str(Path(root) / "build"), "--out", str(Path(root) / "bank")])
            args = scale.read_json(Path(root) / "bank" / "ARGS.json")
            with self.assertRaises(scale.ScaleError):
                scale.bank_args(Path(root) / "missing")
        default = str((Path(root) / "build" / "default").resolve())
        self.assertEqual(args[1:4], ["-Q", default + "/ZesuSsz", "ZesuSsz"])
        self.assertIn("ZesuSsz.Stock.Closure", args)


class StateTests(unittest.TestCase):
    def test_rules_only_states(self):
        with tempfile.TemporaryDirectory() as run:
            goal = dict(id="b-1", reparse="exact")
            make_block(run, "closed", manifest(returncode=0))
            make_block(run, "open", manifest(goals=[goal]), {"b-1": dict(result="FAIL", attempts=[{}])})
            make_block(run, "stopped", manifest(goals=[goal], returncode=143, stopped=True))
            make_block(run, "spatial", manifest(skipped=[dict(kind="final", reason="spatial")]))
            make_block(run, "failed", manifest())
            states = {b: scale.block_state(run, b) for b in ("closed", "open", "stopped", "spatial", "failed", "none")}
        self.assertEqual({b: s["rules"] for b, s in states.items()},
                         dict(closed="closed", open="open", stopped="stopped", spatial="open-unexported",
                              failed="failed", none="not-run"))
        self.assertEqual(states["closed"]["final"], "closed")
        self.assertEqual(states["open"]["final"], "open")
        self.assertEqual((states["open"]["failed"], states["open"]["attempts"]), (1, 1))

    def test_a_closed_rerun_makes_the_block_final_closed(self):
        with tempfile.TemporaryDirectory() as run:
            make_block(run, "b", manifest(goals=[dict(id="b-1", reparse="exact")],
                                          reruns=[dict(closed=True, seconds=50.0, open_again=[], new_goals=[])]),
                       {"b-1": dict(result="PASS", attempts=[{}])})
            state = scale.block_state(run, "b")
        self.assertEqual((state["rules"], state["rerun"], state["final"], state["passed"]),
                         ("open", "closed", "closed", 1))


class BundleTests(unittest.TestCase):
    def test_bundles_hold_open_exact_goals_in_order(self):
        with tempfile.TemporaryDirectory() as run:
            run = Path(run)
            scale.write_json(run / "PLAN.json", dict(function="f", blocks=[dict(block="a"), dict(block="b")]))
            goals = [dict(id="a-1", reparse="exact"), dict(id="a-2", reparse="differs"),
                     dict(id="a-3", reparse="exact"), dict(id="a-4", reparse="exact")]
            make_block(run, "a", manifest(goals=goals), {"a-1": dict(result="OPEN"), "a-3": dict(result="FAIL"),
                                                         "a-4": dict(result="PASS")})
            make_block(run, "b", manifest(returncode=0))
            with redirect_stdout(io.StringIO()):
                scale.cmd_bundle(type("A", (), dict(run=str(run)))())
            readme = (run / "bundles" / "a" / "README.md").read_text()
            prompt = (run / "bundles" / "a" / "AGENT_PROMPT.txt").read_text()
            self.assertFalse((run / "bundles" / "b").exists())
        self.assertIn("2 residual goal(s)", readme)
        self.assertLess(readme.index("`a-1`"), readme.index("`a-3`"))
        self.assertNotIn("`a-2`", readme)
        self.assertNotIn("`a-4`", readme)
        self.assertIn("never proof text", readme)
        self.assertIn("rewrite lemma by tac", readme)
        self.assertIn("Read and Write tools", prompt)


class PacingTests(unittest.TestCase):
    def test_starts_are_spaced_by_the_gap(self):
        starts = []
        scale.paced(["a", "b", "c"], lambda b: starts.append(time.monotonic()) or b, 3, 0.05)
        starts.sort()
        self.assertTrue(all(later - earlier >= 0.045 for earlier, later in zip(starts, starts[1:])))


class DriverTests(unittest.TestCase):
    def test_export_collect_rerun_report_with_a_fake_loop(self):
        with tempfile.TemporaryDirectory() as root:
            root = Path(root)
            (root / "callers").mkdir()
            for b in ("open", "shut"):
                (root / "callers" / ("Caller%s.v" % b)).write_text("")
            (root / "fake_loop.py").write_text(FAKE_LOOP)
            (root / "ARGS.json").write_text("[]")
            saved = scale.LOOP
            scale.LOOP = root / "fake_loop.py"
            try:
                with redirect_stdout(io.StringIO()):
                    scale.main(["plan", "--function", "f", "--callers", str(root / "callers"), "--bank", str(root),
                                "--out", str(root / "run")])
                    scale.main(["export", "--run", str(root / "run"), "--jobs", "2"])
                    first = (root / "run" / "blocks" / "open" / "export.out").read_text()
                    scale.main(["export", "--run", str(root / "run")])  # done blocks are not exported again
                    scale.main(["collect", "--run", str(root / "run")])
                    scale.main(["rerun", "--run", str(root / "run")])
                    out = io.StringIO()
                    with redirect_stdout(out):
                        scale.main(["report", "--run", str(root / "run")])
                    counts = io.StringIO()
                    with redirect_stdout(counts):
                        scale.main(["report", "--run", str(root / "run"), "--counts-only"])
            finally:
                scale.LOOP = saved
            calls_open = (root / "run" / "blocks" / "open" / "CALLS").read_text().split()
            self.assertFalse((root / "run" / "blocks" / "shut" / "CALLS").exists())
        self.assertIn("--claim-gib", first)
        self.assertIn("--module|Residual_f_open", first)
        self.assertEqual(calls_open, ["register", "rerun"])
        report = out.getvalue()
        self.assertIn("RESULT open rules=open goals=1 exact=1 pass=1 fail=0 unexported=0 rerun=closed final=closed",
                      report)
        self.assertIn("RESULT shut rules=closed", report)
        self.assertIn("SUMMARY blocks=2 rules-only-closed=1 rules-plus-residual-closed=2 added=1", report)
        self.assertNotIn("unique-proof-token", report)
        self.assertNotIn("RESULT open ", counts.getvalue())
        self.assertIn("SUMMARY blocks=2", counts.getvalue())


if __name__ == "__main__":
    unittest.main()
