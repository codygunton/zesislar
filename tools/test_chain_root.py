from contextlib import redirect_stderr
import io
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent / "block"))
import chain_root

# P0-B removed the writeSuccess proof tree. These tests read its modules,
# so they run only in a checkout that still has it.
NEEDS_WRITE_SUCCESS = unittest.skipUnless(
    (Path(__file__).resolve().parents[1] / "ZesuSsz/Generated/WriteSuccess").is_dir(),
    "reads ZesuSsz/Generated/WriteSuccess, removed in P0-B")


class ChainRootTests(unittest.TestCase):
    def test_cli_accepts_an_explicit_root(self):
        arguments = ["chain_root.py", "--entries", "/tmp/unused", "--cfg", "/tmp/cfg",
            "--build-dir", "/tmp/build", "--root", "0x1000", "--terminal", "0x2000",
            "--out", "/tmp/out", "--publish-dir", "/tmp/published",
            "--root-declaration", "Fixture.root", "--root-source", "/tmp/root.v",
            "--proof-dir", "/tmp/proofs", "--stage-dir", "/tmp/stage",
            "--trace-import", "Fixture.Traces", "--code-premises", "/tmp/premises"]
        with patch.object(sys, "argv", arguments), patch.object(chain_root, "run", return_value=0) as run:
            self.assertEqual(chain_root.main(), 0)
        self.assertEqual(run.call_args.args[0].root, "0x1000")

    def test_back_edge_uses_ancestry_not_addresses(self):
        blocks = {10: {"successors": ["0x5"]},
                  5: {"successors": ["0xf"]},
                  15: {"successors": ["0x5"]}}
        self.assertEqual(chain_root.back_edges(blocks, 10), {(15, 5)})

    def test_debts_distinguish_equal_owned_states(self):
        left = {"spatial": ["P"], "pending_goals": ["x < 8"]}
        right = {"spatial": ["P"], "pending_goals": ["x < 9"]}
        self.assertNotEqual(chain_root.fingerprint(left), chain_root.fingerprint(right))

    def test_branch_captures_and_back_edge_stop(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            entries = root / "entry.json"
            entries.write_text(json.dumps({"entry": "0xa", "outcome": "reached",
                "binders": "(sp : bv 64)", "spatial": ["P"], "coq": [],
                "root_provenance": {"source": "fixture", "verified_baseline": "test"},
                "shelved_goals": [{"conclusion": "False"}]}))
            cfg = root / "cfg.json"
            cfg.write_text(json.dumps({"functions": [{"start": 10, "blocks": [
                {"start": 10, "end": 14, "successors": ["0x14", "0x1e"]},
                {"start": 20, "end": 24, "successors": ["0xa"]},
                {"start": 30, "end": 34, "successors": []}]}]}))
            args = SimpleNamespace(entries=entries, root="0xa", cfg=cfg,
                                   out=root / "out", publish_dir=root / "published",
                                   terminal="0x28", jobs=2, build_dir=root, seconds=1)

            def capture(state, block, successor, build, seconds):
                return {"outcome": "reached", "entry": hex(block["start"]),
                        "exit": hex(successor), "coq": [], "spatial": ["P"],
                        "pending_goals": [], "shelved_goals": []}

            with patch.object(chain_root, "probe", side_effect=capture), \
                    patch.object(chain_root, "render_successor", return_value="state"), \
                    patch.object(chain_root, "check_subsumption", return_value={"outcome": "closed"}):
                self.assertEqual(chain_root.run(args), 0)
            records = json.loads((args.out / "post_states/a.json").read_text())
            self.assertEqual({row["exit"] for row in records}, {"0x14", "0x1e"})
            for row in records:
                self.assertIn({"conclusion": "False"}, row["derived_state"]["pending_goals"])
                self.assertEqual(row["derived_state"]["provenance"]["source"], "fixture")
                self.assertEqual(row["derived_state"]["provenance"]["verified_baseline"], "test")
            back = json.loads((args.out / "post_states/14.json").read_text())[0]
            self.assertTrue(back["back_edge"])
            self.assertEqual(back["subsumption"]["outcome"], "closed")
            self.assertEqual(json.loads((args.out / "chain_summary.json").read_text())["captures"], 4)
            self.assertEqual(json.loads((args.out / "chain_summary.json").read_text())["pending"], 0)
            terminal = json.loads((args.out / "post_states/1e.json").read_text())[0]
            self.assertTrue(terminal["terminal"])

    def test_unexpected_external_boundary_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            entries = root / "entry.json"
            entries.write_text(json.dumps({"entry": "0xa", "outcome": "reached",
                "binders": "(sp : bv 64)", "spatial": ["P"], "coq": [],
                "root_provenance": {"source": "fixture"}}))
            cfg = root / "cfg.json"
            cfg.write_text(json.dumps({"functions": [{"start": 10, "blocks": [
                {"start": 10, "end": 14, "successors": ["0x999"]}]}]}))
            args = SimpleNamespace(entries=entries, root="0xa", cfg=cfg,
                                   out=root / "out", publish_dir=root / "published",
                                   terminal="0x28", jobs=1, build_dir=root, seconds=1)
            capture = {"entry": "0xa", "exit": "0x999", "outcome": "reached"}
            with patch.object(chain_root, "probe", return_value=capture):
                self.assertEqual(chain_root.run(args), 1)
            summary = json.loads((args.out / "chain_summary.json").read_text())
            self.assertEqual(summary["errors"], 1)
            self.assertEqual(summary["pending"], 0)
            self.assertFalse(args.publish_dir.exists())

    def test_level1_root_rejects_unidentified_legacy_capture(self):
        with tempfile.TemporaryDirectory() as directory:
            entries = Path(directory) / "entry.json"
            entries.write_text(json.dumps({"entry": "0x14d30", "outcome": "reached",
                "binders": "(sp : bv 64)", "spatial": ["P"], "coq": []}))
            args = SimpleNamespace(entries=entries, root="0x14d30", cfg=Path("unused"))
            blocks = {0x14d30: {"successors": []}}
            with patch.object(chain_root.Path, "read_text", autospec=True,
                    side_effect=lambda path: entries.read_bytes().decode() if path == entries else '{}'), \
                    patch.object(chain_root, "graph", return_value=blocks):
                with self.assertRaisesRegex(ValueError, 'root declaration'):
                    chain_root.run(args)

    def test_level1_root_rejects_changed_resources_with_same_provenance(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            entries = root / "entry.json"
            entries.write_text(json.dumps({"entry": "0xa", "outcome": "reached",
                "binders": "(sp : bv 64)", "spatial": ["P"], "coq": [],
                "root_provenance": {"source": "Fixture.root"}}))
            cfg = root / "cfg.json"
            cfg.write_text(json.dumps({"functions": [{"start": 10,
                "blocks": [{"start": 10, "successors": []}]}]}))
            checked = root / "Root.v"
            checked.write_text("checked resources")
            args = SimpleNamespace(entries=entries, root="0xa", cfg=cfg,
                                   root_source=checked, root_declaration="Fixture.root")
            with patch.object(chain_root, "render_successor", return_value="changed resources"):
                with self.assertRaisesRegex(ValueError, 'root resources differ'):
                    chain_root.run(args)

    def test_graph_accepts_stock_entry_and_rows(self):
        graph = chain_root.graph({"functions": [{"entry": 10, "rows": [
            {"pc": 10, "kind": "return"}], "blocks": [
            {"start": 10, "end": 14, "successors": []}]}]}, 10)
        self.assertEqual(graph[10]["instructions"][0]["kind"], "return")

    def test_probe_source_uses_explicit_resources_and_trace_import(self):
        options = {"trace_import": "Fixture.Traces", "code_premises": ["  P -∗"]}
        source = "From Legacy.Traces Require Import Index.\n" + "\n".join(chain_root.infer_boundary.CODE_PREMISES)
        with patch.object(chain_root.infer_boundary, "spec_source", return_value=source):
            actual = chain_root.probe_source({}, options, 20)
        self.assertIn("Require Import Fixture.Traces.", actual)
        self.assertIn("  P -∗", actual)
        self.assertNotIn("Legacy.Traces", actual)

    def test_baseline_preserves_missing_and_unknown_locations(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "baseline.json"
            captures = [
                {"entry": "0xa", "outcome": "stalled", "residual_pcs": [10],
                 "pending_goals": [{"conclusion": "entry residual"}]},
                {"entry": "0x14", "outcome": "stalled", "residual_pcs": [24],
                 "pending_goals": [{"conclusion": "execution residual"}]},
                {"entry": "0x1e", "outcome": "stalled"},
                {"entry": "0x28", "outcome": "closed"},
                {"entry": "0x32", "outcome": "reached"}]
            chain_root.write_baseline(path, dict.fromkeys([10, 20, 30, 40, 50, 60]), captures)
            result = json.loads(path.read_text())
        self.assertEqual([row["outcomes"] for row in result["blocks"]], [
            ["entry-stall"], ["execution-stall"], ["unknown-stall"],
            ["closed"], ["reached"], ["missing-entry"]])
        self.assertEqual(result["first_residuals"]["entry-stall"]["residual"]["conclusion"],
                         "entry residual")

    def test_pc_marker_rejects_an_unevaluated_expression(self):
        output = ("CHAIN-RESIDUAL-PC (bv_to_bvn (Z_to_bv 64 4100))\n"
                  "CHAIN-RESIDUAL-PC (bv_to_bvn (bv_add (Z_to_bv 64 4096) offset))\n")
        self.assertEqual(chain_root.residual_pc_markers(output), ([4100], "unknown"))
        self.assertEqual(chain_root.residual_pc_markers(output.splitlines()[0]), ([4100], "known"))

    def test_compiler_uses_explicit_staging(self):
        with tempfile.TemporaryDirectory() as directory:
            stage = Path(directory) / "stage"
            done = SimpleNamespace(stdout="output", stderr="errors")
            with patch.object(chain_root.subprocess, "run", return_value=done) as run:
                text = chain_root.compile_probe("Goal True. Abort.", "Probe", Path("/tmp/build"),
                                                1, {"stage_dir": str(stage)})
            self.assertEqual((stage / "Probe.v").read_text(), "Goal True. Abort.")
            self.assertIn(str(stage / "Probe.v"), run.call_args.args[0])
            self.assertEqual(text, "output\nerrors")

    def test_same_successor_variants_have_distinct_fingerprints(self):
        first = {"coq": [["H", "x = 0"]], "spatial": ["p ↦ₘ x"]}
        second = {"coq": [["H", "x = 1"]], "spatial": ["p ↦ₘ x"]}
        self.assertNotEqual(chain_root.fingerprint(first), chain_root.fingerprint(second))

    def test_captured_widths_affect_fingerprint(self):
        first = {"spatial": ["p ↦ₘ 0"], "memory_word_widths": {"p": 8}}
        second = {"spatial": ["p ↦ₘ 0"], "memory_word_widths": {"p": 64}}
        self.assertNotEqual(chain_root.fingerprint(first), chain_root.fingerprint(second))

    def test_address_widths_distinguish_states(self):
        first = {"spatial": ["p ↦ₘ 0"], "address_widths": {"p": 32}}
        second = {"spatial": ["p ↦ₘ 0"], "address_widths": {"p": 64}}
        self.assertNotEqual(chain_root.fingerprint(first), chain_root.fingerprint(second))

    def test_failed_compiler_does_not_publish_reached_state(self):
        fixture = (Path(__file__).parent / "fixtures/chain_goals_native.log").read_text()
        fixture = fixture.replace("CHAIN-GOAL-CONCLUSION True%I",
                                  "CHAIN-GOAL-CONCLUSION BLK_STOP_14d80")
        fixture += "\n" + chain_root.probes.END + "\nexit=137 ms=3000 rss_kb=1024\n"
        state = {"name": "Root", "binders": "`{!islaG Sigma} `{!threadG}",
                 "coq": [], "spatial": ["True"]}
        block = {"start": 0x14d30, "end": 0x14d80, "successors": ["0x14d80"]}
        with patch.object(chain_root.subprocess, "run"), \
                patch.object(chain_root.infer_boundary, "run", return_value=fixture):
            captures = chain_root.probe(state, block, 0x14d80, Path("/tmp"), 1)
        self.assertEqual([capture["outcome"] for capture in captures], ["error"])

    def test_missing_compiler_exit_record_rejects_capture(self):
        fixture = (Path(__file__).parent / "fixtures/chain_goals_native.log").read_text()
        fixture = fixture.replace("CHAIN-GOAL-CONCLUSION True%I",
                                  "CHAIN-GOAL-CONCLUSION BLK_STOP_14d80")
        fixture += "\n" + chain_root.probes.END + "\n"
        state = {"name": "Root", "binders": "`{!islaG Sigma} `{!threadG}",
                 "coq": [], "spatial": ["True"]}
        block = {"start": 0x14d30, "end": 0x14d80, "successors": ["0x14d80"]}
        with patch.object(chain_root.subprocess, "run"), \
                patch.object(chain_root.infer_boundary, "run", return_value=fixture):
            captures = chain_root.probe(state, block, 0x14d80, Path("/tmp"), 1)
        self.assertEqual([capture["outcome"] for capture in captures], ["error"])

    def test_shelved_goal_with_different_width_is_preserved(self):
        fixture = (Path(__file__).parent / "fixtures/chain_goals_native.log").read_text()
        active = chain_root.parse_goals(fixture, phase="active")[0]
        active["conclusion"] = "BLK_STOP_14d80"
        shelved = {**active, "memory_word_widths":
                   {address: 8 for address in active["memory_word_widths"]}}
        state = {"name": "Root", "binders": "`{!islaG Sigma} `{!threadG}",
                 "coq": [], "spatial": ["True"]}
        block = {"start": 0x14d30, "end": 0x14d80, "successors": ["0x14d80"]}
        with patch.object(chain_root.subprocess, "run"), \
                patch.object(chain_root.infer_boundary, "run", return_value=chain_root.probes.END + "\nexit=0 ms=1 rss_kb=1024"), \
                patch.object(chain_root, "parse_goals", side_effect=[[active], [shelved]]):
            captures = chain_root.probe(state, block, 0x14d80, Path("/tmp"), 1)
        self.assertEqual(captures[0]["shelved_goals"], [shelved])

    def test_probe_keeps_every_native_goal_at_same_stop(self):
        fixture = (Path(__file__).parent / "fixtures/chain_goals_native.log").read_text()
        fixture = fixture.replace("CHAIN-GOAL-CONCLUSION True%I",
                                  "CHAIN-GOAL-CONCLUSION BLK_STOP_14d80")
        fixture += "\n" + chain_root.probes.END + "\nexit=0 ms=1 rss_kb=1024\n"
        state = {"name": "Root", "binders": "`{!islaG Sigma} `{!threadG}",
                 "coq": [], "spatial": ["True"], "root_provenance": {"entry": "0x14d30"}}
        block = {"start": 0x14d30, "end": 0x14d80, "successors": ["0x14d80"]}
        with patch.object(chain_root.subprocess, "run"), \
                patch.object(chain_root.infer_boundary, "run", return_value=fixture):
            captures = chain_root.probe(state, block, 0x14d80, Path("/tmp"), 1)
        self.assertEqual(len(captures), 2)
        self.assertNotEqual(captures[0]["spatial"], captures[1]["spatial"])
        self.assertEqual(list(captures[0]["memory_word_widths"].values()), [64])
        self.assertEqual(list(captures[1]["memory_word_widths"].values()), [8])
        self.assertTrue(all(capture["context"] for capture in captures))
        implication = fixture.replace("CHAIN-GOAL-CONCLUSION BLK_STOP_14d80",
            "CHAIN-GOAL-CONCLUSION True%I -∗ BLK_STOP_14d80", 1)
        with patch.object(chain_root.subprocess, "run"), \
                patch.object(chain_root.infer_boundary, "run", return_value=implication):
            captures = chain_root.probe(state, block, 0x14d80, Path("/tmp"), 1)
        self.assertEqual(len(captures), 1)
        self.assertEqual(list(captures[0]["memory_word_widths"].values()), [8])


if __name__ == "__main__":
    unittest.main()
