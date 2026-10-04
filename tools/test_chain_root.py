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
    def test_generalized_template_preserves_parameters_provenance_and_debts(self):
        state = {"binders": "`{!islaG Sigma} `{!threadG} (args : DecodeItemArgs)",
                 "coq": [["captured", "bv 64"]], "spatial": ["captured ownership"],
                 "root_provenance": {"source": "root"}, "provenance": {"source": "root"},
                 "pending_goals": [{"conclusion": "False"}], "shelved_goals": ["debt"]}
        hint = {"header_pc": "0x14", "rocq_predicate": "Fixture.foldAt",
                "symbolic_parameters": {"i": {"register": "x15"}},
                "register_bindings": {"x15": "payloadStart + i"}, "design_sha256": "frozen"}
        header = chain_root.generalized_header(state, hint)
        for key in ("binders", "root_provenance", "provenance", "pending_goals", "shelved_goals"):
            self.assertEqual(header[key], state[key])
        self.assertEqual(header["coq"], [])
        self.assertIn("Fixture.foldAt 0x14 args n i payloadStart lengthBytes frameBytes loaded",
                      header["spatial"][0])
        self.assertIn("∃ (n i payloadStart : Z)", header["spatial"][0])
        self.assertEqual(state["spatial"], ["captured ownership"])
        with self.assertRaisesRegex(ValueError, "existing DecodeItemArgs"):
            chain_root.generalized_header({**state, "binders": "(sp : bv 64)"}, hint)

    def test_generalized_header_requires_closed_entailment_before_requeue(self):
        for outcome in ("closed", "conditional", "residual"):
            with self.subTest(outcome=outcome), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                entries, cfg = root / "entries.json", root / "cfg.json"
                entries.write_text(json.dumps({"entry": "0xa", "outcome": "reached",
                    "binders": "(args : DecodeItemArgs)", "spatial": ["P"], "coq": [],
                    "root_provenance": {"source": "fixture"}}))
                cfg.write_text(json.dumps({"functions": [{"start": 10, "blocks": [
                    {"start": 10, "end": 14, "successors": ["0x14"]},
                    {"start": 20, "end": 24, "successors": ["0x14", "0x1e"]},
                    {"start": 30, "end": 34, "successors": []}]}]}))
                hint = {"header_pc": "0x14", "rocq_predicate": "Fixture.foldAt",
                        "symbolic_parameters": {}, "register_bindings": {}, "exit": "0x1e",
                        "design_sha256": "frozen", "machine_obligations": {
                            kind: "Fixture." + kind for kind in ("entry", "preservation", "exit")},
                        "pure_lemmas": {kind: "Fixture.pure" for kind in ("entry", "preservation", "exit")}}
                args = SimpleNamespace(entries=entries, cfg=cfg, root="0xa", terminal="0x28",
                    out=root / "out", publish_dir=root / "published", jobs=1,
                    build_dir=root, seconds=1)
                visited = []
                def capture(state, block, successor, build, seconds):
                    visited.append((block["start"], state))
                    return {"outcome": "reached", "entry": hex(block["start"]),
                            "exit": hex(successor), "coq": [], "spatial": ["P"],
                            "pending_goals": [], "shelved_goals": []}
                with patch.object(chain_root, "load_invariant_hints", return_value={20: hint}), \
                     patch.object(chain_root, "probe", side_effect=capture), \
                     patch.object(chain_root, "render_successor", return_value="state"), \
                     patch.object(chain_root, "check_subsumption", return_value={"outcome": outcome}):
                    # Machine propositions remain pending even when the entailments close.
                    self.assertEqual(chain_root.run(args), 1)
                records = json.loads((args.out / "post_states/a.json").read_text())
                self.assertEqual(bool(records[0].get("requeued_generalized_header")), outcome == "closed")
                headers = [state for pc, state in visited if pc == 20]
                self.assertEqual(bool(headers), outcome == "closed")
                if headers:
                    self.assertTrue(all(state["name"] == "GeneralizedHeader_14" for state in headers))
                    back = json.loads((args.out / "post_states/14.json").read_text())
                    self.assertEqual(next(row for row in back if row["exit"] == "0x14")["invariant_edge"], "preservation")
                    self.assertEqual(next(row for row in back if row["exit"] == "0x1e")["invariant_exit"]["status"], "pending")
                summary = json.loads((args.out / "chain_summary.json").read_text())
                self.assertTrue(all(row["status"] == "pending" for row in summary["invariant_obligations"]))

    def test_root_header_generalizes_before_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            entries, cfg = root / "entries.json", root / "cfg.json"
            state = {"entry": "0xa", "outcome": "reached", "binders": "(args : DecodeItemArgs)",
                     "spatial": ["P"], "coq": [], "root_provenance": {"source": "fixture"}}
            entries.write_text(json.dumps(state))
            cfg.write_text(json.dumps({"functions": [{"start": 10, "blocks": [
                {"start": 10, "end": 14, "successors": ["0xa"]}]}]}))
            args = SimpleNamespace(entries=entries, cfg=cfg, root="0xa", terminal="0x28",
                out=root / "out", publish_dir=root / "published", jobs=1, build_dir=root, seconds=1)
            hint = {"header_pc": "0xa", "rocq_predicate": "Fixture.foldAt", "exit": "0x28",
                    "symbolic_parameters": {}, "register_bindings": {}, "design_sha256": "frozen",
                    "machine_obligations": {kind: "Fixture." + kind for kind in ("entry", "preservation", "exit")},
                    "pure_lemmas": {kind: "Fixture.pure" for kind in ("entry", "preservation", "exit")}}
            with patch.object(chain_root, "load_invariant_hints", return_value={10: hint}), \
                 patch.object(chain_root, "check_subsumption", return_value={"outcome": "conditional"}), \
                 patch.object(chain_root, "probe") as probe:
                self.assertEqual(chain_root.run(args), 1)
            probe.assert_not_called()
            summary = json.loads((args.out / "chain_summary.json").read_text())
            self.assertEqual(summary["root_generalization"]["outcome"], "conditional")
            self.assertEqual(summary["captures"], 0)

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
        source = ("From Legacy.Traces Require Import Index.\nLemma infer_boundary :\n"
                  + "\n".join(chain_root.infer_boundary.CODE_PREMISES)
                  + "\n  instr_body 0xa P.\nProof.\nAbort.\n")
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


class ChainRootInvariantTests(unittest.TestCase):
    def fixture(self, directory, terminal="returnAddress"):
        root = Path(directory)
        entries = root / "entries.json"
        entries.write_text(json.dumps({"entry": "0xa", "outcome": "reached",
            "binders": "(returnAddress : Z)", "spatial": ["P"], "coq": [],
            "root_provenance": {"source": "Fixture.root"}}))
        cfg = root / "cfg.json"
        cfg.write_text(json.dumps({"functions": [{"entry": 10, "blocks": [
            {"start": 10, "end": 14, "successors": [20]},
            {"start": 20, "end": 24, "successors": [20, 30]},
            {"start": 30, "end": 34, "successors": [],
             "instructions": [{"kind": "return", "rs1": 1, "imm": 0}]}]}]}))
        return SimpleNamespace(entries=entries, root="0xa", cfg=cfg,
            out=root / "out", publish_dir=root / "publish", terminal=terminal,
            jobs=1, seconds=1, build_dir=root)

    @staticmethod
    def capture(state, block, successor, build, seconds):
        return {"outcome": "reached", "entry": hex(block["start"]),
            "exit": chain_root.boundary_address(successor), "coq": [], "spatial": ["P"],
            "pending_goals": [], "shelved_goals": []}

    def test_symbolic_return_is_reached_without_numeric_sentinel(self):
        with tempfile.TemporaryDirectory() as directory:
            args = self.fixture(directory)
            with patch.object(chain_root, "probe", side_effect=self.capture), \
                    patch.object(chain_root, "render_successor", return_value="state"), \
                    patch.object(chain_root, "check_subsumption", return_value={"outcome": "closed"}):
                self.assertEqual(chain_root.run(args), 0)
            record = json.loads((args.out / "post_states/1e.json").read_text())[0]
            self.assertTrue(record["terminal"])
            self.assertEqual(record["exit"], "returnAddress")
            self.assertEqual(record["derived_state"]["state_entry"], "returnAddress")

    def test_failed_back_edge_entailment_fails_completion(self):
        with tempfile.TemporaryDirectory() as directory:
            args = self.fixture(directory, "0x28")
            with patch.object(chain_root, "probe", side_effect=self.capture), \
                    patch.object(chain_root, "render_successor", return_value="state"), \
                    patch.object(chain_root, "check_subsumption", return_value={"outcome": "conditional"}):
                self.assertEqual(chain_root.run(args), 1)
            report = json.loads((args.out / "chain_summary.json").read_text())
            self.assertEqual(report["failed_subsumptions"], 1)
            self.assertTrue(report["capture_only"])

    def test_symbolic_terminal_rejects_command_injection(self):
        for value in ["returnAddress. Qed.", "returnAddress; admit", "returnAddress\nQed", "(returnAddress"]:
            with self.assertRaises(ValueError):
                chain_root.terminal_target(value)
        self.assertEqual(chain_root.terminal_target("decodeItemReturnAddress args"),
                         "decodeItemReturnAddress args")

    def test_q27_hints_match_real_cfg_headers(self):
        root = Path(__file__).resolve().parents[1]
        cfg = json.loads((root / "build/stock-zisk/cfg.json").read_text())
        entry = 0x800d6960
        blocks = chain_root.graph(cfg, entry)
        hints = chain_root.load_invariant_hints(root / "ZesuSsz/Evidence/decode_item_block_design.json", blocks, entry)
        self.assertEqual(set(hints), {0x800d6a24, 0x800d6ac4})
        obligations = chain_root.invariant_obligations(hints)
        self.assertEqual(len(obligations), 6)
        self.assertTrue(all(row["status"] == "pending" for row in obligations))
        self.assertTrue(all(row["capture_only"] for row in obligations))

    def test_conflicting_register_hint_is_rejected(self):
        root = Path(__file__).resolve().parents[1]
        cfg = json.loads((root / "build/stock-zisk/cfg.json").read_text())
        design = json.loads((root / "ZesuSsz/Evidence/decode_item_block_design.json").read_text())
        next(row["invariant_hint"] for row in design["blocks"] if "invariant_hint" in row)["register_bindings"]["x15"] = "wrong"
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "design.json"
            path.write_text(json.dumps(design))
            with self.assertRaisesRegex(ValueError, "conflicts"):
                chain_root.load_invariant_hints(path, chain_root.graph(cfg, 0x800d6960), 0x800d6960)

    def test_symbolic_source_keeps_return_expression_in_premise(self):
        source = ('Lemma infer_boundary (returnAddress : Z) :\n'
                  '  instr_lookup_resources -∗\n  instr_body 0xa P.\nProof.\n'
                  'all: idtac "' + chain_root.infer_boundary.RAW_BEGIN + '".\nAbort.\n')
        state = {"name": "Fixture", "binders": "(returnAddress : Z)"}
        block = {"start": 10, "end": 14, "successors": []}
        with patch.object(chain_root.infer_boundary, "spec_source", return_value=source), \
                patch.object(chain_root.gen_block.call_sites, "premises", return_value=([], [], [])), \
                patch.object(chain_root.gen_block.call_sites, "contracts", return_value={}), \
                patch.object(chain_root.gen_block.call_sites, "call_sites", return_value={}), \
                patch.object(chain_root, "render_successor", return_value="Definition Fixture := P."):
            rendered = chain_root.render_probe(state, block, "returnAddress")
        self.assertTrue(rendered.startswith("Require Import ZesuSsz.Automation.All.\n"))
        self.assertIn("instr_pre (returnAddress) CHAIN_STOP_return_", rendered)
        self.assertNotIn("BLK_STOP_", rendered)


    def test_self_edge_preserves_instr_body_for_both_successors(self):
        source = ('Lemma infer_boundary (returnAddress : Z) :\n'
                  '  instr_lookup_resources -∗\n  instr_body 0xa P.\nProof.\n'
                  'all: idtac "' + chain_root.infer_boundary.RAW_BEGIN + '".\nAbort.\n')
        state = {"name": "Fixture", "binders": "(returnAddress : Z)"}
        block = {"start": 10, "end": 14, "successors": [10, 20]}
        for successor in [10, 20]:
            with self.subTest(successor=successor), \
                    patch.object(chain_root.infer_boundary, "spec_source", return_value=source), \
                    patch.object(chain_root.gen_block.call_sites, "premises", return_value=([], [], [])), \
                    patch.object(chain_root.gen_block.call_sites, "contracts", return_value={}), \
                    patch.object(chain_root.gen_block.call_sites, "call_sites", return_value={}), \
                    patch.object(chain_root, "render_successor", return_value="Definition Fixture := P."):
                rendered = chain_root.render_probe(state, block, successor)
            self.assertEqual(rendered.count("instr_body 0xa P."), 1)
            self.assertIn("instr_pre 0xa BLK_STOP_a -∗", rendered)
            self.assertIn("instr_pre 0x14 BLK_STOP_14 -∗", rendered)
            self.assertIn("instr_body 0xa P.\nProof.", rendered)


    def test_self_edge_with_folded_code_premises_keeps_conclusion(self):
        source = ('Lemma infer_boundary (args : DecodeItemArgs) :\n'
                  + "\n".join(chain_root.infer_boundary.CODE_PREMISES)
                  + '\n  instr_body 0xa P.\nProof.\n'
                  + 'all: idtac "' + chain_root.infer_boundary.RAW_BEGIN + '".\nAbort.\n')
        state = {"name": "Fixture", "binders": "(args : DecodeItemArgs)",
                 "probe_options": {"trace_import": "Fixture.Traces",
                                   "code_premises": ["  decodeItemSelectedCode args -∗"]}}
        block = {"start": 10, "end": 14, "successors": [10, 20]}
        for successor in [10, 20]:
            with self.subTest(successor=successor), \
                    patch.object(chain_root.infer_boundary, "spec_source", return_value=source), \
                    patch.object(chain_root.gen_block.call_sites, "premises", return_value=([], [], [])), \
                    patch.object(chain_root.gen_block.call_sites, "contracts", return_value={}), \
                    patch.object(chain_root.gen_block.call_sites, "call_sites", return_value={}), \
                    patch.object(chain_root, "render_successor", return_value="Definition Fixture := P."):
                rendered = chain_root.render_probe(state, block, successor)
            self.assertNotIn("instr_lookup_resources", rendered)
            self.assertIn("decodeItemSelectedCode args -∗", rendered)
            self.assertEqual(rendered.count("instr_body 0xa P."), 1)
            self.assertIn("instr_pre 0xa BLK_STOP_a -∗", rendered)
            self.assertIn("instr_pre 0x14 BLK_STOP_14 -∗", rendered)


    def test_numeric_source_preserves_recorder_blank_line(self):
        source = ("Lemma infer_boundary :\n  instr_lookup_resources -∗\n"
                  "  instr_body 0xa P.\nProof.\n"
                  "all: try zesu_enter_return_wand_if_enabled.\nall: try liShow.\nAbort.\n")
        with patch.object(chain_root.infer_boundary, "spec_source", return_value=source):
            actual = chain_root.probe_source({}, None, 20)
        self.assertIn("all: try zesu_enter_return_wand_if_enabled.\n\nall: try liShow.", actual)
