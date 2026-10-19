"""Check contract preservation, switch isolation, and diagnostic classification."""
import sys
import tempfile
import unittest
from unittest.mock import patch
import json
from types import SimpleNamespace
from unittest.mock import patch

from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
import rule_compare

SOURCE = '''Require Import All.
Require Import Approved.
Definition entry := True.
Lemma helper : True.
Proof.
  exact I.
Qed.
Lemma DesignedBoundary_800d6a38 (n : nat) : n = n.
Proof.
  reflexivity.
Qed.
Print Assumptions DesignedBoundary_800d6a38.
'''
GOAL = '''CHAIN-GOAL-BEGIN active
CHAIN-GOAL-ENV coq CHAIN-FIELD-END
CHAIN-GOAL-CONCLUSION (exists n : nat, n = 0) CHAIN-FIELD-END
CHAIN-GOAL-END
'''
RETURNED = 'RULE-COMPARE-BEGIN\nRULE-COMPARE-RETURNED\n'
INCOMPLETE = 'Error: (in proof DesignedBoundary_800d6a38): Attempt to save an incomplete proof\n'
COMPILER = {"limit": None, "policy_error": None, "compiled_object": None}


class GenerationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.workspace = Path(self.temp.name)
        (self.workspace / "Approved.v").write_text(
            'Require Export Switch.\n')
        (self.workspace / "Switch.v").write_text(
            '#[export] Instance enabled : TestSwitch := I.\n')
        self.module = self.workspace / "Block.v"
        self.module.write_text(SOURCE)

    def prepare(self, **kwargs):
        return rule_compare.prepare(self.module, self.workspace, "TestSwitch", **kwargs)

    def test_preserves_statement_imports_and_helper(self):
        prepared = self.prepare()
        for source in prepared["copies"].values():
            self.assertIn(prepared["statement"], source)
            self.assertEqual(list(rule_compare.imported_modules(source)), ["All", "Approved"])
            self.assertIn('Lemma helper : True.\nProof.\n  exact I.\nQed.', source)
            self.assertIn('  zesu_block.\n', source)
        self.assertEqual(self.module.read_text(), SOURCE)

    def test_canonical_arms_retain_approved_instance_only_in_on(self):
        prepared = self.prepare()
        self.assertEqual(prepared["existing_instances"], ["Switch.enabled"])
        self.assertIn('Remove Hints Switch.enabled : typeclass_instances.', prepared["copies"]["rule_off"])
        self.assertNotIn('Remove Hints', prepared["copies"]["rule_on"])
        self.assertNotIn('#[local] Instance', prepared["copies"]["rule_on"])
        self.assertNotIn('#[local] Instance', prepared["copies"]["rule_off"])
        self.assertIn('Fail Definition rule_compare_switch_probe', prepared["copies"]["rule_off"])
        self.assertNotIn('Fail Definition', prepared["copies"]["rule_on"])
        self.assertEqual(prepared["arm_instances"]["rule_on"],
                         {"removals": [], "local_additions": [], "expected_enabled": True})
        self.assertEqual(prepared["arm_instances"]["rule_off"]["removals"], ["Switch.enabled"])

    def test_empty_record_switch_instance_is_removed_only_from_off(self):
        (self.workspace / "Switch.v").write_text(
            '#[export] Instance enabled : TestSwitch := {}.\n')
        prepared = self.prepare()
        self.assertEqual(prepared["existing_instances"], ["Switch.enabled"])
        self.assertIn('Remove Hints Switch.enabled : typeclass_instances.',
                      prepared["copies"]["rule_off"])
        self.assertNotIn('Remove Hints', prepared["copies"]["rule_on"])
        self.assertNotIn('#[local] Instance', prepared["copies"]["rule_on"])

    def test_future_switch_absent_from_approved_uses_only_local_on_instance(self):
        (self.workspace / "Switch.v").write_text('Class TestSwitch : Prop := constructor : True.\n')
        prepared = self.prepare()
        self.assertEqual(prepared["existing_instances"], [])
        self.assertIn('#[local] Instance : TestSwitch := I.', prepared["copies"]["rule_on"])
        self.assertNotIn('#[local] Instance', prepared["copies"]["rule_off"])
        self.assertEqual(prepared["arm_instances"]["rule_on"]["local_additions"],
                         ['#[local] Instance : TestSwitch := I.'])
        self.assertEqual(prepared["arm_instances"]["rule_off"]["removals"], [])

    def test_finds_all_instances_and_import_cycle(self):
        (self.workspace / "Switch.v").write_text(
            'Require Import Approved.\n'
            '#[export] Instance first : TestSwitch := I.\n'
            '#[export] Instance second : TestSwitch := I.\n')
        prepared = self.prepare()
        self.assertEqual(prepared["existing_instances"], ["Switch.first", "Switch.second"])
        self.assertEqual(prepared["arm_instances"]["rule_off"]["removals"],
                         ["Switch.first", "Switch.second"])
        self.assertEqual(prepared["arm_instances"]["rule_on"]["removals"], [])

    def test_ignores_commented_instances_and_imports(self):
        (self.workspace / "Switch.v").write_text(
            '(* Require Import Missing. (* nested *)\n'
            'Instance fake : TestSwitch := I. *)\n'
            '#[export] Instance enabled : TestSwitch := I.\n')
        self.assertEqual(self.prepare()["existing_instances"], ["Switch.enabled"])

    def test_optional_lemma_is_one_line(self):
        prepared = self.prepare(keyed_lemma="Facts.keyed")
        for source in prepared["copies"].values():
            self.assertEqual(source.count('  apply Facts.keyed.\n'), 1)
            for marker in ('RULE-COMPARE-AUTOMATIC-RETURNED', 'RULE-COMPARE-KEYED-BEGIN', 'RULE-COMPARE-KEYED-RETURNED'):
                self.assertIn('  all: idtac "' + marker + '".', source)
            self.assertLess(source.index('  zesu_block.'), source.index('RULE-COMPARE-AUTOMATIC-RETURNED'))
            self.assertLess(source.index('RULE-COMPARE-KEYED-BEGIN'), source.index('  apply Facts.keyed.'))
            self.assertLess(source.index('  apply Facts.keyed.'), source.index('RULE-COMPARE-KEYED-RETURNED'))
        with self.assertRaises(ValueError):
            self.prepare(keyed_lemma="Facts.keyed. admit.")

    def test_missing_or_ambiguous_main_proof_rejects(self):
        with self.assertRaises(ValueError):
            self.prepare(lemma="absent")
        self.module.write_text(SOURCE + 'Lemma DesignedBoundary_other : True.\nProof.\nexact I.\nQed.\n')
        with self.assertRaises(ValueError):
            self.prepare()

    def test_aborted_source_rejects(self):
        self.module.write_text(SOURCE.replace('  reflexivity.\nQed.', '  reflexivity.\nAbort.'))
        with self.assertRaises(ValueError):
            self.prepare()

    def test_records_shelf_targets_after_unshelve(self):
        for source in self.prepare()["copies"].values():
            self.assertIn('  Unshelve.\n  all: idtac "RULE-COMPARE-RETURNED".', source)
            self.assertIn('chain_print_goal "shelved"', source)


class ClassificationTests(unittest.TestCase):
    def test_incomplete_proof_with_complete_goal_is_residual(self):
        result = rule_compare.classify(1, RETURNED + GOAL + INCOMPLETE, COMPILER)
        self.assertEqual(result["outcome"], "residual:existential")
        self.assertEqual(result["first_residual"]["conclusion"], '(exists n : nat, n = 0)')

    def test_missing_import_is_setup_error(self):
        result = rule_compare.classify(1, 'Error: Cannot find a physical path bound to All.', COMPILER)
        self.assertEqual(result["outcome"], "setup-error")
        self.assertIsNone(result["first_residual"])

    def test_missing_recipe_is_setup_error(self):
        self.assertEqual(rule_compare.classify(2, 'no compiler recipe', None)["outcome"], "setup-error")

    def test_arbitrary_compiler_error_is_not_residual(self):
        result = rule_compare.classify(1, RETURNED + GOAL + 'Error: unknown reference.', COMPILER)
        self.assertEqual(result["outcome"], "compiler-error")
        self.assertIsNone(result["first_residual"])

    def test_tactic_failure_is_not_residual(self):
        result = rule_compare.classify(1, 'RULE-COMPARE-BEGIN\nError: Tactic failure.', COMPILER)
        self.assertEqual(result["outcome"], "tactic-error")

    def test_truncated_capture_is_not_residual(self):
        result = rule_compare.classify(1, RETURNED + 'CHAIN-GOAL-BEGIN active\n' + INCOMPLETE, COMPILER)
        self.assertEqual(result["outcome"], "capture-error")

    def test_resource_stop_is_not_residual(self):
        result = rule_compare.classify(1, RETURNED + GOAL + INCOMPLETE, {**COMPILER, "limit": "memory"})
        self.assertEqual(result["outcome"], "runtime-error")

    def test_shelf_only_residual_uses_complete_post_unshelve_target(self):
        shelf = GOAL.replace('CHAIN-GOAL-BEGIN active', 'CHAIN-GOAL-BEGIN shelved')
        result = rule_compare.classify(1, RETURNED + shelf + INCOMPLETE, COMPILER)
        self.assertEqual(result["outcome"], "residual:existential")
        self.assertEqual(result["first_residual"]["phase"], "post-unshelve")
        self.assertEqual(result["first_residual"]["conclusion"], '(exists n : nat, n = 0)')

    def test_legacy_shelf_only_record_marks_targets_unavailable(self):
        output = ('RULE-COMPARE-BEGIN\nExistential 1 = ?pending\n'
                  'Chars 100 - 118 [Show~Existentials.] 0. secs\n' + INCOMPLETE)
        result = rule_compare.classify(1, output, COMPILER)
        self.assertEqual(result["outcome"], "residual:shelved-unavailable")
        self.assertIsNone(result["first_residual"]["conclusion"])

    def test_other_theorem_qed_failure_is_not_target_residual(self):
        result = rule_compare.classify(1, RETURNED + GOAL + INCOMPLETE,
                                       COMPILER, lemma="another_theorem")
        self.assertEqual(result["outcome"], "compiler-error")

    def test_closure_requires_object_and_empty_assumptions(self):
        closed = {**COMPILER, "compiled_object": {"path": "candidate.vo"}}
        self.assertEqual(rule_compare.classify(0, 'RULE-COMPARE-BEGIN\nClosed under the global context', closed)["outcome"], "closed")
        result = rule_compare.classify(0, RETURNED + 'Axioms:\nfixture : False', closed)
        self.assertEqual(result["outcome"], "compiler-error")


class NoTraceTests(unittest.TestCase):
    def test_cli_defaults_to_no_trace_and_accepts_explicit_flag(self):
        import contextlib
        import io
        result = {"comparison_success": True, "arms": {}}
        for flags in ([], ["--no-trace"]):
            with self.subTest(flags=flags), \
                    patch.object(sys, "argv", ["rule_compare.py", "Block.v", "TestSwitch",
                         "--build-dir", "_build/private", "--out", "_build/compare",
                         "--schema", "schema.json", *flags]), \
                    patch.object(rule_compare, "compare", return_value=result) as compare, \
                    patch.dict(sys.modules, {"trace_block": None, "trace_block_mcp": None}), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(rule_compare.main(), 0)
                self.assertTrue(compare.call_args.kwargs["no_trace"])

    def test_no_trace_requires_valid_compiler_outcomes(self):
        arms = {arm: {"outcome": "residual:memory"}
                for arm in ("rule_off", "rule_on")}
        self.assertTrue(rule_compare.comparison_complete(arms, no_trace=True))
        self.assertFalse(rule_compare.comparison_complete(arms))
        arms["rule_on"]["outcome"] = "setup-error"
        self.assertFalse(rule_compare.comparison_complete(arms, no_trace=True))

    def test_compare_writes_outputs_without_trace_imports(self):
        import builtins
        with tempfile.TemporaryDirectory() as directory:
            workspace = Path(directory)
            module = workspace / "Block.v"
            module.write_text(SOURCE)
            build = workspace / "_build" / "private"
            build.mkdir(parents=True)
            (build / "coqc-ocamlpath.json").write_text(json.dumps({
                "workspace": str(workspace), "private_build": str(build),
                "OCAMLPATH": "/test/findlib"}))
            schema = workspace / "schema.json"
            schema.write_text(json.dumps({"block_record_schema": dict.fromkeys(
                ["slot", "hand_lines", "rule_on", "rule_off", "seconds",
                 "peak_gib", "mcp_record"])}))
            out = workspace / "_build" / "comparison"
            original_import = builtins.__import__

            def without_trace(name, *args, **kwargs):
                if name.startswith("trace_block"):
                    raise AssertionError("A no-trace comparison imported trace tools.")
                return original_import(name, *args, **kwargs)

            def snapshot(build, destination):
                destination.write_text("{}")
                return rule_compare.digest(destination)

            def compile_source(source, directory, build, *, policy):
                log = directory / "compiler.log"
                output = RETURNED + GOAL + INCOMPLETE
                log.write_text(output)
                compiler = {**COMPILER, "cpu_seconds": 1.5,
                            "peak_rss_kib": 1024}
                return SimpleNamespace(returncode=1), output, log, compiler, 2.0

            with patch.object(rule_compare, "__file__", str(workspace / "tools/block/rule_compare.py")), \
                    patch.object(rule_compare, "snapshot_recipe", side_effect=snapshot), \
                    patch.object(rule_compare.subprocess, "check_output", return_value="a" * 40), \
                    patch.object(rule_compare.coqc_primary, "compile_source", side_effect=compile_source), \
                    patch.dict(rule_compare.os.environ), \
                    patch("builtins.__import__", side_effect=without_trace):
                report = rule_compare.compare(module, "TestSwitch", build, out,
                                              schema)
            self.assertTrue(report["comparison_success"])
            self.assertFalse(report["trace_coverage_complete"])
            self.assertEqual(json.loads((out / "report.json").read_text()), report)
            metrics = json.loads((out / "metrics.json").read_text())
            self.assertEqual(metrics["rule_on"], "residual:existential")
            self.assertEqual(metrics["rule_off"], "residual:existential")
            self.assertEqual(metrics["seconds"], 1.5)
            for arm in report["arms"].values():
                self.assertTrue(arm["trace"]["skipped"])
                self.assertFalse(arm["trace"]["complete"])


class TraceIntegrationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.workspace = Path(self.temp.name)
        self.out = self.workspace / "_build" / "compare"
        self.out.mkdir(parents=True)
        self.prepared = {"lemma": "DesignedBoundary_1000", "statement_sha256": "c" * 64,
                         "arm_instances": {
                             "rule_off": {"removals": ["Switch.enabled"], "local_additions": [], "expected_enabled": False},
                             "rule_on": {"removals": [], "local_additions": [], "expected_enabled": True}}}
        self.calls = []

    def row(self, arm, outcome="residual:memory"):
        directory = self.out / arm
        directory.mkdir(exist_ok=True)
        source = directory / "Block.v"
        source.write_text(SOURCE + "(* " + arm + " *)\n")
        return {"source": str(source), "source_sha256": rule_compare.digest(source), "outcome": outcome}

    def runner(self, row, *, mutate=None, status=None, automatic_closed=None):
        # Use the serializer fixture. This mock runs no compiler or MCP operation.
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        from test_trace_block import fixture
        import trace_block
        def run(arguments):
            self.calls.append(arguments)
            args = trace_block.make_parser().parse_args(arguments)
            closed = row["outcome"] == "closed" if automatic_closed is None else automatic_closed
            request, result = fixture("return" if closed else "store")
            rule = args.rules[0]["name"]
            point = result["points"][0]
            point["trigger"]["rule"] = rule
            result["coverage"]["entry_events"] = {rule: 1}
            result["coverage"]["captured_events"] = {rule: 1}
            result["identity"]["source_sha256"] = row["source_sha256"]
            result["identity"]["statement_sha256"] = self.prepared["statement_sha256"]
            result["identity"]["switches"] = {"actual_instances": ["Switch.enabled"] if args.rules[0]["enabled"] else []}
            request.update(block_pc=args.block, rule_set=args.rules, stop=args.stop,
                           scope={"root": "a" * 40, "source": Path(row["source"]).relative_to(args.workspace).as_posix(),
                                  "source_sha256": row["source_sha256"], "statement_sha256": self.prepared["statement_sha256"]})
            result["identity"]["source"] = request["scope"]["source"]
            if "final_obligations" in result["completion"]:
                result["completion"]["final_obligations"]["session"] = trace_block.logical_session_id(request)
            if mutate:
                mutate(request, result)
            trace = trace_block.build_trace(request, result)
            trace_block.write_bundle(args.out, trace)
            return status if status is not None else (0 if trace["completion"]["trace_complete"] else 1)
        return run

    def capture(self, row, arm="rule_on", runner=None, keyed_lemma=None):
        return rule_compare.capture_arm_trace(
            row, arm=arm, workspace=self.workspace, root="a" * 40, block="1000",
            switch="ZesuSsz.Automation.ReturnRoute.ZesuStepReturnRoute",
            prepared=self.prepared, out=self.out, runner=runner or self.runner(row), keyed_lemma=keyed_lemma)

    def test_failing_arm_requests_residual_and_links_every_selected_entry(self):
        row = self.row("rule_on")
        record = self.capture(row)
        self.assertTrue(record["complete"], record["errors"])
        self.assertEqual(record["requested_stop"], "residual")
        self.assertEqual(record["links"]["residual"], "rule_on/trace/TRACE.json#/residual")
        self.assertEqual(record["links"]["selected_triggers"]["ReturnRoute"],
                         ["rule_on/trace/TRACE.json#/points/0"])
        self.assertEqual(record["source_scope"]["source_sha256"], row["source_sha256"])
        self.assertEqual(record["source_scope"]["instance_changes"], self.prepared["arm_instances"]["rule_on"])

    def test_closed_arm_requests_rule_trigger_and_retains_qed(self):
        row = self.row("rule_on", "closed")
        record = self.capture(row)
        self.assertTrue(record["complete"], record["errors"])
        self.assertEqual(record["requested_stop"], "rule:ReturnRoute")
        self.assertIsNone(record["links"]["residual"])

    def test_off_scope_keeps_its_exact_source_and_switch_assignment(self):
        row = self.row("rule_off")
        record = self.capture(row, arm="rule_off")
        self.assertTrue(record["complete"], record["errors"])
        self.assertIn("ReturnRoute=off", self.calls[0])
        self.assertEqual(record["source_scope"]["instance_changes"]["removals"], ["Switch.enabled"])
        self.assertEqual(record["source_scope"]["rule_set"], [{"name": "ReturnRoute", "enabled": False}])

    def test_incomplete_mock_backend_blocks_comparison_without_erasing_outcome(self):
        row = self.row("rule_on")
        run = self.runner(row, mutate=lambda request, result: result["coverage"].update(required_complete=False))
        row["trace"] = self.capture(row, runner=run)
        self.assertFalse(row["trace"]["complete"])
        self.assertFalse(rule_compare.comparison_complete({"rule_on": row}))
        self.assertEqual(row["outcome"], "residual:memory")
        self.assertIsNotNone(row["trace"]["links"]["residual"])

    def test_completeness_flag_alone_does_not_validate_a_trace(self):
        row = self.row("rule_on")
        original = self.runner(row)
        def run(arguments):
            original(arguments)
            path = Path(arguments[arguments.index("--out") + 1]) / "TRACE.json"
            import json
            trace = json.loads(path.read_text())
            trace["points"][0]["evars"].pop("entries")
            path.write_text(json.dumps(trace))
            return 0
        record = self.capture(row, runner=run)
        self.assertFalse(record["complete"])
        self.assertTrue(any("Evd" in error for error in record["errors"]))

    def test_wrong_source_switch_or_statement_cannot_supply_arm_evidence(self):
        changes = [lambda request, result: result["identity"].update(source_sha256="0" * 64),
                   lambda request, result: result["identity"].update(statement_sha256="0" * 64),
                   lambda request, result: request.update(rule_set=[{"name": "ReturnRoute", "enabled": False}])]
        for index, change in enumerate(changes):
            with self.subTest(index=index):
                row = self.row("rule_on")
                directory = Path(row["source"]).parent / "trace"
                if directory.exists():
                    import shutil
                    shutil.rmtree(directory)
                record = self.capture(row, runner=self.runner(row, mutate=change))
                self.assertFalse(record["complete"])
                self.assertTrue(any("different" in error for error in record["errors"]))

    def test_missing_measured_switch_instances_blocks_coverage(self):
        row = self.row("rule_on")
        record = self.capture(row, runner=self.runner(row,
            mutate=lambda request, result: result["identity"].pop("switches")))
        self.assertFalse(record["complete"])
        self.assertTrue(any("measured switch" in error for error in record["errors"]))

    def test_stale_markdown_cannot_supply_complete_trace_links(self):
        row = self.row("rule_on")
        original = self.runner(row)
        def run(arguments):
            original(arguments)
            directory = Path(arguments[arguments.index("--out") + 1])
            (directory / "TRACE.md").write_text("missing points")
            return 0
        record = self.capture(row, runner=run)
        self.assertFalse(record["complete"])
        self.assertTrue(any("Markdown" in error for error in record["errors"]))

    def test_failing_arm_requires_a_residual_even_if_trace_closes(self):
        row = self.row("rule_on")
        def close(request, result):
            result["residual"] = None
            result["coverage"]["traversal"] = "proof-closed"
            result["completion"].update(proof_closed=True, closure_check={
                "command": "Qed.", "accepted": True, "unresolved_evars": False})
        record = self.capture(row, runner=self.runner(row, mutate=close))
        self.assertFalse(record["complete"])
        self.assertTrue(any("residual trace link" in error for error in record["errors"]))

    def test_missing_bundle_or_invalid_generator_call_blocks_coverage(self):
        row = self.row("rule_on")
        record = self.capture(row, runner=lambda arguments: 1)
        self.assertFalse(record["complete"])
        self.assertEqual(len(record["errors"]), 2)
        def invalid(arguments):
            raise SystemExit(2)
        record = self.capture(row, runner=invalid)
        self.assertFalse(record["complete"])
        self.assertIn("SystemExit", record["errors"][0])
        def startup_failure(arguments):
            raise RuntimeError("owned transport setup failed")
        record = self.capture(row, runner=startup_failure)
        self.assertFalse(record["complete"])
        self.assertIn("owned transport setup failed", record["errors"][0])

    def test_fully_observed_absent_trigger_is_not_missing_coverage(self):
        row = self.row("rule_on", "closed")
        def absent(request, result):
            result["points"] = []
            result["coverage"].update(entry_events={"ReturnRoute": 0},
                captured_events={"ReturnRoute": 0}, requested_trigger="not-occurred")
        record = self.capture(row, runner=self.runner(row, mutate=absent))
        self.assertTrue(record["complete"], record["errors"])
        self.assertEqual(record["links"]["selected_triggers"]["ReturnRoute"], [])

    def test_compiler_outcome_without_trace_never_completes_comparison(self):
        self.assertFalse(rule_compare.comparison_complete({"rule_on": {"outcome": "closed"}}))
        complete = {"outcome": "closed", "trace": {"complete": True}}
        self.assertFalse(rule_compare.comparison_complete({"rule_on": complete}))
        self.assertFalse(rule_compare.comparison_complete({}))
        self.assertTrue(rule_compare.comparison_complete({"rule_off": complete, "rule_on": complete}))

    def test_compare_writes_incomplete_rows_and_withholds_metrics(self):
        workspace = Path(rule_compare.__file__).resolve().parents[2]
        parent = workspace / "_build"
        parent.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=parent) as directory:
            root = Path(directory)
            build = root / "private"
            build.mkdir()
            (build / "coqc-ocamlpath.json").write_text(json.dumps({
                "workspace": str(workspace), "private_build": str(build), "OCAMLPATH": "fixture"}))
            module = root / "Block.v"
            module.write_text(SOURCE)
            schema = root / "schema.json"
            fields = ("slot", "hand_lines", "rule_on", "rule_off", "seconds", "peak_gib", "mcp_record")
            schema.write_text(json.dumps({"block_record_schema": dict.fromkeys(fields)}))
            prepared = dict(self.prepared, copies={"rule_off": SOURCE, "rule_on": SOURCE},
                            imports=[], statement="fixture", existing_instances=[], original_hand_lines=1)
            def recipe(build, path):
                path.write_text("{}")
                return rule_compare.digest(path)
            def compiler(source, directory, build, policy):
                log = directory / "compile.log"
                log.write_text("mock compiler result")
                return SimpleNamespace(returncode=1), "", log, {"cpu_seconds": 1, "peak_rss_kib": 1}, 1
            def generate(arguments):
                source = arguments[arguments.index("--source") + 1]
                row = {"source": source, "source_sha256": rule_compare.digest(source), "outcome": "residual:memory"}
                return self.runner(row, mutate=lambda request, result:
                    result["coverage"].update(required_complete=False))(arguments)
            with patch.object(rule_compare, "prepare", return_value=prepared), \
                 patch.object(rule_compare, "snapshot_recipe", side_effect=recipe), \
                 patch.object(rule_compare.coqc_primary, "compile_source", side_effect=compiler), \
                 patch.object(rule_compare, "classify", return_value={
                     "outcome": "residual:memory", "first_residual": None, "goals": []}), \
                 patch.object(rule_compare.subprocess, "check_output", return_value="a" * 40), \
                 patch.dict(rule_compare.os.environ):
                report = rule_compare.compare(module, "ZesuStepReturnRoute", build,
                    root / "comparison", schema, trace_runner=generate, no_trace=False)
            self.assertFalse(report["comparison_success"])
            self.assertFalse(report["trace_coverage_complete"])
            self.assertEqual(set(report["arms"]), {"rule_off", "rule_on"})
            self.assertFalse((root / "comparison" / "metrics.json").exists())
            for arm, row in report["arms"].items():
                self.assertEqual(row["outcome"], "residual:memory")
                self.assertFalse(row["trace"]["complete"])
                self.assertTrue((root / "comparison" / arm / "evidence.json").is_file())
                self.assertIsNotNone(row["trace"]["links"]["residual"])

    def test_keyed_compiler_closure_does_not_require_automatic_closure(self):
        row = self.row("rule_on", "closed")
        row["compiler_stages"] = dict.fromkeys(("automatic_returned", "keyed_started", "keyed_returned"), True)
        record = self.capture(row, keyed_lemma="Facts.keyed", runner=self.runner(row, automatic_closed=False))
        self.assertTrue(record["complete"], record["errors"])
        self.assertFalse(record["stages"]["automatic"]["proof_closed"])
        self.assertIsNotNone(record["stages"]["automatic"]["residual"])
        self.assertTrue(record["stages"]["keyed_continuation"]["sequence_proof_closed"])
        self.assertEqual(record["stages"]["keyed_continuation"]["command"], "apply Facts.keyed.")

    def test_keyed_closure_needs_actual_stage_markers(self):
        row = self.row("rule_on", "closed")
        record = self.capture(row, keyed_lemma="Facts.keyed", runner=self.runner(row, automatic_closed=False))
        self.assertFalse(record["complete"])
        self.assertIn("explicit keyed-stage evidence", " ".join(record["errors"]))

    def test_source_or_time_echo_cannot_supply_execution_markers(self):
        fake = 'Chars 1 - 9 [idtac "RULE-COMPARE-KEYED-RETURNED".]\n'
        self.assertFalse(any(rule_compare.compiler_stages(fake).values()))
        real = 'RULE-COMPARE-AUTOMATIC-RETURNED\nRULE-COMPARE-KEYED-BEGIN\n'
        self.assertEqual(rule_compare.compiler_stages(real),
                         {"automatic_returned": True, "keyed_started": True, "keyed_returned": False})

    def test_backend_registry_rejects_unimplemented_observer(self):
        self.assertEqual(rule_compare.trace_rule_name("ZesuStepReturnRoute"), "ReturnRoute")
        with self.assertRaisesRegex(ValueError, "no entry observer"):
            rule_compare.trace_rule_name("ZesuStepUnimplementedRule")

    def test_non_switch_identifier_has_no_invented_trace_rule(self):
        with self.assertRaisesRegex(ValueError, "no entry observer"):
            rule_compare.trace_rule_name("AnUnrelatedClass")


if __name__ == "__main__":
    unittest.main()
