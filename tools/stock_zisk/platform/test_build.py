"""Retained tests for the platform link boundary."""
import importlib.util
from pathlib import Path
import unittest
import tempfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("platform_build", HERE / "build.py")
build = importlib.util.module_from_spec(spec); spec.loader.exec_module(build)
spec = importlib.util.spec_from_file_location("platform_traces", HERE / "traces.py")
traces = importlib.util.module_from_spec(spec); spec.loader.exec_module(traces)

class TraceCoverageTests(unittest.TestCase):
    def test_instruction_modules_match_selected_pcs(self):
        with tempfile.TemporaryDirectory() as directory:
            out=Path(directory)
            for name in ["a800d6960.v", "a800d6964.v", "instrs.v"]:
                (out/name).touch()
            self.assertEqual(traces.validate_instruction_modules(out,[0x800d6960,0x800d6964]),2)
            (out/"a800d6964.v").unlink()
            with self.assertRaisesRegex(ValueError,"missing=.*a800d6964"):
                traces.validate_instruction_modules(out,[0x800d6960,0x800d6964])
            (out/"a800d6964.v").touch(); (out/"a800d6968.v").touch()
            with self.assertRaisesRegex(ValueError,"extra=.*a800d6968"):
                traces.validate_instruction_modules(out,[0x800d6960,0x800d6964])

    def test_region_partition_requires_unique_coverage(self):
        from indexes import validate_partition
        validate_partition({"left": {1}, "right": {2}}, {1, 2})
        for regions in [{"left": {1}}, {"left": {1}, "right": {1, 2}}, {"left": {1, 2, 3}}]:
            with self.assertRaisesRegex(ValueError, "Index ownership differs"):
                validate_partition(regions, {1, 2})

    def test_native_index_checks_imports_and_entries(self):
        from indexes import validate_indexes
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            index = out / "index_region.v"
            index.write_text("Require Export Example.a1.\nDefinition instr_map := [(0x1%Z, a1)].\n")
            validate_indexes(out, {"region": {1}}, "Example")
            index.write_text("Require Export Example.a1.\nRequire Export Example.a2.\nDefinition instr_map := [(0x1%Z, a2); (0x2%Z, a1)].\n")
            with self.assertRaisesRegex(ValueError, "different instruction address"):
                validate_indexes(out, {"region": {1, 2}}, "Example")
            index.write_text("Require Export Example.a2.\nDefinition instr_map := [(0x1%Z, a1)].\n")
            with self.assertRaisesRegex(ValueError, "imports or entries differ"):
                validate_indexes(out, {"region": {1}}, "Example")

    def test_region_names_do_not_depend_on_inventory_order(self):
        import json
        from indexes import approved_regions
        inventory = json.loads(Path("build/stock-zisk/inventory.json").read_text())
        supported = {row["pc"] for function in inventory["functions"]
                     for row in function["rows"] if row["kind"] != "runtime"}
        supported |= {pc for block in inventory["inline_decodeSingleTx"]["block_ranges"]
                      for pc in range(block["start"], block["end"], 4)}
        expected = approved_regions(inventory, supported)
        inventory["functions"].reverse()
        self.assertEqual(approved_regions(inventory, supported), expected)

    def test_expected_hashes_use_actual_output_directory(self):
        import json
        from bind_traces import sha, validate_expected_files
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory) / "actual-output"
            out.mkdir()
            path = out / "index_region.v"
            path.write_text("native index")
            (out / "generation-measurement.json").write_text("variable measurement")
            manifest = Path(directory) / "manifest.json"
            manifest.write_text(json.dumps({"project_derived": {
                "generated/isla-traces/stock-zisk/closure/index_region.v":
                    {"path": "/unrelated/output/index_region.v", "sha256": sha(path)}}}))
            validate_expected_files(out, manifest, "closure")
            path.write_text("changed index")
            with self.assertRaisesRegex(ValueError, "differs from the manifest"):
                validate_expected_files(out, manifest, "closure")

    def test_byte_and_cfg_exports_reject_changed_data(self):
        from exports import make_commitment, append_exports, validate_exports
        import hashlib
        rows = [{"pc": 8, "size": 4, "word": 0x05060708},
                {"pc": 4, "size": 4, "word": 0x01020304}]
        commitment = make_commitment(rows, [(4, 8), (8, 4)], [])
        self.assertEqual(commitment["instruction_bytes_sha256"],
                         hashlib.sha256(bytes.fromhex("0403020108070605")).hexdigest())
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "instrs.v"
            path.write_text("Native index.\n")
            append_exports(path, "region", commitment)
            validate_exports(path, "region", commitment)
            path.write_text(path.read_text().replace("(0x4%Z, 0x8%Z)", "(0x4%Z, 0xc%Z)"))
            with self.assertRaisesRegex(ValueError, "exports differ"):
                validate_exports(path, "region", commitment)
        with self.assertRaisesRegex(ValueError, "repeats an address"):
            make_commitment(rows + [rows[0]], [], [])

    def test_cfg_separates_calls_from_edges_and_exits(self):
        from exports import cfg_edges
        rows = [{"pc": 4, "size": 4, "kind": "call", "target": 100},
                {"pc": 8, "size": 4, "kind": "branch", "target": 4},
                {"pc": 12, "size": 4, "kind": "return"}]
        edges, exits, calls = cfg_edges(rows, {4, 8, 12})
        self.assertEqual(edges, [(8, 4), (8, 12)])
        self.assertEqual(exits, [{"pc": "0xc", "kind": "return", "target": None}])
        self.assertEqual(calls, [{"pc": "0x4", "callee": {"kind": "entry", "identity": "0x64"}, "continuation": "0x8"}])

    def test_cfg_resolves_table_targets_and_preserves_region_edges(self):
        from exports import cfg_edges
        rows = [{"pc": 4, "size": 4, "kind": "indirect",
                 "resolution": "checked table bytes", "successors": [8, 12]},
                {"pc": 8, "size": 4, "kind": "jump", "target": 16}]
        edges, exits, calls = cfg_edges(rows, {4, 8, 12})
        self.assertEqual(edges, [(4, 8), (4, 12)])
        self.assertEqual(exits, [{"pc": "0x8", "kind": "tail", "target": "0x10"}])
        self.assertEqual(calls, [])

    def test_cfg_binds_selected_vtable_slot(self):
        from exports import cfg_edges
        row = {"pc": 4, "size": 4, "kind": "call", "target": 100,
               "resolution": "selected allocator vtable under the stated entry condition"}
        self.assertEqual(cfg_edges([row], {4, 8}, {100: 200})[2][0]["callee"],
                         {"kind": "vtable-slot", "identity": "0xc8"})
        with self.assertRaisesRegex(ValueError, "slot is absent"):
            cfg_edges([row], {4, 8})

    def test_manifest_commitment_change_fails(self):
        import copy, json
        from bind_traces import validate_expected_commitments
        from exports import make_commitment
        commitment = {"sample": make_commitment([{"pc": 4, "size": 4, "word": 1}], [(4, 8)], [],
            [{"pc": "0x8", "callee": {"kind": "entry", "identity": "0x10"}, "continuation": "0xc"}])}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "manifest.json"
            path.write_text(json.dumps({"traces": {"closure": {"commitments": commitment}}}))
            validate_expected_commitments(commitment, path, "closure")
            for field in ["instruction_bytes_sha256", "instruction_bytes", "cfg_edges", "call_sites"]:
                changed = copy.deepcopy(commitment)
                changed["sample"][field] = "changed"
                path.write_text(json.dumps({"traces": {"closure": {"commitments": changed}}}))
                with self.assertRaisesRegex(ValueError, "commitments differ"):
                    validate_expected_commitments(commitment, path, "closure")

    def test_refused_runtime_keeps_bytes_and_has_no_cfg_edge(self):
        from exports import make_commitment, cfg_edges
        rows = [{"pc": 4, "size": 4, "word": 0x8135a073, "kind": "runtime"},
                {"pc": 8, "size": 4, "word": 0x00c50033, "kind": "plain"},
                {"pc": 12, "size": 4, "word": 0x00008067, "kind": "return"}]
        edges, exits, calls = cfg_edges(rows, {4, 8, 12})
        commitment = make_commitment(rows, edges, exits, calls)
        self.assertEqual(len(commitment["instruction_bytes"]), 3)
        self.assertEqual(commitment["instruction_bytes"][0]["bytes"], "73a03581")
        self.assertEqual(edges, [(8, 12)])
        self.assertEqual(exits, [{"pc": "0xc", "kind": "return", "target": None}])

    def test_exports_use_one_pure_theory(self):
        from exports import make_commitment, render_exports
        text = render_exports("sample", make_commitment([], [], []))
        self.assertIn("Require Import ZesuStock.CalleeIdentity.", text)
        self.assertNotIn("ZesuSsz.CalleeIdentity", text)

    def test_generated_theory_uses_stock_dependency(self):
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            dune = out / "dune"
            dune.write_text("(theories isla isla.riscv64 lithium iris stdpp RecordUpdate Ltac2 ZesuSsz.CalleeIdentity)")
            traces.ensure_callee_theory(out)
            self.assertIn("Ltac2 ZesuStock)", dune.read_text())
            self.assertNotIn("ZesuSsz.CalleeIdentity", dune.read_text())

class LinkTests(unittest.TestCase):
    def setUp(self):
        self.base = Path("/home/cody/isla-snapshots/riscv64.ir").read_text()
        self.adapter = Path("build/stock-zisk/platform/adapter.ir").read_text()
    def test_only_platform_bodies_change(self):
        result, report = build.link(self.base, self.adapter)
        self.assertTrue(report["non_platform_declarations_byte_identical"])
        before, after = build.functions(self.base), build.functions(result)
        self.assertEqual(set(after) - set(before), set(build.ADDED))
        for name in before.keys() - set(build.HOOKS):
            self.assertEqual(before[name], after[name])
    def test_modified_instruction_model_fails(self):
        with self.assertRaisesRegex(ValueError, "base snapshot hash"):
            build.link(self.base.replace("fn zexecute(", "fn zexecute_changed(", 1), self.adapter)
    def test_missing_hook_fails(self):
        with self.assertRaisesRegex(ValueError, "Missing platform hook"):
            build.link(self.base, self.adapter.replace("fn zchecked_mem_read(", "fn zchanged(", 1))

if __name__ == "__main__": unittest.main()
