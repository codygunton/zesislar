"""Check selected aliases without regenerating instruction semantics."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from exports import make_commitment, native_prefix, render_exports
from function_binding import bind, prepare
import function_binding
from indexes import validate_indexes


class FunctionBindingTests(unittest.TestCase):
    def fixture(self, root):
        source = root / "generated/isla-traces/stock-zisk/closure"
        source.mkdir(parents=True)
        elf = root / "build/stock-zisk/zesu-zisk.elf"
        elf.parent.mkdir(parents=True)
        elf.write_bytes(b"synthetic ELF")
        platform = root / "build/stock-zisk/platform/riscv64-zisk.ir"
        platform.parent.mkdir()
        platform.write_text("synthetic platform")
        config = root / "ZesuSsz/riscv64_zesu.toml"
        config.parent.mkdir()
        config.write_text("synthetic configuration")
        rows = [{"pc": 0x1000, "word": 0x13, "size": 4},
                {"pc": 0x1004, "word": 0x8067, "size": 4}]
        digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
        inventory = {"elf_sha256": digest(elf), "functions": [
            {"name": "alt_fl_alloc.free", "rows": rows}]}
        (elf.parent / "inventory.json").write_text(json.dumps(inventory))
        commitment = make_commitment(rows, [(0x1000, 0x1004)],
                                     [{"pc": "0x1004", "kind": "return", "target": None}])
        commitment.update(function="alt_fl_alloc.free", unmodeled_instruction_pcs=[])
        prefix = ("Require Export Trace.a1000.\nRequire Export Trace.a1004.\n"
                  "Definition instr_map := [(0x1000%Z, a1000); (0x1004%Z, a1004)].\n")
        index = source / "index_allocatorFree.v"
        index.write_text(prefix + render_exports("allocatorFree", commitment))
        for pc in (0x1000, 0x1004):
            for suffix in ("v", "isla"):
                (source / f"a{pc:x}.{suffix}").write_text(f"synthetic {pc:x} {suffix}")
        coverage = {"elf_sha256": digest(elf), "platform_snapshot_sha256": digest(platform),
                    "config_sha256": digest(config), "indexes": {"coqdir": "Trace",
                    "regions": {"allocatorFree": ["0x1000", "0x1004"]}},
                    "commitments": {"allocatorFree": commitment},
                    "files": {path.name: digest(path) for path in source.iterdir()}}
        (source / "coverage.json").write_text(json.dumps(coverage))
        return source, index

    def test_selected_index_keeps_exact_native_map_and_uses_named_exports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, index = self.fixture(root)
            report = bind(root, source, "alt_fl_alloc.free", "free")
            output = root / "generated/isla-traces/stock-zisk/free/index_free.v"
            self.assertEqual(native_prefix(output.read_text()), native_prefix(index.read_text()))
            self.assertIn("Definition free_cfg_step", output.read_text())
            self.assertEqual(report["instruction_count"], 2)
            code = root / "ZesuSsz/Contracts/FreeSelected.v"
            self.assertIn("Definition freeSelectedCode", code.read_text())
            self.assertNotIn("IslarisContractCorrect", code.read_text())
            self.assertEqual(bind(root, source, "alt_fl_alloc.free", "free", check=True), report)

    def test_mismatched_elf_and_incomplete_selected_index_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, _ = self.fixture(root)
            coverage_path = source / "coverage.json"
            coverage = json.loads(coverage_path.read_text())
            coverage["indexes"]["regions"]["allocatorFree"].pop()
            coverage_path.write_text(json.dumps(coverage))
            with self.assertRaisesRegex(ValueError, "complete selected function"):
                prepare(root, source, "alt_fl_alloc.free", "free")
            coverage["elf_sha256"] = "wrong"
            coverage_path.write_text(json.dumps(coverage))
            with self.assertRaisesRegex(ValueError, "different ELF"):
                prepare(root, source, "alt_fl_alloc.free", "free")

    def test_original_checker_receives_only_the_selected_index_symlink(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, index = self.fixture(root)
            (source / "index_unrelated.v").write_text("Unrelated retained source.")
            checked = []

            def validate(selected, regions, namespace):
                self.assertEqual([path.name for path in selected.iterdir()], [index.name])
                self.assertTrue((selected / index.name).is_symlink())
                self.assertEqual((selected / index.name).resolve(), index)
                self.assertEqual(regions, {"allocatorFree": {0x1000, 0x1004}})
                self.assertEqual(namespace, "Trace")
                validate_indexes(selected, regions, namespace)
                checked.append(selected)

            with patch.object(function_binding, "validate_indexes", side_effect=validate):
                prepare(root, source, "alt_fl_alloc.free", "free")
            self.assertEqual(len(checked), 1)
            self.assertFalse(checked[0].exists())
            self.assertEqual((source / "index_unrelated.v").read_text(), "Unrelated retained source.")

    def test_original_checker_rejects_a_wrong_selected_index_reference(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, index = self.fixture(root)
            index.write_text(index.read_text().replace("(0x1004%Z, a1004)",
                                                       "(0x1004%Z, a1000)"))
            with self.assertRaisesRegex(ValueError, "different instruction address"):
                prepare(root, source, "alt_fl_alloc.free", "free")

    def test_selected_cli_binds_actual_sources_and_rejects_stale_report(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, _ = self.fixture(root)
            repository = Path(__file__).resolve().parents[3]
            wrapper = Path("tools/stock_zisk/selected/bind_traces.py")
            sources = [wrapper, *(Path("tools/stock_zisk/platform") / name for name in
                        ("function_binding.py", "indexes.py", "exports.py"))]
            for relative in sources:
                destination = root / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(repository / relative, destination)
            command = [sys.executable, str(root / wrapper), "--out", str(source),
                       "--function", "alt_fl_alloc.free", "--trace-name", "free"]
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            report = root / "generated/isla-traces/stock-zisk/free/function-binding.json"
            contents = json.loads(report.read_text())
            self.assertEqual(contents["generator_sources"], {
                str(relative): hashlib.sha256((root / relative).read_bytes()).hexdigest()
                for relative in sources})
            result = subprocess.run([*command, "--check"], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            contents["generator_sources"][str(wrapper)] = "0" * 64
            report.write_text(json.dumps(contents))
            result = subprocess.run([*command, "--check"], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("binding report is stale", result.stderr)

    def test_fresh_and_repeated_binding_preserve_existing_datasets(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, _ = self.fixture(root)
            decode = source.parent / "decodeItem"
            decode.mkdir()
            (decode / "instrs.v").write_text("Retained DecodeItem instructions.\n")
            retained = {path: path.read_bytes() for folder in (source, decode)
                        for path in folder.rglob("*") if path.is_file()}
            first = bind(root, source, "alt_fl_alloc.free", "free")
            for _ in range(2):
                self.assertEqual(bind(root, source, "alt_fl_alloc.free", "free"), first)
                self.assertEqual(bind(root, source, "alt_fl_alloc.free", "free", check=True), first)
            for path, original in retained.items():
                self.assertEqual(path.read_bytes(), original, str(path))

    def test_changed_selected_instruction_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, _ = self.fixture(root)
            (source / "a1000.v").write_text("changed")
            with self.assertRaisesRegex(ValueError, "instruction module changed"):
                prepare(root, source, "alt_fl_alloc.free", "free")

    def test_existing_foreign_selected_source_is_preserved_before_any_write(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, _ = self.fixture(root)
            selected = root / "ZesuSsz/Contracts/FreeSelected.v"
            selected.parent.mkdir()
            selected.write_text("owned by another source")
            with self.assertRaisesRegex(ValueError, "different existing source"):
                bind(root, source, "alt_fl_alloc.free", "free")
            self.assertEqual(selected.read_text(), "owned by another source")
            self.assertFalse((root / "generated/isla-traces/stock-zisk/free/index_free.v").exists())

    def test_output_cannot_replace_the_closure_or_leave_its_parent(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, _ = self.fixture(root)
            with self.assertRaisesRegex(ValueError, "not replace"):
                prepare(root, source, "alt_fl_alloc.free", "closure")
            with self.assertRaisesRegex(ValueError, "not an identifier"):
                prepare(root, source, "alt_fl_alloc.free", "../outside")


if __name__ == "__main__":
    unittest.main()
