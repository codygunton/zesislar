"""Check isolated trace generation without running the frontend or proofs."""
import argparse
from contextlib import ExitStack
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("trace_only_driver", HERE / "traces.py")
traces = importlib.util.module_from_spec(spec)
spec.loader.exec_module(traces)


class TraceOnlyTests(unittest.TestCase):
    def fixture(self, directory):
        root = Path(directory)
        files = {
            "tools/stock_zisk/platform/bin/isla-footprint": "platform wrapper",
            "build/stock-zisk/platform/riscv64-zisk.ir": "platform model",
            "ZesuSsz/riscv64_zesu.toml": "platform configuration",
            "tools/stock_zisk/riscv.py": "decoder identity",
            "bin/islaris": "frontend identity",
            "bin/isla-footprint": "footprint identity",
            "zesu-zisk.elf": "synthetic ELF",
            "input.dump": "4: 00000013 addi\n",
        }
        for name, text in files.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        manifest = root / "manifest.json"
        manifest.write_text(json.dumps({"elf_sha256": traces.sha(root / "zesu-zisk.elf")}))
        return root

    def argv(self, root, mode=("--trace-only",)):
        return ["traces.py", "--manifest", str(root / "manifest.json"),
                "--dump", str(root / "input.dump"), "--out", str(root / "output"),
                "--coqdir", "Example.Heldout", "--jobs", "2", *mode]

    def frontend(self, command, **kwargs):
        output = Path(command[command.index("-o") + 1])
        output.mkdir()
        for name, text in {"a4.v": "instruction definition\n", "a4.isla": "Isla trace\n",
                           "instrs.v": "native instruction index\n", "dune": "native theory\n"}.items():
            (output / name).write_text(text)
        return argparse.Namespace(returncode=0)

    def context(self, stack, root, frontend=None, mode=("--trace-only",)):
        stack.enter_context(patch.object(traces, "ROOT", root))
        stack.enter_context(patch.object(traces, "TRACE_FRONTEND", root / "bin/islaris"))
        stack.enter_context(patch.object(traces, "TRACE_FOOTPRINT", root / "bin/isla-footprint"))
        stack.enter_context(patch.object(traces, "ELFFile"))
        image = stack.enter_context(patch.object(traces, "Image"))
        image.return_value.read.return_value = bytes.fromhex("13000000")
        stack.enter_context(patch.object(traces.sys, "argv", self.argv(root, mode)))
        stack.enter_context(patch("sys.stdout", new_callable=io.StringIO))
        run = stack.enter_context(patch.object(traces.subprocess, "run", side_effect=frontend or self.frontend))
        canonical = stack.enter_context(patch.object(traces, "canonical_decodeitem"))
        indexes = stack.enter_context(patch.object(traces, "generate_indexes"))
        exports = stack.enter_context(patch.object(traces, "append_exports", side_effect=AssertionError("unexpected exports")))
        return run, canonical, indexes, exports

    def test_trace_only_uses_riscv_and_binds_inputs_and_outputs(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = self.fixture(directory)
            run, canonical, indexes, exports = self.context(stack, root)
            traces.main()
            run.assert_called_once()
            command = run.call_args.args[0]
            self.assertEqual(command[0], str(root / "bin/islaris"))
            self.assertIn("--arch=riscv64", command)
            self.assertIn("--coqdir=Example.Heldout", command)
            self.assertEqual(run.call_args.kwargs["env"]["OPAM_SWITCH_PREFIX"], "/home/cody/islaris/_opam")
            canonical.assert_not_called()
            indexes.assert_not_called()
            exports.assert_not_called()
            report = json.loads((root / "output/trace-manifest.json").read_text())
            self.assertEqual(report["instruction_count"], 1)
            self.assertEqual(report["generated_count"], 1)
            self.assertEqual(report["inputs"]["elf"]["sha256"], traces.sha(root / "zesu-zisk.elf"))
            for record in report["inputs"].values():
                self.assertEqual(record["sha256"], traces.sha(Path(record["path"])))
            for name, digest in report["files"].items():
                self.assertEqual(digest, traces.sha(root / "output" / name))
            self.assertEqual((root / "output/instrs.v").read_text(), "native instruction index\n")
            self.assertNotIn("commitments", report)
            self.assertNotIn("proof", json.dumps(report))
            self.assertFalse((root / "output/coverage.json").exists())

    def test_conflicting_modes_refuse_before_generation(self):
        for flag in ["--closure", "--indexes", "--ensure-native-indexes"]:
            with self.subTest(flag=flag), tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
                root = self.fixture(directory)
                run, *_ = self.context(stack, root, mode=("--trace-only", flag))
                stack.enter_context(patch("sys.stderr", new_callable=io.StringIO))
                with self.assertRaises(SystemExit) as error:
                    traces.main()
                self.assertEqual(error.exception.code, 2)
                run.assert_not_called()
                self.assertFalse((root / "output").exists())

    def test_changed_elf_hash_refuses_before_generation(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = self.fixture(directory)
            (root / "zesu-zisk.elf").write_text("changed ELF")
            run, *_ = self.context(stack, root)
            with self.assertRaisesRegex(ValueError, "selected ELF hash changed"):
                traces.main()
            run.assert_not_called()

    def test_dump_bytes_must_match_the_elf(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = self.fixture(directory)
            (root / "input.dump").write_text("4: 00000093 addi\n")
            run, *_ = self.context(stack, root)
            with self.assertRaisesRegex(ValueError, "Dump byte mismatch"):
                traces.main()
            run.assert_not_called()

    def test_duplicate_addresses_refuse_before_generation(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = self.fixture(directory)
            (root / "input.dump").write_text("4: 00000013 addi\n4: 00000013 addi\n")
            run, *_ = self.context(stack, root)
            with self.assertRaisesRegex(ValueError, "repeats an instruction address"):
                traces.main()
            run.assert_not_called()

    def test_runtime_instructions_cannot_disappear_from_the_dataset(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = self.fixture(directory)
            run, *_ = self.context(stack, root)
            stack.enter_context(patch.object(traces, "decode", return_value={
                "pc": 4, "word": 0x13, "kind": "runtime", "mnemonic": "runtime"}))
            with self.assertRaisesRegex(ValueError, "cannot omit runtime instructions"):
                traces.main()
            run.assert_not_called()

    def test_existing_outputs_and_sidecars_are_preserved(self):
        for name in ["output", "output.selected.dump", "output.generation.log"]:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
                root = self.fixture(directory)
                path = root / name
                if name == "output":
                    path.mkdir()
                else:
                    path.write_text("retained evidence")
                run, *_ = self.context(stack, root)
                with self.assertRaisesRegex(ValueError, "requires a new output"):
                    traces.main()
                run.assert_not_called()
                if path.is_file():
                    self.assertEqual(path.read_text(), "retained evidence")

    def test_missing_or_extra_instruction_files_refuse(self):
        for name in ["a4.v", "a8.v", "a4.isla", "a8.isla"]:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
                root = self.fixture(directory)
                def frontend(command, **kwargs):
                    result = self.frontend(command, **kwargs)
                    path = root / "output" / name
                    if name.startswith("a4"):
                        path.unlink()
                    else:
                        path.write_text("extra instruction")
                    return result
                self.context(stack, root, frontend)
                with self.assertRaisesRegex(ValueError, "Instruction (modules|traces) differ"):
                    traces.main()
                self.assertFalse((root / "output/trace-manifest.json").exists())

    def test_changed_inputs_during_generation_refuse(self):
        for name in ["input.dump", "zesu-zisk.elf", "ZesuSsz/riscv64_zesu.toml",
                     "build/stock-zisk/platform/riscv64-zisk.ir", "bin/islaris"]:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
                root = self.fixture(directory)
                def frontend(command, **kwargs):
                    result = self.frontend(command, **kwargs)
                    (root / name).write_text("changed input")
                    return result
                self.context(stack, root, frontend)
                with self.assertRaisesRegex(ValueError, "trace-only input changed"):
                    traces.main()
                self.assertFalse((root / "output/trace-manifest.json").exists())

    def test_selected_dump_changes_refuse(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = self.fixture(directory)
            def frontend(command, **kwargs):
                result = self.frontend(command, **kwargs)
                Path(command[1]).write_text("changed selection")
                return result
            self.context(stack, root, frontend)
            with self.assertRaisesRegex(ValueError, "selected trace-only dump changed"):
                traces.main()

    def test_frontend_failure_keeps_the_log_without_a_success_manifest(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = self.fixture(directory)
            def frontend(command, **kwargs):
                kwargs["stdout"].write("frontend failed\n")
                return argparse.Namespace(returncode=5)
            self.context(stack, root, frontend)
            with self.assertRaisesRegex(RuntimeError, "Trace-only generation failed"):
                traces.main()
            self.assertEqual((root / "output.generation.log").read_text(), "frontend failed\n")
            self.assertFalse((root / "output/trace-manifest.json").exists())

    def test_legacy_decodeitem_route_is_unchanged(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = self.fixture(directory)
            (root / "output").mkdir()
            (root / "output/coverage.json").write_text("existing coverage")
            run, canonical, indexes, _ = self.context(stack, root, mode=())
            traces.main()
            canonical.assert_called_once()
            indexes.assert_not_called()
            run.assert_not_called()

    def test_legacy_closure_route_is_unchanged(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = self.fixture(directory)
            inventory = {"functions": [{"rows": [{"pc": 4, "word": 0x13}]}],
                         "inline_decodeSingleTx": {"block_ranges": []}}
            (root / "inventory.json").write_text(json.dumps(inventory))
            (root / "output").mkdir()
            (root / "output/coverage.json").write_text("existing coverage")
            run, canonical, indexes, _ = self.context(stack, root, mode=("--closure",))
            traces.main()
            indexes.assert_called_once()
            canonical.assert_not_called()
            run.assert_not_called()

    def test_fixed_inventory_validation_still_refuses_an_extra_function(self):
        from indexes import approved_regions
        with self.assertRaisesRegex(ValueError, "selected function names differ"):
            approved_regions({"functions": [{"name": "unregistered.function", "rows": []}]}, set())


if __name__ == "__main__":
    unittest.main()
