"""Check trace-only eql binding without changing production trace contracts."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import bind_traces as binder
from traces import selected_dump


def binding(path):
    return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


class EqlBindingTests(unittest.TestCase):
    def fixture(self, root):
        out = root / "eql"
        out.mkdir()
        rows = [{"pc": 4 * index, "word": 19, "mnemonic": "addi"} for index in range(74)]
        accesses = [{"pc": hex(index), "constraint_emitted": True} for index in range(42)]
        accesses += [{"pc": pc, "constraint_emitted": True} for pc in
                     ["0x8009c43c", "0x8009c440", "0x8009c450", "0x8009c454"]]
        for row in rows:
            for suffix in ["v", "isla"]:
                (out / (f"a{row['pc']:x}." + suffix)).write_text("bound instruction")
        for name in ["instrs.v", "dune"]: (out / name).write_text(name)
        source = root / "source"
        source.write_text("bound input")
        inputs = {name: binding(source) for name in
                  ["manifest", "elf", "dump", "driver", "frontend", "footprint",
                   "footprint_wrapper", "platform_snapshot", "config", "decoder",
                   "per_load_regions", "region_renderer"]}
        config = root / "config.toml"
        config.write_text('[registers.reset]\n"medeleg.bits" = "0x0000000000000000"\n"mideleg.bits" = "0x0000000000000000"\n')
        inputs["config"] = binding(config)
        dump = root / "selected.dump"
        dump.write_text(selected_dump(rows))
        report = {"schema": "stock-zisk.trace-only.v1", "arch": "riscv64", "coqdir": "ZesuSsz.Stock.Eql",
                  "instruction_count": 74, "generated_count": 74, "inputs": inputs,
                  "selected_dump": binding(dump),
                  "files": {p.name: binding(p)["sha256"] for p in out.iterdir()}}
        (out / "trace-manifest.json").write_text(json.dumps(report))
        return out, rows, accesses, report

    def validate(self, out, rows, accesses, **kwargs):
        with patch.object(binder, "ELFFile"), patch.object(binder, "Image"), \
             patch.object(binder, "selected_rows", return_value=rows), \
             patch.object(binder, "annotate_regions", **kwargs) as annotate:
            if not kwargs: annotate.return_value = (rows, accesses, [])
            return binder.validate_trace_only(out, "eql")

    def test_complete_group_accepts(self):
        with tempfile.TemporaryDirectory() as directory:
            out, rows, accesses, report = self.fixture(Path(directory))
            self.assertEqual(self.validate(out, rows, accesses), report)

    def test_changed_input_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            out, rows, accesses, report = self.fixture(Path(directory))
            Path(report["inputs"]["elf"]["path"]).write_text("changed")
            with self.assertRaisesRegex(ValueError, "input changed"):
                self.validate(out, rows, accesses)

    def test_missing_pair_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            out, rows, accesses, report = self.fixture(Path(directory))
            (out / "a0.isla").unlink()
            with self.assertRaisesRegex(ValueError, "file set"):
                self.validate(out, rows, accesses)

    def test_wrong_output_hash_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            out, rows, accesses, report = self.fixture(Path(directory))
            (out / "a0.v").write_text("changed")
            with self.assertRaisesRegex(ValueError, "output hash"):
                self.validate(out, rows, accesses)

    def test_invalid_region_refusal_propagates(self):
        with tempfile.TemporaryDirectory() as directory:
            out, rows, accesses, report = self.fixture(Path(directory))
            with self.assertRaisesRegex(ValueError, "invalid region"):
                self.validate(out, rows, accesses, side_effect=ValueError("invalid region"))

    def test_unconstrained_stack_load_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            out, rows, accesses, report = self.fixture(Path(directory))
            accesses[-1]["constraint_emitted"] = False
            with self.assertRaisesRegex(ValueError, "constrained-access coverage"):
                self.validate(out, rows, accesses)

    def test_exemption_policy_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            out, rows, accesses, report = self.fixture(Path(directory))
            report["inputs"]["load_exemptions"] = report["inputs"]["dump"]
            (out / "trace-manifest.json").write_text(json.dumps(report))
            with self.assertRaisesRegex(ValueError, "constrain every memory access"):
                self.validate(out, rows, accesses)

    def test_changed_selected_dump_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            out, rows, accesses, report = self.fixture(Path(directory))
            dump = Path(report["selected_dump"]["path"])
            dump.write_text(selected_dump(list(reversed(rows))))
            report["selected_dump"] = binding(dump)
            (out / "trace-manifest.json").write_text(json.dumps(report))
            with self.assertRaisesRegex(ValueError, "selected dump differs"):
                self.validate(out, rows, accesses)

    def test_only_eql_group_accepts_trace_only_binding(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, "approved eql group"):
                binder.validate_trace_only(Path(directory), "decodeItem")


if __name__ == "__main__": unittest.main()
