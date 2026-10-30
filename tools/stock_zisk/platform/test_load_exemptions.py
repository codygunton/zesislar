"""Check exact, source-bound exclusions from region annotations."""
from copy import deepcopy
import hashlib
import gzip
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace
import traces
import test_access_regions as baseline
from access_regions import annotate_regions, checked_file, read_packet, read_source_map


def bind(path):
    return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


class LoadExemptionTests(unittest.TestCase):
    def fixture(self, directory):
        root = Path(directory)
        packet, access, instruction = baseline.AccessRegionTests().fixture(root)
        path = root / "regions.json"
        path.write_text(json.dumps(packet))
        exemption = {"pc": "0x4", "kind": "single_leaf_load_exemption",
                     "source_access": {"instruction": instruction}, "new_premises": []}
        for key in ["source_packet", "precise_handoff", "raw_trace", "rocq_trace"]:
            exemption[key] = access["raw_trace"]
        excluded = {"schema": "source.single-leaf-load-exemptions.v1",
                    "exemption_count": 1, "exemptions": [exemption]}
        ep = root / "exemptions.json"
        ep.write_text(json.dumps(excluded))
        return path, ep, excluded, instruction

    def run_fixture(self, path, ep, instruction):
        return annotate_regions([instruction], path, bind(path)["sha256"],
                                ep, bind(ep)["sha256"])

    def test_exact_exemption_preserves_instruction_without_annotation(self):
        with tempfile.TemporaryDirectory() as directory:
            path, ep, excluded, instruction = self.fixture(directory)
            rows, records, sources = self.run_fixture(path, ep, instruction)
            self.assertEqual(rows, [instruction])
            self.assertFalse(records[0]["constraint_emitted"])
            self.assertIn(bind(ep), sources)

    def test_default_still_emits_constraint(self):
        with tempfile.TemporaryDirectory() as directory:
            path, ep, excluded, instruction = self.fixture(directory)
            rows, records, _ = annotate_regions([instruction], path, bind(path)["sha256"])
            self.assertEqual(len(rows[0]["annotations"]), 1)
            self.assertTrue(records[0]["constraint_emitted"])

    def test_changed_binding_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            path, ep, excluded, instruction = self.fixture(directory)
            digest = bind(ep)["sha256"]
            ep.write_text(ep.read_text() + " ")
            with self.assertRaisesRegex(ValueError, "source changed"):
                annotate_regions([instruction], path, bind(path)["sha256"], ep, digest)

    def test_invalid_exemptions_refuse(self):
        for change in ["pc", "word", "duplicate", "premise", "count", "schema", "source"]:
            with self.subTest(change=change), tempfile.TemporaryDirectory() as directory:
                path, ep, excluded, instruction = self.fixture(directory)
                item = excluded["exemptions"][0]
                if change == "pc": item["pc"] = "0x8"
                elif change == "word": item["source_access"]["instruction"]["word"] += 1
                elif change == "duplicate": excluded["exemptions"].append(deepcopy(item))
                elif change == "premise": item["new_premises"] = ["stronger"]
                elif change == "count": excluded["exemption_count"] = 2
                elif change == "schema": excluded["schema"] = "unknown"
                elif change == "source": item["raw_trace"]["sha256"] = "0" * 64
                ep.write_text(json.dumps(excluded))
                with self.assertRaises(ValueError): self.run_fixture(path, ep, instruction)

    def test_explicit_map_rejects_host_fallback(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "existing"
            path.write_text("present on host")
            with self.assertRaisesRegex(ValueError, "no exact retained mapping"):
                checked_file(bind(path), {"root": Path(directory), "paths": {}})

    def test_map_rejects_path_escape(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "source"
            path.write_text("source")
            item = bind(path)
            mapping = {"root": Path(directory), "paths": {str(path):
                       {"path": "../source", "sha256": item["sha256"]}}}
            with self.assertRaisesRegex(ValueError, "escapes"):
                checked_file(item, mapping)

    def test_archive_preserves_exact_payload_hash(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            payload = b'{"unchanged": true}'
            archive = root / "policy.json.gz"
            archive.write_bytes(gzip.compress(payload, mtime=0))
            digest = hashlib.sha256(payload).hexdigest()
            mapping = {"root": root, "paths": {}, "archives": {
                archive.name: {"sha256": bind(archive)["sha256"], "payload_sha256": digest}}}
            self.assertEqual(read_packet(archive, digest, mapping), {"unchanged": True})
            with self.assertRaisesRegex(ValueError, "explicit source map"):
                read_packet(archive, digest)
            with self.assertRaisesRegex(ValueError, "archive binding"):
                read_packet(archive, "0" * 64, mapping)
            archive.write_bytes(archive.read_bytes() + b" ")
            with self.assertRaisesRegex(ValueError, "archive binding"):
                read_packet(archive, digest, mapping)

    def test_missing_or_changed_retained_file_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original = root / "original"
            original.write_text("exact bytes")
            retained = root / "retained"
            retained.write_bytes(original.read_bytes())
            item = bind(original)
            mapping = {"root": root, "paths": {str(original):
                       {"path": "retained", "sha256": item["sha256"]}}}
            original.unlink()
            self.assertEqual(checked_file(item, mapping), retained)
            retained.write_text("changed bytes")
            with self.assertRaisesRegex(ValueError, "source changed"):
                checked_file(item, mapping)
            retained.unlink()
            with self.assertRaises(FileNotFoundError):
                checked_file(item, mapping)

    def test_descriptor_uses_only_explicit_elf_mapping(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            elf = root / "program.elf"
            elf.write_bytes(b"selected ELF bytes")
            descriptor = {"schema": "stock-zisk.eql-trace-input.v1", "elf_input": "elf",
                          "elf_sha256": bind(elf)["sha256"]}
            mapping = {"schema": "source.region-path-map.v1", "paths": {},
                       "input_files": {"elf": {"path": "program.elf", "sha256": bind(elf)["sha256"]}}}
            path = root / "map.json"
            def arguments():
                path.write_text(json.dumps(mapping))
                return SimpleNamespace(manifest=root / "descriptor.json", trace_only=True,
                                       region_source_map=path, region_source_map_sha256=bind(path)["sha256"])
            with patch.object(traces, "ROOT", root):
                self.assertEqual(traces.resolve_trace_elf(arguments(), descriptor), elf)
                original = mapping["input_files"].pop("elf")
                with self.assertRaisesRegex(ValueError, "no explicit input mapping"):
                    traces.resolve_trace_elf(arguments(), descriptor)
                mapping["input_files"]["elf"] = original
                original["path"] = "../program.elf"
                with self.assertRaisesRegex(ValueError, "escapes"):
                    traces.resolve_trace_elf(arguments(), descriptor)
                original["path"] = "program.elf"
                elf.write_bytes(b"changed")
                with self.assertRaisesRegex(ValueError, "binding differs"):
                    traces.resolve_trace_elf(arguments(), descriptor)
                elf.unlink()
                with self.assertRaises(FileNotFoundError):
                    traces.resolve_trace_elf(arguments(), descriptor)

    def test_existing_constraint_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            path, ep, excluded, instruction = self.fixture(directory)
            instruction["annotations"] = ["//@constraint: true"]
            with self.assertRaisesRegex(ValueError, "already has a constraint"):
                self.run_fixture(path, ep, instruction)


if __name__ == "__main__":
    unittest.main()
