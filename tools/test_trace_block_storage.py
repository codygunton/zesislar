"""Check receipt binding with synthetic bytes. These are not native captures."""

import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
from trace_block import json_bytes
from trace_block_storage import verify_storage_records


class StorageTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.root = self.base / "raw"
        self.root.mkdir()
        self.source = self.root / "event.json"
        self.mirror = self.base / "mirror.json"
        self.mirror.write_bytes(b'{"kind":"synthetic"}\n')
        self.source.symlink_to(self.mirror)
        self.archive = self.base / "archive.zst"
        self.archive.write_bytes(b'synthetic archive bytes')
        self.original_hash = self.digest(self.mirror)
        self.archive_hash = self.digest(self.archive)
        self.seal_path = self.base / "TRANSFER-SEAL.json"
        self.journal_path = self.base / "MAPPING.jsonl"
        self.audit_path = self.base / "AUDIT.json"
        self.identity_path = self.base / "IDENTITIES.json"
        self.identity_path.write_bytes(b'{"scope":"synthetic later observation"}\n')
        self.installed = {"phase": "installed", "original": str(self.source),
            "original_sha256": self.original_hash, "mirror": str(self.mirror),
            "mirror_sha256": self.original_hash, "decompressed_sha256": self.original_hash,
            "decompression_equal": True, "archive": str(self.archive),
            "archive_sha256": self.archive_hash, "original_bytes": self.mirror.stat().st_size,
            "archive_bytes": self.archive.stat().st_size, "symlink_target": str(self.mirror),
            "resolved": str(self.mirror)}
        self.rows = [self.installed, {"phase": "complete", "files": 1}]
        self.entry = {"original": str(self.source), "sha256": self.original_hash,
            "mirror": str(self.mirror), "archive": str(self.archive),
            "archive_sha256": self.archive_hash, "original_bytes": self.mirror.stat().st_size,
            "archive_bytes": self.archive.stat().st_size}
        self.seal = {"result": {"phase": "complete", "files": 1},
                     "original_hashes_match": True, "archive_hashes_match": True, "files": [self.entry]}
        self.audit = {key: True for key in ("all_archive_hashes_match", "all_journal_transitions_match",
            "all_recorded_source_mirror_decompression_hashes_match", "all_recorded_targets_and_sizes_match")}
        self.audit.update(limits=["Synthetic binding control only. No decompression or native proof."],
                          journal_gap="Installation-time symlink identity is unavailable.")
        self.refresh()

    @staticmethod
    def digest(path):
        return hashlib.sha256(Path(path).read_bytes()).hexdigest()

    def refresh(self):
        self.journal_path.write_bytes(b''.join(json_bytes(row).replace(b'\n', b'') + b'\n' for row in self.rows))
        self.seal["references"] = [{"path": str(self.journal_path), "sha256": self.digest(self.journal_path)}]
        self.seal_path.write_bytes(json_bytes(self.seal))
        self.audit["bindings"] = {str(path): self.digest(path) for path in
                                  (self.seal_path, self.journal_path, self.identity_path)}
        self.audit["later_identity_supplement"] = {"source": str(self.identity_path),
                                                  "sha256": self.digest(self.identity_path)}
        self.audit_path.write_bytes(json_bytes(self.audit))
        self.records = {name: {"path": str(path), "sha256": self.digest(path)} for name, path in (
            ("transfer_seal", self.seal_path), ("journal", self.journal_path),
            ("audit", self.audit_path), ("identity_observation", self.identity_path))}

    def test_complete_records_preserve_identity_limit(self):
        result = verify_storage_records(self.root, self.records)
        self.assertEqual(len(result["verified_replacements"]), 1)
        self.assertEqual(result["installation_time_identity"], "unavailable")
        self.assertIn("Later identity", result["identity_limit"])
        self.assertIn("No new decompression", result["archive_verification"])
        self.assertEqual(result["records"], self.records)

    def test_raw_link_without_completed_records_rejects(self):
        with self.assertRaisesRegex(ValueError, "require the completed storage"):
            verify_storage_records(self.root, None)

    def test_no_replaced_files_need_no_storage_record(self):
        plain = self.base / "plain"
        plain.mkdir()
        (plain / "event.json").write_text("{}")
        self.assertIsNone(verify_storage_records(plain, None))

    def test_incomplete_reference_map_rejects(self):
        del self.records["journal"]
        with self.assertRaisesRegex(ValueError, "incomplete"):
            verify_storage_records(self.root, self.records)

    def test_changed_archive_rejects(self):
        self.archive.write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, "raw evidence reference changed"):
            verify_storage_records(self.root, self.records)

    def test_changed_mirror_rejects(self):
        self.mirror.write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, "raw evidence reference changed"):
            verify_storage_records(self.root, self.records)

    def test_unlisted_replacement_rejects(self):
        (self.root / "extra.json").symlink_to(self.mirror)
        with self.assertRaisesRegex(ValueError, "no installed storage record"):
            verify_storage_records(self.root, self.records)

    def test_different_symlink_target_rejects(self):
        other = self.base / "other.json"
        other.write_bytes(self.mirror.read_bytes())
        self.source.unlink()
        self.source.symlink_to(other)
        with self.assertRaisesRegex(ValueError, "different mirror target"):
            verify_storage_records(self.root, self.records)

    def test_incomplete_journal_rejects(self):
        self.rows.pop()
        self.refresh()
        with self.assertRaisesRegex(ValueError, "completion counts"):
            verify_storage_records(self.root, self.records)

    def test_work_after_completion_rejects(self):
        self.rows.append(copy.deepcopy(self.installed))
        self.rows[-1]["original"] = "later.json"
        self.refresh()
        with self.assertRaisesRegex(ValueError, "after completion"):
            verify_storage_records(self.root, self.records)

    def test_boolean_completion_count_rejects(self):
        self.rows[-1]["files"] = True
        self.seal["result"]["files"] = True
        self.refresh()
        with self.assertRaisesRegex(ValueError, "completion counts"):
            verify_storage_records(self.root, self.records)

    def test_journal_cannot_claim_another_mirror_hash(self):
        self.installed["mirror_sha256"] = "0" * 64
        self.refresh()
        with self.assertRaisesRegex(ValueError, "recorded byte comparison"):
            verify_storage_records(self.root, self.records)

    def test_seal_and_journal_must_name_same_archive(self):
        self.entry["archive"] = "another.zst"
        self.refresh()
        with self.assertRaisesRegex(ValueError, "disagree on archive"):
            verify_storage_records(self.root, self.records)

    def test_audit_must_bind_exact_seal(self):
        self.audit["bindings"][str(self.seal_path)] = "0" * 64
        self.audit_path.write_bytes(json_bytes(self.audit))
        self.records["audit"]["sha256"] = self.digest(self.audit_path)
        with self.assertRaisesRegex(ValueError, "audit does not bind transfer_seal"):
            verify_storage_records(self.root, self.records)

    def test_unavailable_recorded_decompression_rejects(self):
        self.installed["decompression_equal"] = False
        self.refresh()
        with self.assertRaisesRegex(ValueError, "recorded byte comparison"):
            verify_storage_records(self.root, self.records)

    def test_alias_link_cannot_replace_recorded_direct_target(self):
        alias = self.base / "alias.json"
        alias.symlink_to(self.mirror)
        self.source.unlink()
        self.source.symlink_to(alias)
        with self.assertRaisesRegex(ValueError, "installed storage target"):
            verify_storage_records(self.root, self.records)

    def test_broken_raw_link_rejects_without_receipts(self):
        (self.root / "broken.json").symlink_to(self.base / "missing.json")
        with self.assertRaisesRegex(ValueError, "broken or"):
            verify_storage_records(self.root, None)

    def test_directory_raw_link_rejects(self):
        (self.root / "directory").symlink_to(self.base, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "broken or"):
            verify_storage_records(self.root, self.records)


if __name__ == "__main__":
    unittest.main()
