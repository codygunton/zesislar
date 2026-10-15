"""Test restored-original receipts without a native proof or real storage move."""

import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import test_trace_block_storage as fixtures
from trace_block import json_bytes
from trace_block_storage import verify_storage_records


class RestorationTests(unittest.TestCase):
    def setUp(self):
        self.fixture = fixtures.StorageTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        f = self.fixture
        self.old_root = f.base / "old-mirrors"
        self.old_root.mkdir()
        moved = self.old_root / "mirror.json"
        f.mirror.rename(moved)
        f.mirror = moved
        f.source.unlink()
        f.source.symlink_to(moved)
        f.entry["mirror"] = str(moved)
        for key in ("mirror", "symlink_target", "resolved"):
            f.installed[key] = str(moved)
        f.refresh()
        archive = f.base / "archived-metadata"
        archive.mkdir()
        self.metadata = {}
        for role, reference in f.records.items():
            original = Path(reference["path"])
            target = archive / (role + ".json")
            shutil.copyfile(original, target)
            self.metadata[role] = {"path": str(target), "sha256": f.digest(target),
                                   "original_path": str(original)}
        payload = moved.read_bytes()
        f.source.unlink()
        f.source.write_bytes(payload)
        moved.unlink()
        self.old_root.rmdir()
        self.receipt_path = f.base / "RESTORATION.json"
        self.row = {"original": str(f.source), "sha256": f.original_hash,
            "bytes": f.source.stat().st_size, "regular_file": True, "symlink": False,
            "old_mirror": str(moved), "mirror_removed": True,
            "archive": {"path": str(f.archive), "sha256": f.archive_hash,
                        "bytes": f.archive.stat().st_size, "disposition": "retained-on-home"}}
        self.reversal_journal = f.base / "REVERSAL.jsonl"
        self.reversal_journal.write_text('{"phase":"complete"}\n')
        self.receipt = {"reversal_journal": {"path": str(self.reversal_journal),
            "sha256": f.digest(self.reversal_journal)}, "schema": 1, "status": "complete", "restored_files": [self.row],
            "archived_metadata": self.metadata, "mirror_root": str(self.old_root),
            "mirror_root_removed": True, "proof_source_changes": 0}
        self.records = {"restoration": {}, "archived_metadata": self.metadata}
        self.refresh()

    def refresh(self):
        self.receipt_path.write_bytes(json_bytes(self.receipt))
        self.records["restoration"] = {"path": str(self.receipt_path),
                                      "sha256": self.fixture.digest(self.receipt_path)}

    def verify(self):
        return verify_storage_records(self.fixture.root, self.records)

    def test_restored_regular_files_verify_without_old_mirrors(self):
        result = self.verify()
        self.assertEqual(result["mode"], "restored-originals")
        self.assertEqual(len(result["verified_restorations"]), 1)
        self.assertFalse(Path(self.row["old_mirror"]).exists())
        self.assertEqual(result["installation_time_identity"], "unavailable")
        self.assertEqual(result["records"], self.records)
        self.assertIn("historical", result["historical_mirrors"])

    def test_old_mirror_root_must_be_removed(self):
        self.old_root.mkdir()
        with self.assertRaisesRegex(ValueError, "mirror root still exists"):
            self.verify()

    def test_current_file_hash_must_match(self):
        self.fixture.source.write_text("changed")
        with self.assertRaisesRegex(ValueError, "reference changed"):
            self.verify()

    def test_current_original_must_not_be_symlink(self):
        other = self.fixture.base / "other.json"
        other.write_bytes(self.fixture.source.read_bytes())
        self.fixture.source.unlink()
        self.fixture.source.symlink_to(other)
        with self.assertRaisesRegex(ValueError, "still contains file links"):
            self.verify()

    def test_incomplete_receipt_rejects(self):
        self.receipt["status"] = "running"
        self.refresh()
        with self.assertRaisesRegex(ValueError, "incomplete"):
            self.verify()

    def test_receipt_source_changes_reject(self):
        self.receipt["proof_source_changes"] = 1
        self.refresh()
        with self.assertRaisesRegex(ValueError, "incomplete"):
            self.verify()

    def test_omitted_restoration_rejects(self):
        self.receipt["restored_files"] = []
        self.refresh()
        with self.assertRaisesRegex(ValueError, "different original sets"):
            self.verify()

    def test_changed_original_hash_cannot_override_history(self):
        self.row["sha256"] = "0" * 64
        self.refresh()
        with self.assertRaisesRegex(ValueError, "archived transfer identity"):
            self.verify()

    def test_receipt_cannot_replace_archived_metadata(self):
        self.receipt["archived_metadata"] = copy.deepcopy(self.metadata)
        self.receipt["archived_metadata"]["audit"]["sha256"] = "0" * 64
        self.refresh()
        with self.assertRaisesRegex(ValueError, "differs from its metadata"):
            self.verify()

    def test_archived_journal_bytes_must_match(self):
        Path(self.metadata["journal"]["path"]).write_text("changed")
        with self.assertRaisesRegex(ValueError, "reference changed"):
            self.verify()

    def test_changed_archive_rejects(self):
        self.fixture.archive.write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError, "reference changed"):
            self.verify()

    def test_boolean_schema_rejects(self):
        self.receipt["schema"] = True
        self.refresh()
        with self.assertRaisesRegex(ValueError, "incomplete"):
            self.verify()

    def test_duplicate_original_rejects(self):
        self.receipt["restored_files"].append(copy.deepcopy(self.row))
        self.refresh()
        with self.assertRaisesRegex(ValueError, "repeats"):
            self.verify()

    def test_relocated_archive_cannot_claim_original_disposition(self):
        self.row["archive"]["path"] = str(self.fixture.base / "different.zst")
        self.refresh()
        with self.assertRaisesRegex(ValueError, "archived transfer identity"):
            self.verify()

    def test_receipt_cannot_claim_an_unrelated_removed_root(self):
        self.receipt["mirror_root"] = str(self.fixture.base / "unrelated-absent")
        self.refresh()
        with self.assertRaisesRegex(ValueError, "outside the removed root"):
            self.verify()

    def add_optional_metadata(self):
        f = self.fixture
        result = f.base / "transfer-result.json"
        result.write_bytes(json_bytes({"phase": "complete", "files": 1}))
        original_result = str(f.base / "historical-result.json")
        seal_path = Path(self.metadata["transfer_seal"]["path"])
        seal = json.loads(seal_path.read_text())
        seal["references"].append({"path": original_result, "sha256": f.digest(result)})
        seal_path.write_bytes(json_bytes(seal))
        self.metadata["transfer_seal"]["sha256"] = f.digest(seal_path)
        audit_path = Path(self.metadata["audit"]["path"])
        audit = json.loads(audit_path.read_text())
        audit["bindings"][self.metadata["transfer_seal"]["original_path"]] = f.digest(seal_path)
        audit_path.write_bytes(json_bytes(audit))
        self.metadata["audit"]["sha256"] = f.digest(audit_path)
        redirect = f.base / "monitor-redirect.json"
        redirect.write_bytes(json_bytes({"physical_output_parent": str(f.base / "output"),
            "raw_seals": {"fixture": str(f.base / "output/fixture/RAW-SEAL.json")},
            "proof_changes": 0, "signals": 0}))
        self.metadata["transfer_result"] = {"path": str(result), "sha256": f.digest(result),
                                             "original_path": original_result}
        self.metadata["monitor_redirect"] = {"path": str(redirect), "sha256": f.digest(redirect),
                                             "original_path": str(f.base / "old-redirect.json")}
        self.refresh()

    def test_all_six_actual_roles_are_bound(self):
        self.add_optional_metadata()
        result = self.verify()
        self.assertEqual(set(result["records"]["archived_metadata"]),
            {"transfer_seal", "journal", "audit", "identity_observation", "transfer_result", "monitor_redirect"})
        self.assertEqual(result["reversal_journal"], self.receipt["reversal_journal"])

    def test_unknown_archived_role_rejects(self):
        self.metadata["unknown"] = copy.deepcopy(self.metadata["audit"])
        self.refresh()
        with self.assertRaisesRegex(ValueError, "references are incomplete"):
            self.verify()

    def test_changed_optional_metadata_bytes_reject(self):
        self.add_optional_metadata()
        Path(self.metadata["monitor_redirect"]["path"]).write_text("changed")
        with self.assertRaisesRegex(ValueError, "reference changed"):
            self.verify()

    def test_optional_result_must_be_bound_by_transfer_seal(self):
        self.add_optional_metadata()
        self.metadata["transfer_result"]["original_path"] = "/different/result.json"
        self.refresh()
        with self.assertRaisesRegex(ValueError, "does not bind its result"):
            self.verify()

    def test_changed_reversal_journal_rejects(self):
        self.reversal_journal.write_text("changed")
        with self.assertRaisesRegex(ValueError, "reference changed"):
            self.verify()

    def test_monitor_raw_seals_cannot_leave_output_parent(self):
        self.add_optional_metadata()
        p = Path(self.metadata["monitor_redirect"]["path"])
        value = json.loads(p.read_text())
        value["raw_seals"]["fixture"] = "/outside/RAW-SEAL.json"
        p.write_bytes(json_bytes(value))
        self.metadata["monitor_redirect"]["sha256"] = self.fixture.digest(p)
        self.refresh()
        with self.assertRaisesRegex(ValueError, "invalid output paths"):
            self.verify()


if __name__ == "__main__":
    unittest.main()
