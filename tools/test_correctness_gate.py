"""Check measured gate claims, budget waits, and exact release ownership."""

import fcntl
import json
from pathlib import Path
import tempfile
import unittest

from correctness_gate import active_claims, digest, read, release, reserve, save, select_peak


class GateClaimsTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.ledger = self.root / "LEDGER.json"
        self.lock = self.root / "LEDGER.lock"
        save(self.ledger, {"fixed_claims": {"healthy": 40}})
        self.policy = {"ledger": str(self.ledger), "lock": str(self.lock),
                       "claim_key": "gate-one", "claim_bytes": 30}
        self.owner = {"pid": 99999999, "startticks": 1, "run_id": "one"}

    def test_latest_green_matching_target_wins(self):
        rows = [{"target": "check-fast", "success": True, "completed_ns": 1, "aggregate_peak_bytes": 90},
                {"target": "check-fast", "success": True, "completed_ns": 2, "aggregate_peak_bytes": 11},
                {"target": "check-iris", "success": True, "completed_ns": 3, "aggregate_peak_bytes": 200}]
        result = select_peak({"runs": rows}, "check-fast")
        self.assertEqual(result["claim_bytes"], 17)
        self.assertEqual(result["reason"], "previous_green_matching_gate")

    def test_unknown_target_uses_largest_recorded_peak(self):
        result = select_peak({"runs": [{"target": "check-fast", "success": False,
                              "completed_ns": 1, "aggregate_peak_bytes": 21}]}, "check-iris")
        self.assertEqual(result["claim_bytes"], 32)
        self.assertEqual(result["reason"], "largest_recorded_gate_peak")

    def test_absent_or_invalid_peak_refuses(self):
        for peak in [None, 0, -1, True]:
            with self.subTest(peak=peak), self.assertRaises(ValueError):
                select_peak({"runs": [{"target": "check-fast", "aggregate_peak_bytes": peak}]}, "check-fast")

    def test_unreleased_legacy_claim_counts(self):
        self.assertEqual(active_claims({"fixed_claims": {"a": 5}, "region_claims": {"old": 7}}),
                         {"a": 5, "legacy:old": 7})

    def test_only_hash_checked_legacy_release_removes_claim(self):
        receipt = self.root / "old-release.json"
        save(receipt, {"released": True})
        ledger = {"fixed_claims": {}, "region_claims": {"old": 7},
                  "released_region_claims": {"old": {"bytes": 7, "receipt": str(receipt),
                                                     "sha256": digest(receipt)}}}
        self.assertEqual(active_claims(ledger), {})
        ledger["released_region_claims"]["old"]["bytes"] = 8
        self.assertEqual(active_claims(ledger), {"legacy:old": 7})

    def test_budget_wait_releases_lock_and_preserves_healthy_claim(self):
        free = [90]
        waits = []

        def pause(seconds):
            with self.lock.open("a") as stream:
                fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
            self.assertEqual(read(self.ledger)["fixed_claims"], {"healthy": 40})
            waits.append(seconds)
            free[0] = 100

        record = reserve(self.policy, self.owner, self.root / "ADMISSION.json",
                         available=lambda: free[0], pause=pause)
        self.assertEqual(waits, [60])
        self.assertTrue(record["admitted"])
        self.assertEqual(read(self.ledger)["fixed_claims"], {"healthy": 40, "gate-one": 30})

    def test_duplicate_claim_refuses(self):
        reserve(self.policy, self.owner, self.root / "ADMISSION.json", available=lambda: 100)
        with self.assertRaisesRegex(ValueError, "already exists"):
            reserve(self.policy, self.owner, self.root / "ADMISSION.json", available=lambda: 100)

    def test_release_is_exact_and_idempotent(self):
        reserve(self.policy, self.owner, self.root / "ADMISSION.json", available=lambda: 100)
        request = self.root / "REQUEST.json"
        save(request, {"policy": self.policy, "owner": self.owner})
        first = release(request)
        self.assertTrue(first["released"])
        self.assertEqual(release(request), first)
        self.assertEqual(read(self.ledger)["fixed_claims"], {"healthy": 40, "gate-one": 0})

    def test_preregistered_never_admitted_claim_releases_zero(self):
        request = self.root / "REQUEST.json"
        save(request, {"policy": self.policy, "owner": self.owner})
        result = release(request)
        self.assertTrue(result["never_admitted"])
        self.assertEqual(result["bytes"], 0)
        self.assertEqual(read(self.ledger)["fixed_claims"], {"healthy": 40})
        self.assertEqual(read(self.root / "RELEASE.json"), result)

    def test_missing_ownership_after_admission_refuses_release(self):
        request = self.root / "REQUEST.json"
        save(request, {"policy": self.policy, "owner": self.owner})
        save(self.root / "ADMISSION.json", {"admitted": True})
        with self.assertRaisesRegex(ValueError, "lost its canonical ownership"):
            release(request)

    def test_release_refuses_another_owner(self):
        reserve(self.policy, self.owner, self.root / "ADMISSION.json", available=lambda: 100)
        request = self.root / "REQUEST.json"
        save(request, {"policy": self.policy, "owner": {**self.owner, "run_id": "other"}})
        with self.assertRaisesRegex(ValueError, "owner changed"):
            release(request)
        self.assertEqual(read(self.ledger)["fixed_claims"]["gate-one"], 30)


if __name__ == "__main__":
    unittest.main()
