"""Check measured gate claims, budget waits, and exact release ownership."""

import fcntl
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import correctness_gate

from correctness_gate import active_claims, digest, gate_environment, read, release, reserve, save, select_peak


class GateClaimsTests(unittest.TestCase):
    def test_gates_force_cache_off(self):
        source = {'ZESU_PROOF_CACHE': 'on', 'other': 'preserved'}
        self.assertEqual(gate_environment(source), {'ZESU_PROOF_CACHE': 'off', 'other': 'preserved'})
        self.assertEqual(source['ZESU_PROOF_CACHE'], 'on')

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

    def select_peak(self, history, target, **kwargs):
        return select_peak(history, target, expected_identity={"fixture": "current"}, **kwargs)

    def completed(self, peak, **extra):
        return {"target": "check-fast", "success": True, "exit_code": 0, "completed_ns": 1,
                "aggregate_peak_bytes": peak, "workload_identity": {"fixture": "current"},
                "cache_provenance": {"mode": "uncached", "authority": "complete cold build"}, **extra}

    def test_completed_matching_uncached_peak_allows_measured_claim(self):
        result = self.select_peak({"runs": [self.completed(21)]}, "check-fast", physical_fence_bytes=500)
        self.assertEqual(result["claim_bytes"], 32)

    def test_largest_completed_matching_peak_wins(self):
        rows = [self.completed(90), self.completed(11, completed_ns=2),
                self.completed(1000, success=False, exit_code=1),
                self.completed(2000, target="check-iris")]
        result = self.select_peak({"runs": rows}, "check-fast", physical_fence_bytes=500)
        self.assertEqual(result["claim_bytes"], 135)
        self.assertEqual(result["measurement"], rows[0])

    def test_failed_incomplete_and_unknown_measurements_keep_full_fence(self):
        for extra in [{"success": False, "exit_code": 1}, {"success": None},
                      {"exit_code": None}, {"exit_code": False}, {"completed_ns": None},
                      {"cache_provenance": {"mode": "unknown", "authority": "legacy"}},
                      {"cache_provenance": {"mode": "cache_enabled", "authority": "cached"}}]:
            with self.subTest(extra=extra):
                result = self.select_peak({"runs": [self.completed(1, **extra)]}, "check-fast",
                                     claim_ceiling_bytes=2, physical_fence_bytes=500)
                self.assertEqual((result["claim_bytes"], result["reason"]), (500, "full_physical_fence"))

    def test_unknown_gate_ceiling_cannot_understate_actual_aggregate_fence(self):
        self.assertEqual(self.select_peak({"runs": []}, "check-fast", claim_ceiling_bytes=5,
                                     physical_fence_bytes=500)["claim_bytes"], 500)
        self.assertEqual(self.select_peak({"runs": []}, "check-fast", claim_ceiling_bytes=700,
                                     physical_fence_bytes=500)["claim_bytes"], 700)

    def test_cache_provenance_declaration_remains_exact_and_preserves_history(self):
        row = self.completed(21, result_sha256="a" * 64)
        row.pop("cache_provenance")
        declaration = {"target": "check-fast", "result_sha256": "a" * 64,
                       "mode": "uncached", "authority": "reviewed complete cold build"}
        history = {"runs": [row], "measurement_provenance": [declaration]}
        original = json.dumps(history, sort_keys=True)
        self.assertEqual(self.select_peak(history, "check-fast")["claim_bytes"], 32)
        self.assertEqual(json.dumps(history, sort_keys=True), original)
        with self.assertRaisesRegex(ValueError, "duplicated"):
            self.select_peak({**history, "measurement_provenance": [declaration, declaration]}, "check-fast")
        with self.assertRaisesRegex(ValueError, "unmatched"):
            self.select_peak({"runs": [], "measurement_provenance": [declaration]}, "check-fast")

    def test_conflicting_cache_provenance_refuses(self):
        row = self.completed(21, result_sha256="a" * 64,
                             cache_provenance={"mode": "cache_enabled", "authority": "warm build"})
        declaration = {"target": "check-fast", "result_sha256": "a" * 64,
                       "mode": "uncached", "authority": "cold build"}
        with self.assertRaisesRegex(ValueError, "conflict"):
            self.select_peak({"runs": [row], "measurement_provenance": [declaration]}, "check-fast")

    def test_changed_or_absent_workload_identity_uses_full_gate_fence(self):
        row = self.completed(1)
        for expected in [None, {}, {"fixture": "changed"}]:
            with self.subTest(expected=expected):
                self.assertEqual(correctness_gate.select_peak({"runs": [row]}, "check-fast",
                    expected_identity=expected, physical_fence_bytes=500)["claim_bytes"], 500)
        row.pop("workload_identity")
        self.assertEqual(self.select_peak({"runs": [row]}, "check-fast", physical_fence_bytes=500)["claim_bytes"], 500)

    def test_actual_batch_fence_matches_guard_configuration(self):
        self.assertEqual(correctness_gate.batch_fence_bytes({}), 120 * 1024**3)
        self.assertEqual(correctness_gate.batch_fence_bytes({"ZESU_GATE_LIMIT": "64G"}), 64 * 1024**3)
        self.assertEqual(correctness_gate.batch_fence_bytes({"ZESU_GATE_LIMIT": "123"}), 123)
        self.assertEqual(correctness_gate.batch_fence_bytes(
            {"ZESU_BATCH_LIMIT": "64G", "ZESU_GATE_LIMIT": "120G"}), 120 * 1024**3)
        for value in ["max", "0", "-1", "1.5G"]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                correctness_gate.batch_fence_bytes({"ZESU_GATE_LIMIT": value})

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


class GateSizingCliTests(unittest.TestCase):
    def parse_ceiling(self, extra, environment):
        argv = ["correctness_gate.py", "run", "--target", "check-iris", "--build-dir", "private", *extra,
                "--", "make", "_check-iris"]
        with patch.dict("os.environ", environment, clear=True), patch("sys.argv", argv), \
                patch.object(correctness_gate, "run", return_value=0) as execute:
            self.assertEqual(correctness_gate.main(), 0)
        return execute.call_args.args[0].claim_ceiling_bytes

    def test_explicit_cli_ceiling(self):
        self.assertEqual(self.parse_ceiling(["--claim-ceiling-bytes", "300"], {}), 300)

    def test_ceiling_environment(self):
        self.assertEqual(self.parse_ceiling([], {"ZESU_GATE_CLAIM_CEILING_BYTES": "400"}), 400)

    def test_legacy_bootstrap_argument_remains_explicit_ceiling(self):
        self.assertEqual(self.parse_ceiling(["--bootstrap-claim-bytes", "500"], {}), 500)

    def test_new_environment_overrides_legacy_ceiling(self):
        self.assertEqual(self.parse_ceiling([], {"ZESU_GATE_CLAIM_CEILING_BYTES": "600",
                                                "ZESU_GATE_BOOTSTRAP_CLAIM_BYTES": "700"}), 600)


if __name__ == "__main__":
    unittest.main()
