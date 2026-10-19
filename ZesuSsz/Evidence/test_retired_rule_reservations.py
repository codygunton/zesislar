"""Keep retired reservations historical and reject candidate activation."""
import copy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import check_decode_item_route_repair as checker


class RetiredReservations(unittest.TestCase):
    def setUp(self):
        self.root = Path(__file__).resolve().parent
        self.route = json.loads((self.root / "route_repair/INDEX.json").read_text())
        self.array = json.loads((self.root / "array_store/INDEX.json").read_text())

    def test_retired_route_cannot_accept_candidate(self):
        with self.assertRaisesRegex(ValueError, "retired reservation"):
            checker.acceptance(self.route, {})

    def test_retired_array_preserves_exact_identity(self):
        checker.array_store_schema(self.array)
        self.assertEqual({key: self.array["repair_identity"][key]
                          for key in checker.ARRAY_STORE_IDENTITY}, checker.ARRAY_STORE_IDENTITY)
        self.assertIn("retired switch reservation", checker.array_store_missing(self.array))

    def test_retired_array_rejects_foreign_identity(self):
        self.array["repair_identity"]["class"] = "ForeignClass"
        with self.assertRaisesRegex(ValueError, "reserved array-store identity"):
            checker.array_store_schema(self.array)

    def test_retired_dry_run_reports_history_only(self):
        with patch.object(checker, "inventory"):
            report = checker.dry_run(self.route)
        self.assertEqual(report["reservation_status"], "retired")
        self.assertFalse(report["accepted"])
        self.assertFalse(report["runtime_activation_checked"])
        self.assertIn("retired switch reservation", report["pending_inventory"])

    def test_retired_dry_run_rejects_candidate_sources(self):
        with self.assertRaisesRegex(ValueError, "retired reservation"):
            checker.dry_run(self.route, switch_source="unavailable.v")
        with self.assertRaisesRegex(ValueError, "retired reservation"):
            checker.dry_run(self.route, bundle={})

    def test_active_reservation_remains_distinct(self):
        active = copy.deepcopy(self.route)
        active["repair_identity"].pop("status")
        with patch.object(checker, "inventory"):
            report = checker.dry_run(active)
        self.assertEqual(report["reservation_status"], "active")
        self.assertNotIn("retired switch reservation", report["pending_inventory"])


if __name__ == "__main__":
    unittest.main()
