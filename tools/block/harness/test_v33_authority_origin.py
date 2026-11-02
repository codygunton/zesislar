"""Accept only the byte-identical released authority at its exact historical root."""
from copy import deepcopy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import memory_policy as M
from test_v33_open_memory import V33OpenMemory


class HistoricalAuthorityTests(unittest.TestCase):
    measurement = V33OpenMemory.measurement
    target = V33OpenMemory.target

    def setUp(self):
        V33OpenMemory.setUp(self)
        self.legacy = dict(M.PORT_V33_OPEN_AUTHORITY,
                           path=M.PORT_V33_OPEN_LEGACY_PATHS[0])
        self.profile['authority'] = self.legacy

    def test_exact_released_origin_keeps_every_case_and_measurement(self):
        self.assertEqual(M.v33_open_authority(self.profile), self.authority)
        for case in self.authority['cases']:
            row = dict(self.measurement(case), authority=self.legacy)
            value, reason = M.completed(row, self.target(case))
            self.assertIsNone(reason)
            self.assertEqual(value['claim_bytes'], case['claim_bytes'])

    def test_equal_bytes_at_another_root_refuse(self):
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / 'PORT-V33-OPEN-AUTHORITY.json'
            path.write_bytes(M.bound(self.legacy).read_bytes())
            profile = deepcopy(self.profile)
            profile['authority']['path'] = str(path)
            with self.assertRaisesRegex(ValueError, 'approved roots'):
                M.v33_open_authority(profile)

    def test_changed_bytes_at_the_selected_origin_refuse(self):
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / 'PORT-V33-OPEN-AUTHORITY.json'
            path.write_bytes(M.bound(self.legacy).read_bytes() + b'\n')
            profile = deepcopy(self.profile)
            profile['authority']['path'] = str(path)
            with patch.object(M, 'PORT_V33_OPEN_LEGACY_PATHS', (str(path),)):
                with self.assertRaises(ValueError):
                    M.v33_open_authority(profile)

    def test_historical_origin_grants_no_other_case_or_supplier(self):
        first, second = self.authority['cases'][:2]
        row = dict(self.measurement(first), authority=self.legacy)
        self.assertIsNone(M.completed(row, self.target(second))[0])
        profile = deepcopy(self.profile)
        profile['supplier_ready']['sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            M.v33_open_authority(profile)


if __name__ == '__main__':
    unittest.main()
