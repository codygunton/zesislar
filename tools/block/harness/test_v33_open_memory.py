"""Check the exact released v3.3 open-case memory authority without proofs."""
from copy import deepcopy
from pathlib import Path
import json
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'code'))
import memory_policy as M


class V33OpenMemory(unittest.TestCase):
    def setUp(self):
        self.authority = M.read(M.PORT_V33_OPEN_AUTHORITY)
        self.profile = {'schema': 'scratch.admission-profile.v1', 'kind': M.PORT_KIND,
                        'authority': M.PORT_V33_OPEN_AUTHORITY, 'memory_route': 'measured_native',
                        'memory_booking': M.PORT_V33_OPEN_BOOKING,
                        'supplier_ready': self.authority['supplier_ready']}

    def measurement(self, case):
        return dict(format='completed_stock_v33_open_v1', route='stock_zesu_block',
                    block=case['block'], module=case['module'], native_source=case['source'],
                    statement_sha256=case['statement_sha256'], authority=M.PORT_V33_OPEN_AUTHORITY,
                    **{key: case['measurement'][key] for key in ['result', 'accounting', 'closure', 'release']})

    def target(self, case):
        return dict(module=case['module'], pc=case['pc'], source_sha256=case['source']['sha256'],
                    statement_sha256=case['statement_sha256'])

    def test_eight_exact_completed_peaks_use_the_pr92_formula(self):
        self.assertEqual(len(self.authority['cases']), 8)
        for case in self.authority['cases']:
            with self.subTest(block=case['block']):
                value, reason = M.completed(self.measurement(case), self.target(case))
                self.assertIsNone(reason)
                self.assertEqual(value['claim_bytes'], (3 * case['peak_bytes'] + 1) // 2)
                self.assertEqual(value['claim_bytes'], case['claim_bytes'])
                self.assertLessEqual(value['claim_bytes'], 32 * M.GIB)

    def test_public_profile_uses_only_the_v33_supplier(self):
        self.assertEqual(M.production_port_authority(self.profile), self.authority)
        changed = deepcopy(self.profile)
        changed['supplier_ready']['sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            M.production_port_authority(changed)

    def test_changed_target_identity_refuses(self):
        case = self.authority['cases'][0]
        for field, value in [('module', 'Other.Module'), ('pc', case['pc'] + 4),
                             ('source_sha256', '0' * 64), ('statement_sha256', '0' * 64)]:
            with self.subTest(field=field):
                target = dict(self.target(case), **{field: value})
                self.assertIsNone(M.completed(self.measurement(case), target)[0])

    def test_changed_receipt_and_extra_fields_refuse(self):
        case = self.authority['cases'][0]
        row = self.measurement(case)
        row['result'] = self.authority['cases'][1]['measurement']['result']
        self.assertIsNone(M.completed(row, self.target(case))[0])
        row = dict(self.measurement(case), claim_bytes=1)
        self.assertIsNone(M.completed(row, self.target(case))[0])

    def test_only_the_eight_authorized_targets_have_the_32g_fence(self):
        for case in self.authority['cases']:
            job = {'phase': 'native', 'key': case['block'], 'ordered_modules': [],
                   'target': self.target(case)}
            self.assertEqual(M.production_port_case(self.profile, job)[1], case)
        with self.assertRaises(ValueError):
            M.production_port_case(self.profile, {'phase': 'native', 'key': '800d6974',
                                                   'ordered_modules': [], 'target': self.target(case)})

    def test_existing_v34_and_default_routes_stay_separate(self):
        self.assertFalse(M.v34_profile(self.profile))
        self.assertNotEqual(M.PORT_V33_OPEN_BOOKING, M.PORT_V34_PEAK_BOOKING)
        self.assertEqual(M.rounded_claim(M.GIB), 8 * M.GIB)
        six = next(case for case in self.authority['cases'] if case['block'] == '800d6ae0')
        self.assertEqual(six['peak_bytes'], 6338080768)
        self.assertEqual(six['label'], 'non-pilot; join entries were hand-seeded')


if __name__ == '__main__':
    unittest.main()
