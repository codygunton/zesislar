"""Check the approved additional caller without starting a proof or a claim."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE / 'code'), str(HERE)]
import _historical_fixtures as historical
import memory_policy as P


class Authority23Tests(unittest.TestCase):
    def setUp(self):
        source = Path(P.PORT_AUTHORITY_23['path'])
        self.assertEqual(hashlib.sha256(source.read_bytes()).hexdigest(),
                         P.PORT_AUTHORITY_23['sha256'])
        historical.use_policy(self)
        temporary = tempfile.TemporaryDirectory(dir=historical.root())
        self.addCleanup(temporary.cleanup)
        authority = historical.read_json(source)
        target = Path(temporary.name) / 'AUTHORITY-23.json'
        target.write_text(json.dumps(authority))
        binding = {'path': str(target),
                   'sha256': hashlib.sha256(target.read_bytes()).hexdigest()}
        self.enterContext(patch.object(P, 'PORT_AUTHORITY_23', binding))
        self.profile = {'schema': 'scratch.admission-profile.v1',
                        'kind': P.PORT_KIND, 'authority': binding,
                        'memory_route': 'measured_native'}

    def test_original_twenty_two_rows_are_exact(self):
        previous = json.loads((HERE / 'policies/PORT-FAMILY-AUTHORITY-22.json').read_bytes())
        extended = json.loads((HERE / 'policies/PORT-FAMILY-AUTHORITY-23.json').read_bytes())
        self.assertEqual(extended['cases'][:22], previous['cases'])
        authority = P.production_port_authority(self.profile)
        self.assertEqual(len(authority['cases']), 23)
        self.assertEqual(authority['cases'][-1]['block'], '800d6974')

    def test_new_case_requires_its_exact_identity(self):
        case = P.production_port_authority(self.profile)['cases'][-1]
        job = dict(key=case['block'], phase='native', target=dict(
            module=case['module'], pc=case['pc'],
            source_sha256=case['source']['sha256'],
            statement_sha256=case['statement_sha256']))
        self.assertEqual(P.production_port_case(self.profile, job)[1], case)
        for field in ['module', 'pc', 'source_sha256', 'statement_sha256']:
            wrong = deepcopy(job)
            wrong['target'][field] = 'wrong'
            with self.assertRaises(ValueError):
                P.production_port_case(self.profile, wrong)

    def test_unapproved_authority_hash_refuses(self):
        profile = deepcopy(self.profile)
        profile['authority']['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'not authorized'):
            P.production_port_authority(profile)

    def test_full_fence_booking_keeps_the_exact_additional_caller(self):
        self.profile['memory_booking'] = 'full_physical_fence'
        authority = P.production_port_authority(self.profile)
        case = authority['cases'][-1]
        self.assertEqual(case['source']['sha256'],
                         'fc7669a62c6b1539f4d17f2ea3adcd72344b3466c86a911bb8c67b6b3c67feff')
        job = dict(key=case['block'],phase='native',ordered_modules=[],target=dict(
            module=case['module'],pc=case['pc'],source_sha256=case['source']['sha256'],
            statement_sha256=case['statement_sha256']))
        self.assertEqual(P.production_port_case(self.profile,job)[1],case)
        job['target']['source_sha256'] = '0'*64
        with self.assertRaisesRegex(ValueError,'source or statement differs'):
            P.production_port_case(self.profile,job)
