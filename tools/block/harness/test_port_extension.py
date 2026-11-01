"""Check the exact 21-case release without starting proof work."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE)]
import _historical_fixtures as historical
import memory_policy as P
from test_production_port_memory import ProductionPortMemory

class ExactExtension(unittest.TestCase):
    def setUp(self):
        historical.use_policy(self)
    def test_real_authority_keeps_original_fifteen_and_exact_six(self):
        profile={'schema':'scratch.admission-profile.v1','kind':P.PORT_KIND,'authority':P.PORT_AUTHORITY,'memory_route':'measured_native'}
        authority=P.production_port_authority(profile)
        extension=P.read(P.PORT_EXTENSION)
        self.assertEqual(authority['cases'],extension['original_cases']+extension['additional_cases'])
        self.assertEqual(len(authority['cases']),22)
        self.assertTrue(all(row['block'].startswith('region-return-') for row in authority['cases'][15:21]))
        self.assertIn('8009c354',{row['block'] for row in authority['cases']})

    def test_each_full_return_key_selects_exact_source_and_statement(self):
        profile={'schema':'scratch.admission-profile.v1','kind':P.PORT_KIND,'authority':P.PORT_AUTHORITY,'memory_route':'measured_native'}
        authority=P.production_port_authority(profile)
        for case in authority['cases'][15:21]:
            job=dict(key=case['block'],phase='native',target=dict(module=case['module'],pc=case['pc'],
                source_sha256=case['source']['sha256'],statement_sha256=case['statement_sha256']))
            self.assertEqual(P.production_port_case(profile,job)[1],case)
            for field in ['module','pc','source_sha256','statement_sha256']:
                wrong=deepcopy(job);wrong['target'][field]='wrong'
                with self.assertRaises(ValueError):P.production_port_case(profile,wrong)
            wrong=deepcopy(job);wrong['key']=format(case['pc'],'x')
            with self.assertRaises(ValueError):P.production_port_case(profile,wrong)
