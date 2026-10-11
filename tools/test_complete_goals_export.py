"""Complete-goal export retains all raw fields without formatting limits."""
import copy
import gzip
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).parent/'block'))
from complete_goals_mcp import PRINTING_DEPTH, complete_with_definitions, write_export


class Complete:
    def __init__(self, value):
        self.value = value

    def to_json(self):
        return copy.deepcopy(self.value)


class PrintingPet:
    def __init__(self, ordinary, kernel):
        self.ordinary = ordinary
        self.kernel = kernel
        self.calls = []

    def complete_goals(self, state, timeout):
        self.calls.append(('complete', state, timeout))
        return Complete(self.kernel if state == 'printing' else self.ordinary)

    def run(self, state, command, timeout):
        self.calls.append(('run', state, command, timeout))
        return 'printing'


class ExportTests(unittest.TestCase):
    def test_recovered_6ae0_retains_all_contexts_and_ownership_definitions(self):
        data = Path(__file__).parent / 'block/testdata/complete_goals_6ae0.json.gz'
        provenance = json.loads(data.with_suffix('').with_suffix('.provenance.json').read_text())
        self.assertEqual(hashlib.sha256(data.read_bytes()).hexdigest(), provenance['fixture_sha256'])
        payload = gzip.decompress(data.read_bytes())
        self.assertEqual(hashlib.sha256(payload).hexdigest(), provenance['original_export']['sha256'])
        retained = json.loads(payload)
        ordinary = {key: value for key, value in retained.items()
                    if key not in ('kernel_groups', 'local_definition_export')}
        kernel = retained['kernel_groups']
        pet = PrintingPet(ordinary, kernel)
        complete, full = complete_with_definitions(pet, 'original')
        self.assertEqual(pet.calls, [('complete', 'original', 30),
                                    ('run', 'original', f'Set Printing All. Set Printing Depth {PRINTING_DEPTH}.', 30),
                                    ('complete', 'printing', 30), ('complete', 'original', 30)])
        with tempfile.TemporaryDirectory() as root:
            result = write_export(complete, root, 13, full)
            exported = json.loads(Path(result['path']).read_text())
            self.assertEqual([result[key] for key in ('active_goals', 'stack_entries',
                                                     'shelved_goals', 'given_up_goals')], [5, 0, 10, 0])
            for key in ('goals', 'stack', 'shelf', 'given_up'):
                self.assertEqual(exported[key], ordinary[key])
                self.assertEqual(exported['kernel_groups'][key], kernel[key])
            ownership = exported['kernel_groups']['goals'][0]['hyps'][66]
            self.assertEqual(ordinary['goals'][0]['hyps'][66]['def'], 'HIDDEN')
            self.assertEqual(ownership['names'], ['IPM_JANNO'])
            self.assertIn('@Envs', ownership['def'])
            self.assertEqual(write_export(complete, root, 13, full), result)

    def test_definitions_in_every_group_and_both_focus_sides(self):
        goal = {'info': {'evar': 1}, 'ty': 'TRACE',
                'hyps': [{'names': ['TRACE'], 'ty': 'nat', 'def': 'HIDDEN'},
                         {'names': ['IPM_JANNO'], 'ty': 'nat', 'def': 'HIDDEN'},
                         {'names': ['LET_GOAL'], 'ty': 'nat', 'def': 'HIDDEN'}]}
        ordinary = {'goals': [goal], 'stack': [[[goal], [goal]]],
                    'shelf': [goal], 'given_up': [goal]}
        kernel = copy.deepcopy(ordinary)
        for group in (kernel['goals'], *kernel['stack'][0], kernel['shelf'], kernel['given_up']):
            for entry in group:
                for index, hyp in enumerate(entry['hyps']):
                    hyp['def'] = 'S (' * (100 + index) + 'O' + ')' * (100 + index)
        complete, full = complete_with_definitions(PrintingPet(ordinary, kernel), 'original')
        with tempfile.TemporaryDirectory() as root:
            result = write_export(complete, root, 7, full)
            exported = json.loads(Path(result['path']).read_text())
            self.assertEqual(exported['kernel_groups'], kernel)
            self.assertEqual(exported['local_definition_export']['printing_depth'], PRINTING_DEPTH)
            self.assertEqual(complete.to_json(), ordinary)

    def test_rejects_hidden_or_truncated_kernel_definitions(self):
        ordinary = {'goals': [{'info': {}, 'ty': 'TRACE',
                              'hyps': [{'names': ['TRACE'], 'ty': 'nat', 'def': 'HIDDEN'}]}],
                    'stack': [], 'shelf': [], 'given_up': []}
        for body, error in [('HIDDEN', 'hides a local definition'), ('S (S (...))', 'printer ellipsis')]:
            with self.subTest(body=body):
                kernel = copy.deepcopy(ordinary)
                kernel['goals'][0]['hyps'][0]['def'] = body
                with self.assertRaisesRegex(ValueError, error):
                    complete_with_definitions(PrintingPet(ordinary, kernel), 'original')

    def test_rejects_changed_context_order_or_source_state(self):
        ordinary = {'goals': [{'info': {}, 'ty': 'x',
                              'hyps': [{'names': ['x'], 'ty': 'nat'}, {'names': ['y'], 'ty': 'nat'}]}],
                    'stack': [], 'shelf': [], 'given_up': []}
        kernel = copy.deepcopy(ordinary)
        kernel['goals'][0]['hyps'].reverse()
        with self.assertRaisesRegex(ValueError, 'ordered context'):
            complete_with_definitions(PrintingPet(ordinary, kernel), 'original')
        class ChangedPet(PrintingPet):
            def complete_goals(self, state, timeout):
                if len(self.calls) == 3:
                    return Complete(dict(self.ordinary, shelf=[self.ordinary['goals'][0]]))
                return super().complete_goals(state, timeout)
        with self.assertRaisesRegex(ValueError, 'original proof state'):
            complete_with_definitions(ChangedPet(ordinary, ordinary), 'original')

    def test_exports_large_goals_and_every_debt_class(self):
        value = {'goals': [{'hyps': [], 'ty': 'x'*70000}],
                 'stack': [[[], [{'ty': 'stack proposition'}]]],
                 'shelf': [{'ty': 'shelved proposition'}],
                 'given_up': [{'ty': 'given-up proposition'}]}
        class Complete:
            def to_json(self):
                return value
        with tempfile.TemporaryDirectory() as root:
            result = write_export(Complete(), root, 12)
            self.assertEqual(json.loads(Path(result['path']).read_text()), value)
            self.assertGreater(result['bytes'], 70000)
            self.assertEqual(result['stack_frame_goal_counts'], [{'left': 0, 'right': 1}])
            self.assertEqual(result['shelved_goals'], 1)
            self.assertEqual(result['given_up_goals'], 1)

    def test_missing_proof_scope_is_unavailable_and_creates_no_goal_payload(self):
        with tempfile.TemporaryDirectory() as root:
            result = write_export(None, root, 19)
            self.assertFalse(result['success'])
            self.assertEqual(result['reason'], 'no-proof-scope')
            self.assertEqual(result['state_id'], 19)
            self.assertEqual(list(Path(root).iterdir()), [])

    def test_rejects_changed_data_for_the_same_live_state(self):
        class Complete:
            def to_json(self):
                return {'goals': [], 'stack': [], 'shelf': [], 'given_up': []}
        with tempfile.TemporaryDirectory() as root:
            write_export(Complete(), root, 12)
            Path(root, 'state_12.json').write_text('changed')
            with self.assertRaisesRegex(ValueError, 'same state'):
                write_export(Complete(), root, 12)


if __name__ == '__main__':
    unittest.main()
