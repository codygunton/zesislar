"""annotations.py: compile to a function profile, check it, and test rows on machine-run snapshots."""
from pathlib import Path
import json
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import annotations  # noqa: E402

HERE = Path(__file__).resolve().parent
NEXT_UINT64 = HERE / 'testdata/nextUint64.annotations.json'
PROFILE = HERE.parents[1] / 'tools/block/functions/nextUint64.json'


def fixture():
    return json.loads(NEXT_UINT64.read_text())


class Compile(unittest.TestCase):
    def test_compile_reproduces_the_designs_of_next_uint64(self):
        profile = json.loads(PROFILE.read_text())
        compiled = annotations.compile_profile(fixture())
        self.assertEqual(compiled['loop_designs'], profile['loop_designs'])
        self.assertEqual(compiled['join_designs'], profile['join_designs'])
        self.assertEqual(compiled['loop_heads'], profile['loop_heads'])
        # The whole hand-written profile, not only its designs.
        self.assertEqual(compiled, profile)

    def test_compiled_profile_names_its_source(self):
        compiled = annotations.compile_profile(fixture(), NEXT_UINT64)
        self.assertEqual(compiled['generated_from']['path'], 'tools/oblig/testdata/nextUint64.annotations.json')
        self.assertEqual(len(compiled['generated_from']['sha256']), 64)

    def test_an_access_row_becomes_a_placement_row(self):
        data = fixture()
        data['rows'].append({'id': 'access-50', 'request': 'nextUint64/decision/access_placement-0050',
                             'at': {'pc': '+0x50', 'boundary': 'access'},
                             'placement': {'array': 'nextInputBytes (nextUint64Base args)', 'index': 'i',
                                           'scale': 1, 'offset': 0}})
        compiled = annotations.compile_profile(data)
        self.assertEqual(compiled['access_placements'], [{'pc': '+0x50', 'array': 'nextInputBytes (nextUint64Base args)',
                                                          'index': 'i', 'scale': 1, 'offset': 0}])

    def test_schema_errors_are_refused(self):
        data = fixture()
        data['rows'][0]['at']['boundary'] = 'somewhere'
        with self.assertRaisesRegex(annotations.AnnotationError, 'boundary'):
            annotations.compile_profile(data)
        data = fixture()
        data['rows'][0]['at']['pc'] = '0x800d6300'
        with self.assertRaisesRegex(annotations.AnnotationError, 'pc must be'):
            annotations.compile_profile(data)
        data = fixture()
        data['profile']['loop_designs'] = []
        with self.assertRaisesRegex(annotations.AnnotationError, 'compiled keys'):
            annotations.compile_profile(data)

    def test_check_fails_when_the_profile_drifts(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            functions = root / 'tools/block/functions'
            functions.mkdir(parents=True)
            source = functions / 'nextUint64.annotations.json'
            source.write_text(NEXT_UINT64.read_text())
            with mock.patch.object(annotations, 'ROOT', root), mock.patch.object(annotations, 'FUNCTIONS', functions):
                self.assertEqual(annotations.cmd_compile('nextUint64'), 0)
                self.assertEqual(annotations.cmd_check(None), 0)
                profile = json.loads((functions / 'nextUint64.json').read_text())
                profile['loop_designs'][0]['index'] = 'j'
                (functions / 'nextUint64.json').write_text(json.dumps(profile))
                with mock.patch('sys.stderr'):
                    self.assertEqual(annotations.cmd_check(None), 1)
                # A profile that names generated_from without its annotation file fails too.
                source.unlink()
                with mock.patch('sys.stderr'):
                    self.assertEqual(annotations.cmd_check(None), 1)


def snapshot(directory, offset, visits, input_id):
    path = directory / ('STATE-%s.json' % offset)
    path.write_text(json.dumps({'schema': 'oblig-exec-snapshot/1', 'function': 'demo', 'input': input_id,
                                'offset': '+0x' + offset, 'visits': visits}))


def regs(**values):
    result = {name: 0 for name in annotations.ABI[1:]}
    result.update(values)
    return result


@unittest.skipUnless(annotations.coqc_command(), 'no coqc')
class MachineRuns(unittest.TestCase):
    """A loop at +0xa4 entered from +0x9c: a2 walks from its entry value up to a3 (excluded)."""
    ROW = {'id': 'loop-a4', 'request': 'demo/decision/loop_assertion-00a4',
           'at': {'pc': '+0xa4', 'boundary': 'loop_cut', 'predecessor': '+0x9c'},
           'binders': [{'name': 'machine_x12', 'register': 'x12'},
                       {'name': 'i', 'role': 'index', 'exec': '(bv_unsigned {reg:x12} - bv_unsigned {x12})%Z'}],
           'facts': [{'coq': 'bv_unsigned machine_x12 = (bv_unsigned {x12} + i)%Z', 'role': 'index_link'},
                     {'coq': '(0 <= i)%Z', 'role': 'index_range'},
                     {'coq': 'bv_unsigned machine_x12 < bv_unsigned {x13}', 'role': 'bound'}]}

    def run_dir(self, root):
        for input_id, start, end in (('short', 100, 102), ('long', 200, 205)):
            directory = root / 'exec' / input_id
            directory.mkdir(parents=True)
            snapshot(directory, '0000', [{'visit': 0, 'insn': 0, 'regs': regs(a2=start, a3=end)}], input_id)
            snapshot(directory, '009c', [{'visit': 0, 'insn': 10, 'regs': regs(a2=start, a3=end)}], input_id)
            snapshot(directory, '00a4', [{'visit': n, 'insn': 12 + 5 * n, 'regs': regs(a2=start + n, a3=end)}
                                         for n in range(end - start)], input_id)
        return root

    def data(self, *rows):
        return {'schema': annotations.SCHEMA, 'function': 'demo', 'symbol': 'demo.fn', 'profile': {},
                'rows': list(rows)}

    def test_a_true_loop_assertion_passes_every_snapshot(self):
        with tempfile.TemporaryDirectory() as directory:
            result = annotations.test_rows(self.data(self.ROW), self.run_dir(Path(directory)))
        self.assertEqual(result['verdict'], 'passed')
        self.assertEqual(result['checked'], 3 * (2 + 5))
        self.assertEqual(result['unchecked'], [])

    def test_a_wrong_bound_is_rejected_and_names_the_input(self):
        wrong = json.loads(json.dumps(self.ROW))
        # The bound `machine_x12 < entry x12 + 3` holds on the short input only.
        wrong['facts'][2]['coq'] = '(bv_unsigned machine_x12 < bv_unsigned {x12} + 3)%Z'
        with tempfile.TemporaryDirectory() as directory:
            result = annotations.test_rows(self.data(wrong), self.run_dir(Path(directory)))
        self.assertEqual(result['verdict'], 'rejected')
        self.assertEqual((result['row'], result['input'], result['visit'], result['pc']), ('loop-a4', 'long', 3, '+0xa4'))
        self.assertEqual(result['fact'], wrong['facts'][2]['coq'])

    def test_a_fact_over_contract_names_is_unchecked_not_rejected(self):
        row = json.loads(json.dumps(self.ROW))
        row['facts'].append({'coq': '(nextInputPointer (nextUint64Base args) <= bv_unsigned {x12})%Z', 'role': 'meaning'})
        with tempfile.TemporaryDirectory() as directory:
            result = annotations.test_rows(self.data(row), self.run_dir(Path(directory)))
        self.assertEqual(result['verdict'], 'passed')
        # Reported once: the fact does not elaborate on the first visit, so no visit evaluates it.
        self.assertEqual(len(result['unchecked']), 1)
        self.assertEqual(result['checked'], 3 * (2 + 5))
        self.assertIn('nextInputPointer', result['unchecked'][0]['error'])


if __name__ == '__main__':
    unittest.main()
