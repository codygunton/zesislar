"""The decodeItem steps of render_function.sh: return-package design, loop-exit entries,
loop-head and design callers. Each step's output equals the committed file it renders."""
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import render_design_callers
import render_function_callers
import render_loop_exits
from function_profiles import load_profile
from render_fp301_statements import render_return_package

ROOT = Path(__file__).resolve().parents[2]
TOOLS = ROOT / 'tools/block'


def design_cfg(profile):
    """A CFG with the design table's blocks and successors (FUNCTION.json shape)."""
    design = json.loads((ROOT / profile['design_callers']['design']).read_text())
    return {'functions': [{'blocks': [
        {'start': int(row['entry_pc'], 0), 'end': int(row['entry_pc'], 0) + 4,
         'successors': [int(pc, 0) for pc in row['successor_pcs']]} for row in design['blocks']]}]}


class RenderFunctionSteps(unittest.TestCase):
    def setUp(self):
        self.profile = load_profile('decodeItem')
        self.generated = ROOT / self.profile.generated_directory
        self.callers = ROOT / self.profile['callers_directory']

    def test_return_package_design_renders_the_committed_package(self):
        entries, structural = render_return_package(self.profile)
        self.assertEqual(entries, (self.generated / 'FunctionReturnEntries.v').read_text())
        self.assertEqual(structural, (self.generated / 'FunctionReturnStructural.v').read_text())
        self.assertEqual(entries.count('⌜DecodeMeaningModuloKnownBugs args currentStorage⌝'), 1)

    def test_loop_exit_blocks_are_blocks_of_the_function(self):
        self.assertEqual(render_function_callers._block_key(self.profile, 0x800d6a38), '00d8')
        self.assertEqual(render_function_callers._block_key(self.profile, 0x800d6a24), '00c4')
        self.assertIsNone(render_function_callers._block_key(self.profile, 0x800d6a3c))

    def test_loop_exit_entries_render_into_the_output_directory(self):
        with tempfile.TemporaryDirectory() as scratch:
            output = Path(scratch) / 'loop-exits'
            argv = ['render_loop_exits.py', '--function', 'decodeItem', '--coqc-args', str(Path(scratch) / 'a.json'),
                    '--output', str(output), '--loop-heads-dir', str(self.generated)]
            (Path(scratch) / 'a.json').write_text('["coqc"]')
            with mock.patch.object(sys, 'argv', argv), \
                    mock.patch.object(render_loop_exits, 'RocqContradictionCheck') as check:
                check.return_value.return_value = False
                render_loop_exits.main()
            cases = json.loads((output / 'RESULT.json').read_text())['cases']
            self.assertEqual([case['pc'] for case in cases], ['0x800d6a38', '0x800d6a40', '0x800d6ad8', '0x800d6b08'])
            for case in cases:
                for key in ('entry', 'structural'):
                    path = Path(case[key]['path'])
                    self.assertEqual(path.read_text(), (self.generated / path.name).read_text(), path.name)

    def test_driver_callers_equal_the_committed_callers(self):
        with tempfile.TemporaryDirectory() as scratch:
            scratch = Path(scratch)
            cases = [{'pc': self.profile.pc(block), 'status': 'source_declarations_rendered'}
                     for block in self.profile['blocks']]
            cases.append({'pc': 'function_return', 'status': 'source_declarations_rendered'})
            exits = [{'pc': self.profile.pc(row['pc']), 'status': 'source_declarations_rendered'}
                     for row in self.profile['loop_exits']['design']]
            (scratch / 'RESULT.json').write_text(json.dumps({'cases': cases}))
            (scratch / 'EXITS.json').write_text(json.dumps({'cases': exits}))
            (scratch / 'FUNCTION.json').write_text(json.dumps(design_cfg(self.profile)))
            output = scratch / 'callers'
            subprocess.run([sys.executable, str(TOOLS / 'render_function_callers.py'), '--function', 'decodeItem',
                            '--entries', str(scratch / 'RESULT.json'), '--extra-entries', str(scratch / 'EXITS.json'),
                            '--cfg', str(scratch / 'FUNCTION.json'), '--output', str(output)],
                           check=True, capture_output=True)
            table = json.loads((output / 'CALLERS.json').read_text())
            self.assertEqual((table['rendered'], table['refused'], table['design']), (18, 0, 2))
            subprocess.run([sys.executable, str(TOOLS / 'render_design_callers.py'), '--function', 'decodeItem',
                            '--write', '--output', str(output)], check=True, capture_output=True)
            rendered = sorted(path.name for path in output.glob('Caller*.v'))
            self.assertEqual(rendered, sorted(path.name for path in self.callers.glob('Caller*.v')))
            self.assertEqual(len(rendered), 24)
            for name in rendered:
                self.assertEqual((output / name).read_text(), (self.callers / name).read_text(), name)
        self.assertEqual(render_design_callers.check(self.profile), [])


if __name__ == '__main__':
    unittest.main()
