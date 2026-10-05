"""Native trace events bind register footprints to selected instruction bytes."""
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from trace_registers import events, extract


class TraceRegisterTests(unittest.TestCase):
    def test_overwrite_requires_a_written_register_even_without_a_read(self):
        footprint, assumptions = events('ReadReg "PC" [] value :t: WriteReg "x14" [] value :t: WriteReg "PC" [] value')
        self.assertEqual(footprint, {'regs_read': ['PC'], 'regs_written': ['PC', 'x14']})
        self.assertEqual(assumptions, [])

    def test_comments_and_string_contents_do_not_create_events(self):
        footprint, _ = events('(* ReadReg "x2" (* WriteReg "x3" *) *) ReadReg "x1" [] value "WriteReg ""x4"""')
        self.assertEqual(footprint, {'regs_read': ['x1'], 'regs_written': []})

    def test_assumption_references_remain_separate_until_the_ruling(self):
        footprint, references = events('Assume (AVal_Var "mstatus" fields) :t: ReadReg "x1" [] value')
        self.assertEqual(footprint['regs_read'], ['x1'])
        self.assertEqual(references, ['mstatus'])

    def test_union_includes_every_instruction_and_binds_hashes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            manifest = {'artifact_identity': 'selected', 'project_derived': {}}
            for pc, body in ((16, 'ReadReg "x1" [] value'), (20, 'WriteReg "x2" [] value')):
                path = root / f'a{pc:x}.v'
                path.write_text(f'Definition a{pc:x} : isla_trace := {body}.')
                manifest['project_derived'][str(path)] = {'artifact_identity': 'selected',
                    'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
            cfg = {'artifact_identity': 'selected', 'functions': [{'entry': 16,
                'rows': [{'pc': 16}, {'pc': 20}], 'blocks': [{'start': 16, 'end': 24}]}]}
            blocks, instructions, sources = extract(cfg, 16, root, manifest)
            self.assertEqual(blocks, [{'entry_pc': '0x10', 'regs_read': ['x1'], 'regs_written': ['x2'], 'regs_assumed': []}])
            self.assertEqual(len(instructions), 2)
            self.assertEqual(len(sources), 2)
            (root/'a10.v').write_text('changed')
            with self.assertRaisesRegex(ValueError, 'hash changed'):
                extract(cfg, 16, root, manifest)

    def test_unclosed_comment_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'unfinished comment'):
            events('(* ReadReg "x1"')


if __name__ == '__main__':
    unittest.main()
