"""check_relocatable.py refuses absolute addresses in listed files and passes the tree."""
import io
import json
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_relocatable  # noqa: E402

# Built at run time so this file holds no address literal itself.
ADDRESS = '0x' + '800d' + '6960'


def run(argv):
    out, err = io.StringIO(), io.StringIO()
    with redirect_stdout(out), redirect_stderr(err):
        code = check_relocatable.main(argv)
    return code, out.getvalue() + err.getvalue()


class CheckRelocatableTests(unittest.TestCase):
    def test_tree_passes(self):
        code, text = run([])
        self.assertEqual(code, 0, text)

    def fixture(self, files, body):
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(lambda: __import__('shutil').rmtree(tmp))
        (tmp / 'Contract.v').write_text(body)
        (tmp / 'list.json').write_text(json.dumps(
            {'schema': check_relocatable.SCHEMA, 'files': files, 'exclude': ['Gen*.v']}))
        return tmp

    def test_fixture_with_address_fails(self):
        tmp = self.fixture(['*.v', 'missing/*.v', 'absent.v'],
                           f'Definition entry := {ADDRESS}.\n')
        code, text = run(['--root', str(tmp), '--list', str(tmp / 'list.json')])
        self.assertEqual(code, 1)
        self.assertIn(f'Contract.v:1: absolute address {ADDRESS}', text)

    def test_exclude_and_missing_files(self):
        tmp = self.fixture(['*.v', 'absent.v'], 'Definition entry := sym_memcpy.\n')
        (tmp / 'Generated.v').write_text(f'Notation x := ({ADDRESS} : Z).\n')
        code, text = run(['--root', str(tmp), '--list', str(tmp / 'list.json')])
        self.assertEqual(code, 0, text)
        self.assertIn('1 file(s)', text)

    def test_patterns(self):
        hits = check_relocatable.address_hits
        decimal = '2148' + '000000'
        low = '21474' + '83648'
        upper = '0x' + ADDRESS[2:].upper()
        self.assertEqual(hits(f'a {upper} b'), [(1, upper)])
        self.assertEqual(hits(f'x\n({decimal})'), [(2, decimal)])
        self.assertEqual(hits(f'{low}%Z'), [(1, low)])
        # Not whole tokens: a longer number, a hash fragment, an offset.
        self.assertEqual(hits(f'1{decimal} {decimal}7 ab{low} +0x6960 {ADDRESS}0'), [])

    def test_whole_image_range(self):
        hits = check_relocatable.address_hits
        text_end = '0x' + '8010' + 'fd78'
        high = '0x' + '80ff' + 'ffff'
        self.assertEqual(hits(f'({text_end})%Z <= x'), [(1, text_end)])
        self.assertEqual(hits(high), [(1, high)])
        for decimal in (str((1 << 31) + 0x10fd78), str((1 << 31) + 0xffffff)):
            self.assertEqual(hits(f'({decimal})%Z'), [(1, decimal)])
        # Outside the image: RAM, an address one hex digit longer.
        self.assertEqual(hits('0x' + 'a000' + '0000' + ' 0x' + '8010' + 'fd780'), [])

    def test_a_profile_non_address_constant_passes_in_its_residual_modules_only(self):
        bound = '0x' + '8000' + '0000'
        tmp = self.fixture(['*.v', 'ZesuSsz/Residuals/*/*.v'],
                           'Notation inputHigh := ((2 ^ 31) : Z) (only parsing).\n'
                           f'Definition other := ({bound})%Z.\n')
        (tmp / 'ZesuSsz/Residuals/fn').mkdir(parents=True)
        (tmp / 'ZesuSsz/Residuals/fn/Block.v').write_text(f'Lemma r : p <= ({bound})%Z -> pc = {ADDRESS}.\n')
        profiles = tmp / 'tools/block/functions'
        profiles.mkdir(parents=True)
        row = {'name': 'inputHigh', 'value': 2 ** 31, 'source': 'Contract.v'}
        (profiles / 'fn.json').write_text(json.dumps({'non_address_constants': [row]}))
        code, text = run(['--root', str(tmp), '--list', str(tmp / 'list.json')])
        self.assertEqual(code, 1)
        # The residual module keeps its code address; the bound passes there, not in Contract.v.
        self.assertIn(f'Block.v:1: absolute address {ADDRESS}', text)
        self.assertNotIn(f'Block.v:1: absolute address {bound}', text)
        self.assertIn(f'Contract.v:2: absolute address {bound}', text)
        # A row the source does not declare with that value is refused.
        (profiles / 'fn.json').write_text(json.dumps({'non_address_constants': [{**row, 'value': 2 ** 31 + 8}]}))
        code, text = run(['--root', str(tmp), '--list', str(tmp / 'list.json')])
        self.assertEqual(code, 2)
        self.assertIn('does not declare inputHigh', text)


if __name__ == '__main__':
    unittest.main()
