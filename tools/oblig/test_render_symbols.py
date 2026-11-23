"""render_symbols.py renders Symbols.v from the pinned ELF and detects a stale file."""
import io
import json
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

from elftools.elf.elffile import ELFFile

sys.path.insert(0, str(Path(__file__).resolve().parent))
import render_symbols  # noqa: E402

ELF = render_symbols.ROOT / 'build/stock-zisk/zesu-zisk.elf'


def run(argv):
    out, err = io.StringIO(), io.StringIO()
    with redirect_stdout(out), redirect_stderr(err):
        code = render_symbols.main(argv)
    return code, out.getvalue() + err.getvalue()


class RenderSymbolsTests(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp)

    def write_list(self, symbols):
        path = self.tmp / 'symbols.json'
        path.write_text(json.dumps({'schema': render_symbols.SCHEMA, 'elf': str(ELF),
                                    'output': str(self.tmp / 'Symbols.v'), 'symbols': symbols}))
        return str(path)

    def test_committed_module_is_current(self):
        code, text = run(['--check'])
        self.assertEqual(code, 0, text)

    def test_body_is_symtab_address_and_check_detects_stale(self):
        with open(ELF, 'rb') as handle:
            table = ELFFile(handle).get_section_by_name('.symtab')
            address = next(s['st_value'] for s in table.iter_symbols() if s.name == 'memcpy')
        listing = self.write_list(['memcpy', 'rlp.decodeItem'])
        self.assertEqual(run(['--list', listing])[0], 0)
        output = self.tmp / 'Symbols.v'
        text = output.read_text()
        self.assertIn(f'Notation sym_memcpy := (({address:#x}) : Z) (only parsing).', text)
        self.assertIn('(*   sym_rlp_decodeItem <- "rlp.decodeItem" *)', text)
        self.assertEqual(run(['--list', listing, '--check'])[0], 0)
        output.write_text(text.replace('sym_memcpy :=', 'sym_memcpy_old :='))
        code, message = run(['--list', listing, '--check'])
        self.assertEqual(code, 1)
        self.assertIn('stale', message)
        output.unlink()
        self.assertEqual(run(['--list', listing, '--check'])[0], 1)

    def test_names(self):
        self.assertEqual(render_symbols.notation_name('array_list.Aligned([32]u8,null).toOwnedSlice'),
                         'sym_array_list_Aligned_32_u8_null_toOwnedSlice')
        with self.assertRaises(render_symbols.SymbolError):
            render_symbols.render(['a.b', 'a_b'], {'a.b': 1, 'a_b': 2}, 'elf', '0', 'list')

    def test_missing_symbol_refused(self):
        code, text = run(['--list', self.write_list(['no.such.symbol'])])
        self.assertEqual(code, 2)
        self.assertIn('0 defined entries', text)


if __name__ == '__main__':
    unittest.main()
