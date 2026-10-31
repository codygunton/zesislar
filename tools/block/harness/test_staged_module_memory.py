"""Import the actual staged compiler closure with no parent tools path."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import scratch


class StagedMemoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.tools = self.root / 'owned/tools'
        self.harness = Path(scratch.__file__).resolve().parent
        for relative, source in json.loads((self.harness / 'TOOL-LAYOUT.json').read_text()).items():
            target = self.tools / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(self.harness / source, target)

    def run_import(self, *, compiler=False, ambient=None):
        code = 'import sys;sys.path.insert(0,sys.argv[1]);'
        code += 'import entry_chain_compiler;' if compiler else ''
        code += 'import module_memory;print(module_memory.compiler_pids.__globals__["__file__"])'
        environment = dict(os.environ, PYTHONPATH=str(ambient or ''), PYTHONDONTWRITEBYTECODE='1')
        return subprocess.run([sys.executable, '-B', '-c', code, str(self.tools / 'block')],
                              cwd=self.root, env=environment, capture_output=True, text=True)

    def test_actual_compiler_import_resolves_owned_dependency(self):
        result = self.run_import(compiler=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(Path(result.stdout.strip()), self.tools / 'det/coqc_slots.py')

    def test_ambient_det_cannot_replace_owned_dependency(self):
        ambient = self.root / 'ambient'
        package = ambient / 'det'
        package.mkdir(parents=True)
        (package / '__init__.py').write_text('raise RuntimeError("ambient det loaded")\n')
        result = self.run_import(ambient=ambient)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(Path(result.stdout.strip()), self.tools / 'det/coqc_slots.py')

    def test_missing_owned_dependency_refuses_ambient_fallback(self):
        (self.tools / 'det/coqc_slots.py').unlink()
        result = self.run_import()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('lacks its owned det dependency', result.stderr)

    def test_dependency_symlink_outside_owned_tools_refuses(self):
        slots = self.tools / 'det/coqc_slots.py'
        foreign = self.root / 'foreign.py'
        shutil.copyfile(slots, foreign)
        slots.unlink()
        slots.symlink_to(foreign)
        result = self.run_import()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('lacks its owned det dependency', result.stderr)


if __name__ == '__main__':
    unittest.main()
