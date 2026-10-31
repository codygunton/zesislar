"""Run portable harness controls in an isolated Python process."""
from pathlib import Path
import subprocess
import sys
import unittest


class SharedHarnessControls(unittest.TestCase):
    def test_isolated_controls(self):
        root = Path(__file__).resolve().parents[1]
        source = root / 'tools/block/harness/shared_controls.py'
        result = subprocess.run([sys.executable, '-B', str(source)], cwd=root,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__': unittest.main()
