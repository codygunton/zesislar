"""Check the shared configurable probe limit in both public guards."""
import os
import subprocess
import unittest
from pathlib import Path
HERE = Path(__file__).resolve().parent

class ProbeLimits(unittest.TestCase):
    def run_reason(self, count, key='new', limit=None):
        results = []
        for path in (HERE/'runtime-tools/resource_guard.sh', HERE.parents[1]/'resource_guard.sh'):
            text = path.read_text()
            start = text.index('probe_admission_reason() {')
            function = text[start:text.index('\n}', start)+2]
            script = "probe_keys() { for ((i=0;i<"+str(count)+";i++)); do printf 'aggregate:a%s\\n' \"$i\"; done; }; probe_owner_aggregate() { echo \"$2\"; }; process_start() { echo 1; }; "+function+"; ZESU_AGGREGATE_SLICE="+key+"; probe_admission_reason 123"
            env = dict(os.environ)
            env.pop('ZESU_PROBE_AGGREGATE_LIMIT', None)
            if limit is not None: env['ZESU_PROBE_AGGREGATE_LIMIT'] = limit
            results.append(subprocess.run(['/bin/bash','-c',script], env=env, capture_output=True, text=True))
        return results

    def test_default_limit_accepts_fifteen_and_refuses_sixteen(self):
        for result in self.run_reason(15):
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), '')
        for count in (16, 17):
            for result in self.run_reason(count):
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn('16-aggregate limit', result.stdout)

    def test_existing_nested_aggregate_keeps_its_slot(self):
        for result in self.run_reason(16, 'a0'):
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), '')

    def test_explicit_limit_has_exact_boundary(self):
        for result in self.run_reason(7, limit='8'):
            self.assertEqual(result.stdout.strip(), '')
        for result in self.run_reason(8, limit='8'):
            self.assertIn('8-aggregate limit', result.stdout)

    def test_invalid_configuration_refuses(self):
        for limit in ('0', '-1', '1.5', 'abc', '9999999999'):
            for result in self.run_reason(0, limit=limit):
                self.assertEqual(result.returncode, 2)
                self.assertIn('invalid probe aggregate limit', result.stderr)

if __name__ == '__main__': unittest.main()
