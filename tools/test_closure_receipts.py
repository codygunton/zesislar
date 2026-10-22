"""Reject unapproved object changes and unsupported physical compiler limits."""
import copy
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from closure_receipts import ObjectBindings, validate_physical_receipt
from promotion_verification import digest


def arm(root):
    private = root / '_build/owned/default'
    private.mkdir(parents=True)
    for name in ('Target', 'Dependency'):
        (private / (name + '.vo')).write_bytes(name.encode())
    return dict(workspace=str(root), build_dir=str(private.parent),
                objects=[dict(path=str(path), sha256=digest(path)) for path in sorted(private.glob('*.vo'))])


class ObjectTests(unittest.TestCase):
    def fixture(self, directory):
        root = Path(directory)
        return ObjectBindings(arm(root / 'baseline'), arm(root / 'candidate'))

    def target(self, bindings, name='Target'):
        return Path(bindings.candidate['build_dir']) / 'default' / (name + '.vo')

    def arguments(self, bindings):
        return dict(workspace=bindings.candidate['workspace'],
                    file=str(Path(bindings.candidate['workspace']) / 'Target.v'))

    def test_every_baseline_object_remains_fixed(self):
        with tempfile.TemporaryDirectory() as directory:
            bindings = self.fixture(directory)
            original = copy.deepcopy(bindings.baseline)
            (Path(bindings.baseline['build_dir']) / 'default/Dependency.vo').write_bytes(b'Changed baseline')
            with self.assertRaisesRegex(ValueError, 'baseline object changed'):
                bindings.check()
            with self.assertRaisesRegex(ValueError, 'baseline object changed'):
                bindings.after('rocq_compile_file', self.arguments(bindings), dict(success=True))
            self.assertEqual(bindings.baseline, original)

    def test_successful_named_compilation_updates_only_its_target(self):
        with tempfile.TemporaryDirectory() as directory:
            bindings = self.fixture(directory)
            bindings.check()
            self.target(bindings).write_bytes(b'Recompiled target')
            bindings.after('rocq_compile_file', self.arguments(bindings), dict(success=True))
            bindings.check()
            self.assertEqual(len(bindings.transitions), 1)
            self.assertEqual(bindings.transitions[0]['path'], str(self.target(bindings)))

    def test_success_does_not_authorize_a_changed_dependency(self):
        with tempfile.TemporaryDirectory() as directory:
            bindings = self.fixture(directory)
            before = copy.deepcopy(bindings.candidate)
            self.target(bindings).write_bytes(b'Recompiled target')
            self.target(bindings, 'Dependency').write_bytes(b'Unrelated change')
            with self.assertRaisesRegex(ValueError, 'dependency object changed'):
                bindings.after('rocq_compile_file', self.arguments(bindings), dict(success=True))
            self.assertEqual(bindings.candidate, before)
            self.assertEqual(bindings.transitions, [])

    def test_failed_compile_or_statement_check_cannot_update_a_target(self):
        for tool, result in [('rocq_compile_file', dict(success=False)),
                             ('rocq_verify', dict(success=True, verification_method='module_m'))]:
            with self.subTest(tool=tool), tempfile.TemporaryDirectory() as directory:
                bindings = self.fixture(directory)
                self.target(bindings).write_bytes(b'Changed target')
                with self.assertRaisesRegex(ValueError, 'without its successful compilation'):
                    bindings.after(tool, self.arguments(bindings), result)
                self.assertEqual(bindings.transitions, [])

    def test_unlisted_additions_and_removals_refuse(self):
        for action in ('add', 'remove'):
            with self.subTest(action=action), tempfile.TemporaryDirectory() as directory:
                bindings = self.fixture(directory)
                if action == 'add':
                    self.target(bindings, 'Unexpected').write_bytes(b'Unlisted object')
                else:
                    self.target(bindings, 'Dependency').unlink()
                with self.assertRaises(ValueError):
                    bindings.after('rocq_compile_file', self.arguments(bindings), dict(success=True))


class PhysicalReceiptTests(unittest.TestCase):
    def fixture(self):
        executable = dict(path='/pinned/bin/coqc', sha256='1' * 64)
        receipt = dict(pid=123, start_ticks=456, executable=executable['path'],
            executable_sha256=executable['sha256'], argv=[executable['path'], 'Exact.v'],
            cwd='/owned/private/default', cgroup='/fixture.scope',
            memory_max_bytes=64 * 1024**3, memory_swap_max_bytes=0,
            cpu_limit_line='Max cpu time              unlimited            unlimited            seconds',
            cpu_quota_controls=[dict(path='/sys/fs/cgroup/fixture.scope/cpu.max', present=False),
                                dict(path='/sys/fs/cgroup/cpu.max', present=True, value='max 100000')])
        return executable, receipt

    def test_missing_leaf_uses_explicit_ancestor_receipts(self):
        executable, receipt = self.fixture()
        validate_physical_receipt(receipt, executable)

    def test_memory_swap_cpu_and_compiler_mismatches_refuse(self):
        executable, receipt = self.fixture()
        for field, value in [('memory_max_bytes', 32 * 1024**3), ('memory_swap_max_bytes', 1024),
                             ('cpu_limit_line', 'Max cpu time unlimited 1200 seconds'),
                             ('executable_sha256', '2' * 64), ('argv', ['/resource-wrapper'])]:
            with self.subTest(field=field), self.assertRaises(ValueError):
                validate_physical_receipt(dict(receipt, **{field: value}), executable)

    def test_incomplete_or_bounded_cpu_quota_refuses(self):
        executable, receipt = self.fixture()
        for controls in (receipt['cpu_quota_controls'][:1],
                [dict(row, value='100000 100000') if row['present'] else row for row in receipt['cpu_quota_controls']],
                [dict(path=row['path'], present=False) for row in receipt['cpu_quota_controls']]):
            with self.subTest(controls=controls), self.assertRaises(ValueError):
                validate_physical_receipt(dict(receipt, cpu_quota_controls=controls), executable)


if __name__ == '__main__':
    unittest.main()
