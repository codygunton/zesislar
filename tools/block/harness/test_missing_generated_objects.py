"""Exercise missing-object discovery without a proof, claim, or compiler."""
from pathlib import Path
import tempfile
import unittest

import scratch
from entry_chain_stage import invalidation


class MissingGeneratedObjects(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.workspace = Path(self.directory.name)
        self.modules = {name: name.replace('.', '/')+'.v' for name in (
            'A.Entry', 'A.Structural', 'A.Caller',
            'B.Entry', 'B.Structural', 'B.Caller',
            'Rules', 'RuleSupport', 'Unrelated.Entry')}
        for relative in self.modules.values():
            source = self.workspace/relative
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text('Definition unchanged := 0.\n')
            source.with_suffix('.vo').write_bytes(b'existing compiled object')
        self.edges = [
            {'from':'A.Caller', 'to':'A.Structural'},
            {'from':'A.Structural', 'to':'A.Entry'},
            {'from':'B.Caller', 'to':'B.Structural'},
            {'from':'B.Structural', 'to':'B.Entry'},
            {'from':'Rules', 'to':'RuleSupport'}]
        self.forward = {}
        for row in self.edges:
            self.forward.setdefault(row['from'], set()).add(row['to'])

    def remove_object(self, name):
        (self.workspace/self.modules[name]).with_suffix('.vo').unlink()

    def missing(self, targets):
        return scratch.missing_prerequisite_objects(
            targets, self.forward, self.modules, self.workspace)

    def test_union_discovers_unchanged_second_entry_and_orders_its_importer(self):
        before = (self.workspace/self.modules['B.Entry']).read_bytes()
        self.remove_object('B.Entry')
        missing = self.missing(['A.Caller', 'B.Caller'])
        self.assertEqual(missing, ['B.Entry'])
        self.assertEqual((self.workspace/self.modules['B.Entry']).read_bytes(), before)
        plan = invalidation(self.edges, missing, ['A.Caller', 'B.Caller'])
        self.assertEqual(plan['prerequisites'], ['B.Entry', 'B.Structural'])
        self.assertEqual(self.missing(['A.Caller']), [])

    def test_single_target_keeps_its_original_scope(self):
        self.remove_object('A.Entry')
        self.remove_object('B.Entry')
        self.assertEqual(self.missing(['A.Caller']), ['A.Entry'])
        self.assertEqual(self.missing(['B.Caller']), ['B.Entry'])

    def test_rule_only_declaration_uses_rule_dependencies(self):
        self.remove_object('RuleSupport')
        self.remove_object('A.Entry')
        missing = self.missing(['Rules'])
        self.assertEqual(missing, ['RuleSupport'])
        plan = invalidation(self.edges, missing, ['Rules'])
        self.assertEqual(plan['ordered_required'], ['RuleSupport', 'Rules'])

    def test_existing_objects_and_unrelated_missing_objects_stay_reused(self):
        self.remove_object('Unrelated.Entry')
        self.assertEqual(self.missing(['A.Caller', 'B.Caller']), [])

    def test_vos_file_does_not_replace_the_required_vo(self):
        self.remove_object('B.Entry')
        (self.workspace/self.modules['B.Entry']).with_suffix('.vos').write_bytes(b'partial')
        self.assertEqual(self.missing(['A.Caller', 'B.Caller']), ['B.Entry'])


if __name__ == '__main__':
    unittest.main()
