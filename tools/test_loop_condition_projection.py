"""Keep refused loop assumptions out of both entries and evaluator seeds."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from loop_condition_projection import project_loop_conditions


class LoopConditionProjectionTests(unittest.TestCase):
    def render(self, condition):
        if condition.get('local'):
            raise ValueError('A trace-local expression has no source binder')
        return condition['source']

    def test_checked_relation_keeps_only_its_renderable_dependencies(self):
        conditions = [{'source': '0 <= cursor'}, {'source': 'cursor < end'}, {'source': 'extra'}]
        relations = [{'kind': 'affine_cursor'}]
        result = project_loop_conditions(conditions, relations, [[0, 1]], render=self.render)
        self.assertEqual(result['condition_indices'], [0, 1])
        self.assertEqual(result['conditions'], conditions[:2])
        self.assertEqual(result['relations'], relations)
        self.assertEqual(result['condition_records'][2]['status'], 'unused')

    def test_refused_dependency_drops_its_relation_and_records_every_omission(self):
        conditions = [{'source': 'bound'}, {'source': 'local', 'local': True}]
        before = deepcopy(conditions)
        result = project_loop_conditions(conditions, [{'kind': 'affine_cursor'}], [[0, 1]], render=self.render)
        self.assertEqual(result['relations'], [])
        self.assertEqual(result['conditions'], [])
        self.assertEqual(result['original_conditions'], before)
        self.assertEqual(conditions, before)
        self.assertEqual({row['kind'] for row in result['refusals']},
            {'loop_condition_refusal', 'loop_relation_refusal', 'loop_unused_condition'})
        self.assertEqual(result['relation_records'][0]['original_dependencies'], [0, 1])

    def test_one_checked_source_recheck_can_remove_a_refused_dependency(self):
        conditions = [{'source': 'bound'}, {'source': 'local', 'local': True}]
        calls = []
        def recheck(relation, available):
            calls.append((relation, available))
            return {'checked': True, 'condition_dependencies': [0], 'source_evidence': {'checks': ['preheader', 'backedge']}}
        result = project_loop_conditions(conditions, [{'kind': 'affine_cursor'}], [[0, 1]],
            render=self.render, recheck=recheck)
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0][1], [(0, conditions[0])])
        self.assertEqual(result['condition_indices'], [0])
        self.assertEqual(len(result['relations']), 1)

    def test_failed_recheck_does_not_retain_a_stronger_assumption(self):
        result = project_loop_conditions([{'source': 'bad', 'local': True}], [{}], [[0]],
            render=self.render, recheck=lambda *_: {'checked': False})
        self.assertEqual(result['conditions'], [])
        self.assertEqual(result['relations'], [])

    def test_invalid_or_refused_recheck_dependencies_refuse(self):
        for dependencies in ([1], [0, 0], [-1], [False], None):
            with self.subTest(dependencies=dependencies):
                with self.assertRaises(ValueError):
                    project_loop_conditions([{'source': 'bound'}, {'source': 'local', 'local': True}],
                        [{}], [[1]], render=self.render, recheck=lambda *_: {
                            'checked': True, 'condition_dependencies': dependencies, 'source_evidence': {'source': 'bound'}})

    def test_missing_evidence_and_invalid_original_dependencies_refuse(self):
        with self.assertRaises(ValueError):
            project_loop_conditions([{'source': 'local', 'local': True}], [{}], [[0]], render=self.render,
                recheck=lambda *_: {'checked': True, 'condition_dependencies': []})
        for dependencies in ([], [[2]], [[True]], [[0, 0]]):
            with self.subTest(dependencies=dependencies), self.assertRaises(ValueError):
                project_loop_conditions([{'source': 'bound'}], [{}], dependencies, render=self.render)


if __name__ == '__main__':
    unittest.main()
