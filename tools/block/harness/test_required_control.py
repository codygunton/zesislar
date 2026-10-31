from pathlib import Path
import ast
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'code'))
import entry_chain_provider as provider


class RequiredControlTests(unittest.TestCase):
    def test_optional_failure_remains_supported(self):
        self.assertFalse(provider.control_step_required({}))
        provider.require_control_result(False, {'success': False, 'error': 'expected'})

    def test_required_success(self):
        required = provider.control_step_required({'required': True})
        provider.require_control_result(required, {'success': True})

    def test_required_failure_preserves_result(self):
        result = {'success': False, 'error': 'exact kernel mismatch'}
        with self.assertRaisesRegex(provider.ToolFailure, 'exact kernel mismatch') as raised:
            provider.require_control_result(True, result)
        self.assertIs(raised.exception.result, result)

    def test_truthy_success_does_not_pass(self):
        with self.assertRaises(provider.ToolFailure):
            provider.require_control_result(True, {'success': 'yes'})

    def test_malformed_requirement_refuses(self):
        with self.assertRaisesRegex(ValueError, 'must be Boolean'):
            provider.control_step_required({'required': 'yes'})

    def test_failure_stops_later_work(self):
        later = []
        with self.assertRaises(provider.ToolFailure):
            provider.require_control_result(True, {'success': False, 'error': 'identity failed'})
            later.append('solver')
        self.assertEqual(later, [])

    def test_guard_is_in_actual_session_loop(self):
        tree = ast.parse(Path(provider.__file__).read_text())
        loops = [node for node in ast.walk(tree) if isinstance(node, ast.For)
                 and isinstance(node.target, ast.Name) and node.target.id == 'step']
        self.assertEqual(len(loops), 1)
        body = loops[0].body
        first = body[0]
        self.assertIsInstance(first, ast.Assign)
        self.assertEqual(first.value.func.id, 'control_step_required')
        guard = [i for i, node in enumerate(body) if isinstance(node, ast.Expr)
                 and isinstance(node.value, ast.Call)
                 and isinstance(node.value.func, ast.Name)
                 and node.value.func.id == 'require_control_result']
        self.assertEqual(len(guard), 1)
        self.assertIsInstance(body[guard[0] + 1], ast.If)


if __name__ == '__main__':
    unittest.main()
