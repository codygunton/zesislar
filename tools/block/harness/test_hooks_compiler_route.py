from pathlib import Path
import ast
import tempfile
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'code'))
import entry_chain_provider as provider

HOOKS = 'ZesuSsz.Automation.Hooks'
PROJECTION = Path('/home/cody/zesislar/_build/agents/worker-build-2/v12-F6-hooks-projection-v1/projection/Hooks.v')


class HooksCompilerRouteTests(unittest.TestCase):
    def source(self, text):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name) / 'Hooks.v'
        path.write_text(text)
        return path

    def test_exact_projection_uses_mcp(self):
        self.assertFalse(provider.hooks_plugin_build(HOOKS, PROJECTION))

    def test_altered_projection_refuses(self):
        path = self.source(PROJECTION.read_text() + '\n')
        with self.assertRaisesRegex(ValueError, 'trusted dependency plugin declaration changed'):
            provider.hooks_plugin_build(HOOKS, path)

    def test_unchanged_plugin_fallback(self):
        path = self.source('Declare ML Module "zesu-signature-gates.plugin".\n')
        self.assertTrue(provider.hooks_plugin_build(HOOKS, path))

    def test_wrong_plugin_refuses(self):
        path = self.source('Declare ML Module "other.plugin".\n')
        with self.assertRaisesRegex(ValueError, 'trusted dependency plugin declaration changed'):
            provider.hooks_plugin_build(HOOKS, path)

    def test_duplicate_plugin_refuses(self):
        path = self.source('Declare ML Module "zesu-signature-gates.plugin".\n' * 2)
        with self.assertRaisesRegex(ValueError, 'trusted dependency plugin declaration changed'):
            provider.hooks_plugin_build(HOOKS, path)

    def test_other_modules_keep_mcp(self):
        path = self.source('Definition ordinary := 0.\n')
        self.assertFalse(provider.hooks_plugin_build('Other.Module', path))

    def test_router_is_connected_to_mcp_branch(self):
        tree = ast.parse(Path(provider.__file__).read_text())
        branches = [node for node in ast.walk(tree) if isinstance(node, ast.If)
                    and isinstance(node.test, ast.Call)
                    and isinstance(node.test.func, ast.Name)
                    and node.test.func.id == 'hooks_plugin_build']
        self.assertEqual(len(branches), 1)
        strings = [node.value for node in ast.walk(ast.Module(body=branches[0].orelse, type_ignores=[]))
                   if isinstance(node, ast.Constant) and isinstance(node.value, str)]
        self.assertIn('rocq_compile_file', strings)


if __name__ == '__main__':
    unittest.main()
