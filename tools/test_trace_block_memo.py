import ast, copy, sys, types, unittest
from pathlib import Path
from unittest.mock import patch
P = Path(__file__).resolve().parent / 'block'

def branch(tree):
    server = next((n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'server_main'))
    tool = next((n for n in server.body if isinstance(n, ast.AsyncFunctionDef) and n.name == 'rocq_trace_run'))
    execute = next((n for n in tool.body if isinstance(n, ast.FunctionDef) and n.name == 'execute'))
    attempt = next((n for n in execute.body if isinstance(n, ast.Try)))
    return (server, attempt)

class MemoTests(unittest.TestCase):

    def test_public_options_and_legacy_boundary(self):
        tree = ast.parse((P / 'trace_block_mcp.py').read_text())
        _, attempt = branch(tree)
        body = [attempt.body[0], ast.Return(value=ast.Name(id='after', ctx=ast.Load()))]
        args = ast.arguments(posonlyargs=[], args=[ast.arg(arg=x) for x in ['pet', 'state', 'command', 'bounded']], kwonlyargs=[], kw_defaults=[], defaults=[])
        fn = ast.FunctionDef(name='perform', args=args, body=body, decorator_list=[])
        scope = {}
        exec(compile(ast.fix_missing_locations(ast.Module(body=[fn], type_ignores=[])), 'actual-memo-branch', 'exec'), scope)

        class Opts:

            def __init__(self, **kwargs):
                self.options = kwargs

        class Pet:

            def run(self, *args, **kwargs):
                self.call = (args, kwargs)
                return 'result'
        with patch.dict(sys.modules, {'pytanque': types.SimpleNamespace(Opts=Opts)}):
            pet = Pet()
            self.assertEqual(scope['perform'](pet, 1, 'command.', True), 'result')
            self.assertEqual(pet.call[0], (1, 'command.'))
            self.assertIsNone(pet.call[1]['timeout'])
            self.assertEqual(pet.call[1]['opts'].options, {'memo': False, 'hash': True})
            self.assertEqual(scope['perform'](pet, 1, 'command.', False), 'result')
            self.assertEqual(pet.call, ((1, 'command.'), {'timeout': None}))
if __name__ == '__main__':
    unittest.main()
