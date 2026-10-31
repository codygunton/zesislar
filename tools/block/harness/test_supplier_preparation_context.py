"""Check the actual preparation handoff without staging or running a proof."""
from copy import deepcopy
import ast
import inspect
import json
from pathlib import Path
from types import SimpleNamespace
import unittest

import memory_policy as policy
import scratch
import test_supplier_ready as supplier_fixtures

binding = supplier_fixtures.binding


class SupplierPreparationContext(unittest.TestCase):
    def setUp(self):
        self.fixture = supplier_fixtures.SupplierReady()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.case = policy.read(policy.PORT_AUTHORITY)['cases'][0]
        self.function = ast.parse(inspect.getsource(scratch.prepare)).body[0]

    def context(self, *, external=False, physical_change=None, graph_change=False):
        fixture = self.fixture
        if external:
            fixture.external_installation()
        workspace = fixture.root / 'native-owned'
        workspace.mkdir()
        for row in fixture.modules:
            for kind in ['source', 'object']:
                path = Path(row[kind]['path'])
                if path.is_relative_to(fixture.workspace):
                    copied = workspace / path.relative_to(fixture.workspace)
                    copied.parent.mkdir(parents=True, exist_ok=True)
                    copied.write_bytes(path.read_bytes())
        out = fixture.root / 'native-output'
        out.mkdir()
        graph = json.loads(Path(fixture.graph['path']).read_text())
        if graph_change:
            graph['import_edges'] = []
        (out / 'INVALIDATION.json').write_text(json.dumps(graph))
        config = fixture.config()
        # The parent graph intentionally differs from the prepared graph.
        config['cache_import_graph'] = fixture.save('PARENT-GRAPH.json', dict(import_edges=[]))
        if physical_change:
            config['physical_flags'] = physical_change(config['physical_flags'])
        modules = deepcopy(fixture.mapping)
        modules[self.case['module']] = self.case['source']['path']
        parsed = [word.replace(str(fixture.workspace), str(workspace)) for word in fixture.flags]
        namespace = dict(scratch.__dict__, c=config, source=fixture.workspace, workspace=workspace,
                         out=out, modules=modules, pre=dict(ordered_modules=[]),
                         a=SimpleNamespace(declarations_only=False),
                         _parse_project_flags=lambda path: list(parsed))
        names = {'physical_flags', 'expected_mcp_flags', 'import_graph'}
        nodes = [node for node in self.function.body if isinstance(node, ast.Assign) and
                 any(isinstance(target, ast.Name) and target.id in names for target in node.targets)]
        branch = next(node for node in self.function.body if isinstance(node, ast.If) and
                      ast.unparse(node.test) == 'a.admission_profile')
        nodes.append(next(node for node in branch.body if isinstance(node, ast.Assign) and
                          any(isinstance(target, ast.Name) and target.id == 'actual_config'
                              for target in node.targets)))
        exec(compile(ast.fix_missing_locations(ast.Module(body=nodes, type_ignores=[])),
                     '<actual-preparation-context>', 'exec'), namespace)
        profile = dict(schema='scratch.admission-profile.v1', kind=policy.PORT_KIND,
                       authority=deepcopy(policy.PORT_AUTHORITY), memory_route='measured_native',
                       supplier_ready=fixture.freeze())
        profile_binding = fixture.save('PROFILE.json', profile)
        job = dict(key=self.case['block'], phase='native', ordered_modules=[], target=dict(
            module=self.case['module'], pc=self.case['pc'],
            source_sha256=self.case['source']['sha256'], statement_sha256=self.case['statement_sha256']))
        return namespace, profile_binding, job

    def test_native_supplier_handoff_uses_relocated_flags_and_actual_graph(self):
        namespace, profile, job = self.context()
        actual = namespace['actual_config']
        workload = policy.workload_for_job(profile, job, actual)
        self.assertEqual(workload['kind'], policy.PORT_KIND)
        self.assertEqual(actual['cache_import_graph'], binding(namespace['out'] / 'INVALIDATION.json'))
        self.assertNotEqual(actual['cache_import_graph'], namespace['c']['cache_import_graph'])

    def test_parent_root_flags_reproduce_the_original_refusal(self):
        namespace, profile, job = self.context()
        inherited = deepcopy(namespace['actual_config'])
        inherited['physical_flags'] = namespace['c']['physical_flags']
        with self.assertRaisesRegex(ValueError, 'staged physical_flags differs'):
            policy.workload_for_job(profile, job, inherited)

    def test_checked_projection_equals_the_final_runtime_projection(self):
        namespace, _, _ = self.context()
        final_nodes = [node for node in self.function.body if isinstance(node, ast.Assign) and
                       any(isinstance(target, ast.Subscript) and ast.unparse(target) in
                           {"c['physical_flags']", "c['expected_mcp_flags']"} for target in node.targets)]
        update = next(node for node in self.function.body if isinstance(node, ast.Expr) and
                      isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute)
                      and ast.unparse(node.value.func) == 'c.update' and
                      any(keyword.arg == 'cache_import_graph' for keyword in node.value.keywords))
        graph_value = next(keyword.value for keyword in update.value.keywords
                           if keyword.arg == 'cache_import_graph')
        final_nodes.append(ast.Assign(targets=[ast.Subscript(value=ast.Name(id='c', ctx=ast.Load()),
            slice=ast.Constant(value='cache_import_graph'), ctx=ast.Store())], value=graph_value))
        actual = deepcopy(namespace['actual_config'])
        exec(compile(ast.fix_missing_locations(ast.Module(body=final_nodes, type_ignores=[])),
                     '<actual-final-runtime-fields>', 'exec'), namespace)
        for field in ['physical_flags', 'expected_mcp_flags', 'cache_import_graph']:
            self.assertEqual(actual[field], namespace['c'][field])

    def test_changed_external_mapping_still_refuses(self):
        namespace, profile, job = self.context(external=True, physical_change=lambda words:
            [word.replace('/home/cody/islaris/_opam/lib/coq/theories',
                          '/home/cody/islaris/_opam/lib/coq/other-theories') for word in words])
        with self.assertRaisesRegex(ValueError, 'staged physical_flags differs'):
            policy.workload_for_job(profile, job, namespace['actual_config'])

    def test_changed_compiler_flag_still_refuses(self):
        namespace, profile, job = self.context(physical_change=lambda words: words + ['-impredicative-set'])
        with self.assertRaisesRegex(ValueError, 'staged physical_flags differs'):
            policy.workload_for_job(profile, job, namespace['actual_config'])

    def test_changed_prepared_import_closure_still_refuses(self):
        namespace, profile, job = self.context(graph_change=True)
        with self.assertRaisesRegex(ValueError, 'staged import closure differs'):
            policy.workload_for_job(profile, job, namespace['actual_config'])


if __name__ == '__main__':
    unittest.main()
