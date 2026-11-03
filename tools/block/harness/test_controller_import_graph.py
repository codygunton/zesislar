"""Check reuse helpers with the controller's isolated Python import paths."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE / 'code'))
PROBE = r'''
import hashlib,json,sys
from pathlib import Path
paths=json.loads(sys.argv[1]);workspace=Path(sys.argv[2])
sys.path[:0]=paths
import object_imports as O
import closed_compilation_origin as C
import gate_object_origin as G
assert C.KIND=='accepted-closed-compilations'
assert G.KIND=='accepted-correctness-gate-objects'
assert 'entry_chain_stage' not in sys.modules
assert O.graph_closure(['Owner'],{'Owner':['Dependency']})=={'Owner','Dependency'}
modules={'Owner':'Owner.v','Dependency':'Dependency.v'}
for relative in modules.values():
    source=workspace/relative
    source.write_text('(* Nonproof source fixture. *)\n')
    source.with_suffix('.vo').write_bytes(b'Nonproof object fixture')
compiler=workspace/'nonproof-compiler';compiler.write_bytes(b'Never executed')
binding=lambda p:{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
flags=['-Q',str(workspace),'Example']
edges=[{'from':'Owner','to':'Dependency'}]
result=O.compatibility(['Owner'],edges,modules,workspace,{},binding(compiler),flags)
assert result['rebuild_modules']==['Dependency','Owner']
graph=workspace/'GRAPH.json';graph.write_text(json.dumps({'import_edges':edges}))
config={'cache_import_graph':binding(graph),'object_imports':{},
        'jobs':[{'phase':'native','target':{'module':'Owner'}}]}
runtime={'module_files':modules,'ordered_modules':[],
         'physical_compiler':binding(compiler),'physical_flags':flags}
try:
    O.require_reuse(config,runtime,workspace)
except ValueError as error:
    assert 'staged plan must rebuild an owned object: Dependency' in str(error)
else:
    raise AssertionError('The required import lost its reuse check.')
runtime['ordered_modules']=['Dependency']
assert not O.require_reuse(config,runtime,workspace)['rebuild_modules']
assert 'entry_chain_stage' not in sys.modules
print(json.dumps({'helper':str(Path(O.graph_closure.__code__.co_filename).resolve()),
                  'reuse':str(Path(O.__file__).resolve()),'strict_checks':True}))
'''


class ControllerImportGraph(unittest.TestCase):
    def probe(self, paths, expected):
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run([sys.executable, '-I', '-B', '-c', PROBE,
                                     json.dumps([str(path) for path in paths]), directory],
                                    cwd=directory, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        value = json.loads(result.stdout)
        self.assertTrue(value['strict_checks'])
        self.assertEqual(value['helper'], str((expected / 'import_graph.py').resolve()))
        self.assertEqual(value['reuse'], str((expected / 'object_imports.py').resolve()))

    def test_exact_versioned_controller_paths(self):
        self.probe([HERE / 'code', ROOT / 'tools/block', ROOT / 'tools'], HERE / 'code')

    def test_owned_staged_helpers_without_harness_directory(self):
        from clone_copy import copy2
        layout = json.loads((HERE / 'TOOL-LAYOUT.json').read_text())
        self.assertEqual(layout['block/import_graph.py'], 'code/import_graph.py')
        self.assertEqual(layout['block/object_imports.py'], 'code/object_imports.py')
        self.assertEqual(layout['block/gate_object_origin.py'], 'code/gate_object_origin.py')
        build = ROOT / '_build'
        build.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=build) as directory:
            tools = Path(directory) / 'tools'
            for relative, source in layout.items():
                target = tools / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                copy2(HERE / source, target)
            self.assertFalse((tools / 'block/harness').exists())
            self.probe([tools / 'block', tools], tools / 'block')


if __name__ == '__main__':
    unittest.main()
