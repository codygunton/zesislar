"""Reject missing or mismatched objects in the exact replay view."""
import unittest

from replay_object_view import select_closure


def row(name, bank='original'):
    return {'object': {'path': '/' + name + '.vo', 'sha256': name}, 'bank': bank}


class ViewClosureTests(unittest.TestCase):
    def inspector(self, imports, compatible=True):
        def inspect(objects, checks):
            return {'objects': [{'path': path, 'module': path[1:-3],
                     'imports': [{'module': name} for name in imports.get(path[1:-3], [])]}
                    for path in objects],
                    'checks': [dict(check, compatible=compatible) for check in checks]}
        return inspect

    def test_original_and_ordinary_umbrella_keep_all_transitive_checks(self):
        objects = {'Original': row('Original'), 'Umbrella': row('Umbrella', 'umbrella')}
        selected, compared = select_closure(objects, lambda name: row(name) if name == 'Base' else None,
            {'Extra': row('Extra', 'umbrella')},
            self.inspector({'Original': ['Base'], 'Umbrella': ['Base', 'Extra'], 'Extra': ['Base']}))
        self.assertEqual(set(selected), {'Original', 'Umbrella', 'Base', 'Extra'})
        self.assertEqual(len(compared['checks']), 4)
        self.assertEqual(selected['Base']['bank'], 'original')

    def test_missing_dependency_refuses_before_copy(self):
        with self.assertRaisesRegex(ValueError, 'lacks an imported object: Missing'):
            select_closure({'Original': row('Original')}, lambda name: None, {},
                           self.inspector({'Original': ['Missing']}))

    def test_mismatched_original_is_not_replaced_by_a_donor(self):
        original = row('Dependency')
        donor = {'object': {'path': '/Other.vo', 'sha256': 'other'}, 'bank': 'umbrella'}
        with self.assertRaisesRegex(ValueError, 'mismatched md_deps'):
            select_closure({'Original': row('Original')}, lambda name: original,
                           {'Dependency': donor}, self.inspector({'Original': ['Dependency']}, False))
        self.assertEqual(original['object']['path'], '/Dependency.vo')

    def test_canonical_module_alias_refuses(self):
        with self.assertRaisesRegex(ValueError, 'canonical module'):
            select_closure({'Original': row('Wrong')}, lambda name: None, {}, self.inspector({}))

    def test_repeated_import_name_refuses(self):
        with self.assertRaisesRegex(ValueError, 'repeats an imported module'):
            select_closure({'Original': row('Original')}, lambda name: row(name), {},
                           self.inspector({'Original': ['Base', 'Base']}))

    def test_dependency_cycles_do_not_skip_digest_checks(self):
        selected, compared = select_closure({'A': row('A')}, lambda name: row(name), {},
                                           self.inspector({'A': ['B'], 'B': ['A']}))
        self.assertEqual(set(selected), {'A', 'B'})
        self.assertEqual(len(compared['checks']), 2)

    def test_inspector_cannot_return_fewer_comparisons(self):
        ordinary = self.inspector({'A': ['B']})
        def incomplete(objects, checks):
            value = ordinary(objects, checks)
            value['checks'] = []
            return value
        with self.assertRaisesRegex(ValueError, 'md_deps'):
            select_closure({'A': row('A')}, lambda name: row(name), {}, incomplete)


class OrdinaryUmbrellaTests(unittest.TestCase):
    def setUp(self):
        import tempfile
        from pathlib import Path
        from entry_chain import binding, save
        from unittest.mock import patch
        self.temporary=tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root=Path(self.temporary.name)
        self.save,self.binding=save,binding
        self.source=self.root/'Hints.v';self.source.write_text('Exact source fixture.\n')
        self.obj=self.root/'Hints.vo';self.obj.write_text('Exact object fixture.\n')
        receipt={'source':binding(self.source),'object':binding(self.obj),
                 'import_provenance':{'owned_workspace':str(self.root)},
                 'normalized_flags':[],'compiler':{'path':'/compiler','sha256':'compiler'}}
        self.reference=self.write('OBJECT.json',receipt)
        job=self.root/'job';job.mkdir()
        result=self.write('job/RESULT.json',{'success':True})
        self.write('job/CLOSURE.json',{'all_owned_actors_closed':True,'claim_key':'owned'})
        self.write('job/RELEASE.json',{'released':True,'bytes':24,'claim_key':'owned'})
        readiness=self.write('READINESS.json',{'prerequisite_result':result,'all_required_compiles_passed':True})
        self.write('RESULT.json',{'success':True,'status':'declarations_passed','prerequisites':result})
        self.ready={'declarations_only':True,'control_session':None,'readiness':readiness,
                    'jobs':[{'phase':'prerequisites','output':str(job),'claim_bytes':24}],
                    'object_imports':{'ZesuSsz.Compliance.DecodeItemHints':self.reference}}
        self.ready_reference=self.write('READY-RUNTIME.json',self.ready)
        self.origin=patch('replay_object_view._record',return_value=({},self.root))
        self.record=self.origin.start();self.addCleanup(self.origin.stop)
        constants=patch('replay_object_view.SOURCE_SHA',binding(self.source)['sha256'])
        constants.start();self.addCleanup(constants.stop)

    def write(self,name,value):
        path=self.root/name;self.save(path,value);return self.binding(path)

    def validate(self):
        from replay_object_view import ordinary_umbrella
        return ordinary_umbrella(self.ready_reference,self.reference)

    def test_ordinary_receipt_uses_the_existing_full_validator(self):
        self.validate()
        self.record.assert_called_once()
        self.assertEqual(self.record.call_args.args[1],'ZesuSsz.Compliance.DecodeItemHints')

    def test_missing_release_refuses_before_receipt_authentication(self):
        (self.root/'job/RELEASE.json').unlink()
        with self.assertRaises(FileNotFoundError):self.validate()
        self.record.assert_not_called()

    def test_wrong_release_amount_refuses(self):
        self.write('job/RELEASE.json',{'released':True,'bytes':1,'claim_key':'owned'})
        with self.assertRaisesRegex(ValueError,'closed accepted'):self.validate()
        self.record.assert_not_called()

    def test_gate_origin_cannot_authorize_the_new_umbrella(self):
        import json
        receipt=json.loads((self.root/'OBJECT.json').read_text())
        receipt['schema']='entry-chain.object-import-migration.v1'
        self.reference=self.write('OBJECT.json',receipt)
        self.ready['object_imports']['ZesuSsz.Compliance.DecodeItemHints']=self.reference
        self.ready_reference=self.write('READY-RUNTIME.json',self.ready)
        with self.assertRaisesRegex(ValueError,'ordinary compiler receipt'):self.validate()
        self.record.assert_not_called()

    def test_changed_object_refuses(self):
        self.obj.write_text('Changed object fixture.\n')
        with self.assertRaisesRegex(ValueError,'input changed'):self.validate()
        self.record.assert_not_called()

    def test_changed_ordinary_receipt_cannot_replace_the_READY_member(self):
        self.ready['object_imports']['ZesuSsz.Compliance.DecodeItemHints']={'path':'/another','sha256':'another'}
        self.ready_reference=self.write('READY-RUNTIME.json',self.ready)
        with self.assertRaisesRegex(ValueError,'closed accepted'):self.validate()
        self.record.assert_not_called()


class ProjectPlacementTests(unittest.TestCase):
    def test_real_MCP_parser_resolves_both_roots_to_the_same_owned_objects(self):
        import tempfile
        from pathlib import Path
        from entry_chain import binding
        from replay_object_view import install_projects
        from rocq_mcp.server import _parse_project_flags
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary)
            source=root/'source';source.mkdir()
            project=b'-Q default/Library Library\n-R default/ZesuSsz ZesuSsz\n-I default/Plugin\n'
            references=[]
            for name in ['_CoqProject','_RocqProject']:
                path=source/name;path.write_bytes(project);references.append(binding(path))
            output=root/'view';output.mkdir()
            installed=install_projects(references,output)
            for name in ['Library','ZesuSsz','Plugin']:(output/'artifacts/default'/name).mkdir()
            objects=output/'artifacts/default/Library/Value.vo';objects.write_bytes(b'object fixture')
            returned_flags=_parse_project_flags(output)
            artifact_flags=_parse_project_flags(output/'artifacts')
            self.assertEqual(returned_flags,artifact_flags)
            self.assertEqual(returned_flags,['-Q','default/Library','Library','-R','default/ZesuSsz','ZesuSsz','-I','default/Plugin'])
            for workspace in [output,output/'artifacts']:
                selected=(workspace/returned_flags[1]/'Value.vo').resolve()
                self.assertEqual(selected,objects.resolve())
                self.assertTrue(selected.is_relative_to((output/'artifacts/default').resolve()))
                for name in ['_CoqProject','_RocqProject']:
                    self.assertEqual((workspace/name).read_bytes(),project)
            self.assertEqual(len(installed),4)
            self.assertEqual([Path(row['path']).read_bytes() for row in references],[project,project])
