"""Check native coverage, protected baselines, and the one-command coordinator."""
import asyncio
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
import check_function_closure as closure

ROOT = Path(__file__).resolve().parents[1]


class NativeRowsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.commit = closure.Commit(ROOT, '402d2a46bb492a46ab6fec54b3326abd21db1292')

    def overlay(self, path, change):
        base = self.commit
        class Overlay:
            paths = base.paths
            def read(self, selected):
                data = base.read(selected)
                return change(data) if selected == path else data
        return Overlay()

    def test_cfg_coverage_keeps_both_split_theorems(self):
        report = closure.native_rows(self.commit)
        self.assertEqual((report['cfg_pcs'], report['native_theorem_rows']), (24, 25))
        self.assertEqual(len(report['umbrellas']), 1)
        rows = [row for row in report['rows'] if row['pc'] == '800d698c']
        self.assertEqual({row['theorem'] for row in rows}, {
            'DesignedBoundary_800d698cLiteral', 'DesignedBoundary_800d698cShortString'})
        self.assertTrue(all(row['source_sha256'] == hashlib.sha256(
            self.commit.read(row['source'])).hexdigest() for row in report['rows']))

    def test_abort_cannot_supply_production_closure(self):
        current = self.overlay('ZesuSsz/Proofs/DecodeItem/Hand/Block800d6a08.v',
                               lambda data: data.replace(b'Qed.', b'Abort.'))
        with self.assertRaisesRegex(ValueError, 'end with Qed'):
            closure.native_rows(current)

    def test_one_hand_branch_refuses_all_native_coverage(self):
        current = self.overlay('ZesuSsz/Proofs/DecodeItem/Auto/Block800d698cLiteral.v',
                               lambda data: data.replace(b'zesu_block.', b'lia.'))
        with self.assertRaisesRegex(ValueError, 'hand body'):
            closure.native_rows(current)

    def test_missing_split_source_refuses_instead_of_collapsing_pc(self):
        current = self.overlay('', lambda data: data)
        current.paths = current.paths - {'ZesuSsz/Proofs/DecodeItem/Auto/Block800d698cShortString.v'}
        with self.assertRaisesRegex(ValueError, 'umbrella and both branches'):
            closure.native_rows(current)


def committed_arm(root):
    root.mkdir()
    source = root / 'Fixture.v'
    source.write_text('Lemma fixture : True.\nProof. exact I. Qed.\n')
    subprocess.run(['git', '-c', 'init.defaultBranch=main', 'init', '-q', str(root)], check=True)
    subprocess.run(['git', '-C', str(root), 'add', 'Fixture.v'], check=True)
    subprocess.run(['git', '-C', str(root), '-c', 'user.name=Fixture', '-c',
                    'user.email=fixture@example.invalid', '-c', 'commit.gpgsign=false',
                    'commit', '-qm', 'Fixture'], check=True)
    commit = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
    build = root / '_build/owned'
    private = build / 'default'
    private.mkdir(parents=True)
    (root / '_build/default').symlink_to(private)
    (private / 'Fixture.v').write_bytes(source.read_bytes())
    (private / 'Fixture.vo').write_bytes(b'Fixture object; not real proof evidence')
    recipe, findlib = build / 'coqc_recipe.json', build / 'coqc-ocamlpath.json'
    recipe.write_text(json.dumps(dict(command=['coqc', '-Q', '.', 'Fixture', 'Fixture.v'],
                                      working_dir=str(private))))
    findlib.write_text(json.dumps(dict(schema_version=1, workspace=str(root),
        private_build=str(build), OCAMLPATH=str(build / 'install/default/lib'))))
    return dict(workspace=str(root), commit=commit, build_dir=str(build),
                recipe=dict(path=str(recipe), sha256=closure.digest(recipe)),
                findlib=dict(path=str(findlib), sha256=closure.digest(findlib)))


class ArmTests(unittest.TestCase):
    def test_read_only_baseline_does_not_need_an_active_candidate_link(self):
        with tempfile.TemporaryDirectory() as directory:
            arm = committed_arm(Path(directory) / 'arm')
            (Path(arm['workspace']) / '_build/default').unlink()
            report, _ = closure.arm_binding(arm, require_active=False)
            self.assertEqual(report['commit'], arm['commit'])
            with self.assertRaisesRegex(ValueError, 'contained active build'):
                closure.arm_binding(arm)

    def test_arm_binds_commit_sources_objects_cwd_and_findlib(self):
        with tempfile.TemporaryDirectory() as directory:
            arm = committed_arm(Path(directory) / 'arm')
            report, commit = closure.arm_binding(arm)
            self.assertEqual(report['commit'], commit.sha)
            self.assertEqual(len(report['sources']), 1)
            self.assertEqual(len(report['objects']), 1)
            self.assertEqual(report['cwd'], str(Path(arm['build_dir']) / 'default'))
            self.assertTrue(report['OCAMLPATH'].startswith(arm['build_dir']))

    def test_changed_arm_and_missing_json_binding_refuse(self):
        with tempfile.TemporaryDirectory() as directory:
            arm = committed_arm(Path(directory) / 'arm')
            for key, value in [('commit', '0' * 40), ('recipe', dict(path=arm['recipe']['path'], sha256='0' * 64))]:
                with self.subTest(key=key), self.assertRaises(ValueError):
                    closure.arm_binding(dict(arm, **{key: value}))
            (Path(arm['workspace']) / 'Fixture.v').write_text('Changed source.\n')
            with self.assertRaisesRegex(ValueError, 'tracked changes'):
                closure.arm_binding(arm)

    def test_private_cwd_and_findlib_cannot_select_another_arm(self):
        with tempfile.TemporaryDirectory() as directory:
            arm = committed_arm(Path(directory) / 'arm')
            recipe = Path(arm['recipe']['path'])
            data = json.loads(recipe.read_text())
            data['working_dir'] = directory
            recipe.write_text(json.dumps(data))
            arm['recipe']['sha256'] = closure.digest(recipe)
            with self.assertRaisesRegex(ValueError, 'compiler cwd'):
                closure.arm_binding(arm)


class PublicMappingTests(unittest.TestCase):
    def test_missing_duplicate_unused_or_foreign_baseline_refuse(self):
        root = Path('/candidate')
        baseline = dict(workspace='/baseline', commit='1' * 40, build_dir='/baseline/_build/owned')
        expected = {(str(root / path), name): dict(baseline_workspace=baseline['workspace'],
                    baseline_commit=baseline['commit'], baseline_build_dir=baseline['build_dir'])
                    for name, path in closure.PUBLIC.items()}
        with patch.object(closure, 'prepare_protected_expectations', return_value=expected):
            self.assertEqual(closure.public_mapping(root, baseline, []), expected)
        for missing in list(expected):
            rows = dict(expected)
            del rows[missing]
            with self.subTest(missing=missing), patch.object(closure, 'prepare_protected_expectations', return_value=rows), \
                    self.assertRaisesRegex(ValueError, 'inventory differs'):
                closure.public_mapping(root, baseline, [])
        with patch.object(closure, 'prepare_protected_expectations', return_value=expected), \
                self.assertRaisesRegex(ValueError, 'different baseline'):
            closure.public_mapping(root, dict(baseline, commit='2' * 40), [])
        with self.assertRaisesRegex(ValueError, 'requires all protected'):
            closure.public_mapping(root, baseline, None)


class CoordinatorTests(unittest.TestCase):
    def report(self, root):
        source = str(root / 'Selected.v')
        baseline = dict(workspace=str(root / 'baseline'), build_dir=str(root / 'baseline/_build/owned'), objects=[])
        candidate = dict(workspace=str(root), build_dir=str(root / '_build/owned'), objects=[], OCAMLPATH='/owned/lib')
        return dict(success=False, proof_execution=False, candidate=candidate,
                    selected=[dict(source=source, required_statements=['native', 'public'])], rpc_timeout=18000,
                    baseline=baseline, physical_compiler=dict(path='/pinned/coqc', sha256='1' * 64))

    def test_prepare_only_opens_no_verifier(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.object(closure, 'prepare', return_value=self.report(root)), \
                    patch.object(closure, 'verify') as verify:
                report = asyncio.run(closure.run({}, root / 'result', prepare_only=True))
            verify.assert_not_called()
            self.assertFalse(report['proof_execution'])
            self.assertTrue((root / 'result/PREPARED.json').is_file())

    def test_exact_statement_coverage_is_required_and_failure_is_retained(self):
        for names in (['native'], ['native', 'public']):
            with self.subTest(names=names), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                async def verify(workspace, sources, pc, output, **kwargs):
                    output.mkdir()
                    (output / 'RESULT.json').write_text('{}\n')
                    return dict(success=True, checks=[dict(source=str(root / 'Selected.v'), statements=[
                        dict(name=name, verification=dict(success=True, assumptions=[], verification_method='module_m')) for name in names])])
                with patch.object(closure, 'prepare', return_value=self.report(root)), \
                        patch.object(closure, 'unchanged_preparation'), patch.object(closure, 'verify', side_effect=verify), \
                        patch.dict(closure.os.environ, {'OCAMLPATH': '/owned/lib'}):
                    if len(names) == 1:
                        with self.assertRaisesRegex(ValueError, 'no exact verification'):
                            asyncio.run(closure.run(dict(protected_expectations=[], mcp_launcher=None,
                                compiler_launcher=None), root / 'result'))
                        result = json.loads((root / 'result/RESULT.json').read_text())
                        self.assertFalse(result['success'])
                        self.assertIn('error', result)
                    else:
                        result = asyncio.run(closure.run(dict(protected_expectations=[], mcp_launcher=None,
                            compiler_launcher=None), root / 'result'))
                        self.assertTrue(result['success'])

    def test_input_schema_and_rpc_timeout_refuse_before_transport(self):
        with self.assertRaisesRegex(ValueError, 'incomplete or unsupported'):
            closure.prepare({})
        mapping = dict(schema_version=1, function='decodeItem', baseline={}, candidate={},
                       protected_expectations=[], freshness=None, mcp_launcher=None,
                       compiler_launcher=None, rpc_timeout=0, physical_compiler=None,
                       physical_admission=None, baseline_verification=None)
        with self.assertRaisesRegex(ValueError, 'RPC timeout'):
            closure.prepare(mapping)

    def test_shared_defs_extra_statement_cannot_hide_behind_valid_required_checks(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            async def verify(workspace, sources, pc, output, **kwargs):
                output.mkdir()
                (output / 'RESULT.json').write_text('{}\n')
                return dict(success=True, checks=[dict(source=str(root / 'Selected.v'), statements=[
                    dict(name=name, verification=dict(success=True, assumptions=[], verification_method=method))
                    for name, method in [('native', 'module_m'), ('public', 'module_m'), ('helper', 'shared_defs')]])])
            with patch.object(closure, 'prepare', return_value=self.report(root)), \
                    patch.object(closure, 'unchanged_preparation'), patch.object(closure, 'verify', side_effect=verify), \
                    patch.dict(closure.os.environ, {'OCAMLPATH': '/owned/lib'}), \
                    self.assertRaisesRegex(ValueError, 'returned statement lacks exact module_m'):
                asyncio.run(closure.run(dict(protected_expectations=[], mcp_launcher=None,
                    compiler_launcher=None), root / 'result'))
            report = json.loads((root / 'result/RESULT.json').read_text())
            self.assertFalse(report['success'])

    def test_missing_baseline_verification_refuses(self):
        with self.assertRaisesRegex(ValueError, 'JSON binding needs'):
            closure.baseline_verification(None, {}, {}, {})


if __name__ == '__main__':
    unittest.main()
