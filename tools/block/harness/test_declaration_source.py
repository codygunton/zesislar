"""Keep tactic owners separate from executed native proof commands."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from declaration_parallel_plan import attach, validate
from declaration_source import contains_native_proof
from entry_chain import binding, save
from memory_policy import workload_for_job


HERE = Path(__file__).resolve().parent
FIXTURES = HERE / 'test-fixtures/declaration-source'
OWNERS = {
    'ZesuSsz.Automation.Finish': ('Finish.v',
        '63d5fe374012248cb22595923add0d55b3bc20053f72519a7915fc95b4258644'),
    'ZesuSsz.Automation.Legacy.Finish': ('LegacyFinish.v',
        '17a8c4fc5025470807f75671c9543f1ae5c3410cf8dd41747dee9dd0b1e27d85'),
}
GIB = 1024 ** 3


class DeclarationSourceTests(unittest.TestCase):
    def test_exact_finish_sources_are_tactic_declarations(self):
        for module, (filename, expected) in OWNERS.items():
            with self.subTest(module=module):
                raw = (FIXTURES / filename).read_bytes()
                self.assertEqual(hashlib.sha256(raw).hexdigest(), expected)
                self.assertIn('Ltac zesu_block :=', raw.decode())
                self.assertFalse(contains_native_proof(raw.decode()))

    def test_comments_and_strings_do_not_invoke_search(self):
        source = ('(* zesu_block. (* nested zesu_block *) *)\n'
                  'Definition message := "zesu_block and ""quoted"" text".\n')
        self.assertFalse(contains_native_proof(source))

    def test_ltac1_entry_definitions_and_ordinary_definitions_pass(self):
        for source in [
                'Ltac zesu_block := idtac.',
                'Local Ltac zesu_block := idtac.',
                'Global Ltac zesu_block ::= idtac.',
                '#[local] Ltac zesu_block := idtac.',
                'Ltac wrapper := idtac.',
                'Ltac2 @ external ordinary : unit -> unit := "plugin" "entry".']:
            with self.subTest(source=source):
                self.assertFalse(contains_native_proof(source))

    def test_native_aliases_refuse_before_any_alias_execution(self):
        for source in [
                'Ltac hidden := zesu_block. Goal True. hidden. Qed.',
                'Local Ltac hidden := Owner.zesu_block.',
                'Ltac hidden := zesu_block. Ltac other := hidden. Goal True. other. Qed.']:
            with self.subTest(source=source):
                self.assertTrue(contains_native_proof(source))

    def test_ltac2_native_initializers_and_bodies_refuse_conservatively(self):
        for source in ['Ltac2 x := zesu_block ().',
                       'Ltac2 x : unit := zesu_block ().',
                       'Ltac2 x := let y := zesu_block () in y.',
                       'Ltac2 wrapper () := zesu_block ().',
                       'Ltac2 x := fun () => zesu_block ().',
                       'Ltac2 @ external zesu_block : unit -> unit := "plugin" "entry".']:
            with self.subTest(source=source):
                self.assertTrue(contains_native_proof(source))

    def test_actual_native_calls_refuse(self):
        for source in [
                'Lemma native : True. Proof. zesu_block. Qed.',
                'Goal True. Proof. all: first [progress zesu_block | idtac]. Qed.',
                'Goal True. Proof. Owner.zesu_block. Qed.',
                'Goal True. Proof. Time zesu_block. Qed.',
                'Definition native : True := ltac:(zesu_block).',
                'Ltac wrapper := idtac. Goal True. Proof. zesu_block. Qed.',
                'Ltac2 Eval zesu_block ().']:
            with self.subTest(source=source):
                self.assertTrue(contains_native_proof(source))

    def test_malformed_sources_refuse(self):
        for source in ['(* unfinished', 'Definition message := "unfinished.',
                       'Ltac wrapper := (idtac].', 'Ltac wrapper := idtac',
                       'Ltac wrapper := .', 'Ltac wrapper.', '#[local].', '.']:
            with self.subTest(source=source), self.assertRaises(ValueError):
                contains_native_proof(source)

    def test_the_staged_parser_and_classifier_import_without_the_harness(self):
        layout = json.loads((HERE / 'TOOL-LAYOUT.json').read_text())
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for relative in ['block/declaration_source.py', 'block/check_data_only_lemmas.py']:
                target = root / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((HERE / layout[relative]).read_bytes())
            code = ('import sys; sys.path.insert(0,sys.argv[1]); '
                    'from declaration_source import contains_native_proof; '
                    'assert not contains_native_proof("Ltac zesu_block := idtac."); '
                    'assert contains_native_proof("Proof. zesu_block. Qed.")')
            result = subprocess.run([sys.executable, '-I', '-B', '-c', code,
                                     str(root / 'block')], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)


class PublicDeclarationClassifierTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.dune = self.root / 'dune'
        self.dune.write_text('Nonexecutable compiler and Dune fixture.\n')
        self.graph = self.root / 'GRAPH.json'
        save(self.graph, {'import_edges': []})

    def configuration(self, sources):
        rows, modules = [], {}
        for index, (module, text) in enumerate(sources.items()):
            path = self.root / ('Source' + str(index) + '.v')
            path.write_text(text)
            modules[module] = path.name
            rows.append(dict(binding(path), module=module, role='consumer_check'))
        profile = self.root / 'PROFILE.json'
        save(profile, {'schema': 'scratch.admission-profile.v1', 'kind': 'focused_check',
                       'memory_booking': 'full_physical_fence', 'sources': rows})
        config = {'declarations_only': True, 'prepared_workspace': str(self.root),
                  'effective_compiler_version': {'compiler': binding(self.dune)},
                  'physical_flags': [], 'cache_import_graph': binding(self.graph),
                  'proof_runtime': {'module_files': modules},
                  'jobs': [{'phase': 'prerequisites', 'claim_bytes': 64 * GIB,
                            'physical_fence_bytes': 64 * GIB,
                            'ordered_modules': list(sources)}]}
        return config, binding(profile)

    def attach(self, config):
        with patch('declaration_parallel_plan.shutil.which', return_value=str(self.dune)):
            return attach(config)

    def test_exact_owners_pass_both_public_classifiers_and_staged_validation(self):
        sources = {module: (FIXTURES / row[0]).read_text() for module, row in OWNERS.items()}
        config, profile = self.configuration(sources)
        job = config['jobs'][0]
        self.assertEqual(workload_for_job(profile, job, config)['kind'], 'focused_check')
        spec = self.attach(config)
        self.assertIn('ZesuSsz.Automation.Finish', spec['protected_modules'])
        runtime = dict(config['proof_runtime'], phase='prerequisites', declaration_dag=spec,
                       ordered_modules=job['ordered_modules'], physical_flags=[],
                       physical_compiler=config['effective_compiler_version']['compiler'],
                       canonical_admission={'minimum_claim_bytes': spec['claim_bytes'],
                                            'physical_fence_bytes': 64 * GIB})
        self.assertEqual(validate(runtime, self.root), spec)

    def test_calls_aliases_and_initializers_refuse_both_public_classifiers(self):
        for source in ['Lemma native : True. Proof. zesu_block. Qed.',
                       'Ltac hidden := zesu_block. Goal True. hidden. Qed.',
                       'Ltac2 x := zesu_block ().']:
            with self.subTest(source=source):
                config, profile = self.configuration({'Example.Owner': source})
                with self.assertRaisesRegex(ValueError, 'native proof'):
                    workload_for_job(profile, config['jobs'][0], config)
                with self.assertRaisesRegex(ValueError, 'native proof'):
                    self.attach(config)

    def test_malformed_source_refuses_both_public_classifiers(self):
        config, profile = self.configuration({'Example.Owner': '(* unfinished'})
        with self.assertRaises(ValueError):
            workload_for_job(profile, config['jobs'][0], config)
        with self.assertRaises(ValueError):
            self.attach(config)

    def test_proof_module_still_refuses_with_a_declaration_only_body(self):
        config, _ = self.configuration({'Example.Proofs.Native': 'Ltac zesu_block := idtac.'})
        with self.assertRaisesRegex(ValueError, 'native proof'):
            self.attach(config)

    def test_source_binding_and_native_phase_checks_remain(self):
        config, profile = self.configuration({'Example.Owner': 'Ltac zesu_block := idtac.'})
        (self.root / 'Source0.v').write_text('Ltac zesu_block := fail.')
        with self.assertRaisesRegex(ValueError, 'binding changed'):
            workload_for_job(profile, config['jobs'][0], config)
        changed = deepcopy(config)
        changed['declarations_only'] = False
        with self.assertRaisesRegex(ValueError, 'declaration-only'):
            self.attach(changed)


if __name__ == '__main__':
    unittest.main()
