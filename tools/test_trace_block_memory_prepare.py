"""Test the exact historical MemoryAccess observation boundary."""
import hashlib
import json
from pathlib import Path
import sys
import unittest

TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS / 'block'))
import trace_block_prepare as prepare
import trace_block_mcp as backend

FIXTURES = TOOLS / 'fixtures/trace_block/memory_access'
CALL = 'zesu_memory_access_if_enabled zesu_integer_array_facts'


class MemoryPreparationTests(unittest.TestCase):
    def setUp(self):
        self.hooks = (FIXTURES / 'Hooks.v.txt').read_text()
        self.module = (FIXTURES / 'MemoryAccess.v.txt').read_text()

    def test_fixture_commands_match_historical_bindings(self):
        for name, row in json.loads((FIXTURES / 'SOURCE.json').read_text()).items():
            self.assertEqual(hashlib.sha256((FIXTURES / (name + '.txt')).read_bytes()).hexdigest(),
                             row['command_sha256'])

    def test_both_callbacks_recover_exact_original_sources(self):
        hooks, module, descriptors = prepare.instrument_memory_access(self.hooks, self.module)
        self.assertEqual(set(descriptors), {'MemoryAccess.Hooks', 'MemoryAccess.FindInContext'})
        line = next(line for line in hooks.splitlines() if 'trace_block_filtered "MemoryAccess.Hooks"' in line)
        self.assertEqual(hooks.replace(line, '  | ' + CALL), self.hooks)
        prefix = ' let original := ltac:(fun unused => '
        body, wrapper = module.split(prefix, 1)
        original, _ = wrapper.split(') in let observe := ltac2:', 1)
        self.assertEqual(module[:module.index(prefix)].removeprefix(prepare.package.BRIDGE_IMPORT + '\n')
                         + original + ' : typeclass_instances.', self.module)
        self.assertIn('Ltac1.apply original [Ltac1.of_constr constr:(tt)]', module)
        self.assertEqual(descriptors['MemoryAccess.Hooks']['commands']['whole-rule'], CALL)
        self.assertIn(original, descriptors['MemoryAccess.FindInContext']['commands']['whole-rule'])
        for descriptor in descriptors.values():
            self.assertEqual(descriptor['rule'], 'MemoryAccess')
            self.assertEqual(descriptor['typed_guard']['sha256'], hashlib.sha256(descriptor['typed_guard']['command'].encode()).hexdigest())

    def test_missing_repeated_and_changed_hook_refuse(self):
        for hooks in (self.hooks.replace(CALL, 'idtac'), self.hooks.replace('| ' + CALL, '| ' + CALL + '\n  | ' + CALL),
                      self.hooks.replace(CALL, CALL + ' extra')):
            with self.subTest(hooks=hooks[-80:]):
                with self.assertRaises(ValueError): prepare.instrument_memory_access(hooks, self.module)

    def test_missing_repeated_changed_and_observed_hint_refuse(self):
        observed = prepare.instrument_memory_access(self.hooks, self.module)[1]
        for module in ('', self.module + '\n' + self.module,
                       self.module.replace('unify key FICSyntactic', 'unify key FIAll'), observed):
            with self.subTest(module=module[-80:]):
                with self.assertRaises(ValueError): prepare.instrument_memory_access(self.hooks, module)

    def test_instruction_and_memory_wrappers_retain_both_clients(self):
        hooks, _, original = prepare.instrument_hooks(self.hooks, {'kind':'instruction','value':'FindMemMapsTo'}, False)
        updated, module, descriptors = prepare.instrument_memory_access(hooks, self.module)
        self.assertEqual(set(descriptors), {'MemoryAccess.Hooks', 'MemoryAccess.FindInContext'})
        self.assertIn('trace_block_checkpoint "instruction-lookup"', updated)
        self.assertIn('trace_block_checkpoint "requested-trigger"', updated)
        self.assertIn(CALL, original)
        self.assertIn('trace_block_filtered "MemoryAccess.FindInContext"', module)

    def test_default_preparation_builds_both_supported_clients(self):
        import tempfile
        import shutil
        from types import SimpleNamespace
        from unittest.mock import patch
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original = root / 'original'
            original.mkdir()
            source = original / 'Block.v'
            prefix = 'Require Import ZesuSsz.Automation.All.\nLemma fixture : True.\nProof.\n'
            source.write_text(prefix + 'Abort.\n')
            (original / 'generated/isla-traces').mkdir(parents=True)
            (original / 'generated/isla-traces/index.v').write_text('exact native input')
            automation = original / 'ZesuSsz/Automation'
            automation.mkdir(parents=True)
            (automation / 'Hooks.v').write_text(self.hooks)
            (automation / 'MemoryAccess.v').write_text(self.module)
            owner = root / 'owner'
            for name in (*prepare.RUNTIME_FILES, *prepare.package.overlay_files(prepare.OWNER)):
                target = owner / name
                target.parent.mkdir(parents=True, exist_ok=True)
                if (prepare.OWNER / name).is_file():
                    shutil.copy2(prepare.OWNER / name, target)
                else:
                    target.write_bytes(b"mock operational input")
            targets = []
            def git(workspace, *args):
                return (str(root / '.git') if '--git-common-dir' in args else 'a' * 40).encode()
            def command(args, **kwargs):
                if 'worktree' in args:
                    shutil.copytree(original, Path(args[-2]))
                else:
                    build = Path(args[args.index('--build-dir') + 1])
                    names = args[args.index('-j32') + 1:]
                    targets.extend(names)
                    for name in names:
                        if name.endswith('.vo'):
                            artifact = build / 'default' / name
                            artifact.parent.mkdir(parents=True, exist_ok=True)
                            artifact.write_bytes(b'mock object')
                    (build / 'coqc-ocamlpath.json').write_text(json.dumps({
                        'workspace': str(kwargs['cwd']), 'private_build': str(build)}))
                return SimpleNamespace(returncode=0)
            request = {'workspace':str(original), 'source':str(source), 'writer_id':'fixture-owner',
                'block_pc':'0x800d6b08', 'rule_set':[{'name':'MemoryAccess','enabled':True}],
                'stop':{'kind':'instruction','value':'FindMemMapsTo'},
                'scope':{'root':'a'*40, 'source_sha256':prepare.digest(source)},
                'prefix_text':prefix, 'source_prefix':prefix}
            with patch.object(prepare,'OWNER',owner), patch.object(prepare,'corrected_prepared',return_value=None), \
                 patch.object(prepare,'_git',side_effect=git), patch.object(prepare,'source_inventory',return_value={}), \
                 patch.object(prepare.package,'configure',return_value=[]), \
                 patch.object(prepare.package,'runtime_inputs',return_value={}), \
                 patch.object(prepare,'switch_adjusted_prefix',return_value=(prefix,[])), \
                 patch.object(prepare.shutil,'which',return_value='/pinned/opam'), \
                 patch.object(prepare.subprocess,'run',side_effect=command):
                result = prepare.prepare_request(request,root/'output')
            self.assertEqual(set(result['entry_descriptors']), {'MemoryAccess.Hooks','MemoryAccess.FindInContext'})
            self.assertIn('ZesuSsz/Automation/MemoryAccess.vo',targets)
            self.assertLess(targets.index('p0-filtered-trace.install'), targets.index('ZesuSsz/Automation/MemoryAccess.vo'))
            workspace = Path(result['workspace'])
            self.assertIn('trace_block_filtered "MemoryAccess.Hooks"', (workspace/'ZesuSsz/Automation/Hooks.v').read_text())
            self.assertIn('trace_block_filtered "MemoryAccess.FindInContext"', (workspace/'ZesuSsz/Automation/MemoryAccess.v').read_text())
            self.assertEqual((automation/'Hooks.v').read_text(), self.hooks)
            self.assertEqual((automation/'MemoryAccess.v').read_text(), self.module)

    def test_qualified_switch_names_match_existing_modules(self):
        for name in ('ReturnRoute', 'ConjunctMatch', 'MemoryAccess', 'FinishFacts'):
            self.assertEqual(backend.rule_declaration(name), 'ZesuSsz.Automation.' + name + '.ZesuStep' + name)
        self.assertEqual(backend.rule_name_for_switch('ZesuStepMemoryAccess'), 'MemoryAccess')
        with self.assertRaises(ValueError): backend.rule_declaration('Unknown')


if __name__ == '__main__': unittest.main()
