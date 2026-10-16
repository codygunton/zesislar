"""Check the bounded preparation flow without compiler or proof execution."""
import hashlib
import json
from pathlib import Path
import sys
import unittest

TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS / 'block'))
import trace_block_prepare as prepare
import trace_block_bounded_package as package

class BoundedFlowTests(unittest.TestCase):
    def setUp(self):
        fixtures = TOOLS / 'fixtures/trace_block/memory_access'
        self.hooks = (fixtures / 'Hooks.v.txt').read_text()
        self.module = (fixtures / 'MemoryAccess.v.txt').read_text()

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
            for name in (*prepare.RUNTIME_FILES, *package.overlay_files(prepare.OWNER)):
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
                'capture_surface_policy':'bounded-kernel-v1', 'block_pc':'0x800d6b08', 'rule_set':[{'name':'MemoryAccess','enabled':True}],
                'stop':{'kind':'instruction','value':'FindMemMapsTo'},
                'scope':{'root':'a'*40, 'source_sha256':prepare.digest(source)},
                'prefix_text':prefix, 'source_prefix':prefix}
            with patch.object(prepare,'OWNER',owner), patch.object(prepare,'corrected_prepared',return_value=None), \
                 patch.object(prepare,'_git',side_effect=git), patch.object(prepare,'source_inventory',return_value={}), \
                 patch.object(package,'configure',return_value=[]), \
                 patch.object(package,'runtime_inputs',return_value={}), \
                 patch.object(prepare,'switch_adjusted_prefix',return_value=(prefix,[])), \
                 patch.object(prepare.shutil,'which',return_value='/pinned/opam'), \
                 patch.object(prepare.subprocess,'run',side_effect=command):
                result = prepare.prepare_request(request,root/'output')
            self.assertEqual(set(result['entry_descriptors']), {'MemoryAccess.Hooks','MemoryAccess.FindInContext'})
            self.assertIn('ZesuSsz/Automation/MemoryAccess.vo',targets)
            self.assertLess(targets.index('p0-bounded-trace.install'), targets.index('ZesuSsz/Automation/MemoryAccess.vo'))
            workspace = Path(result['workspace'])
            self.assertIn('trace_bounded_filtered "MemoryAccess.Hooks"', (workspace/'ZesuSsz/Automation/Hooks.v').read_text())
            self.assertIn('trace_bounded_filtered "MemoryAccess.FindInContext"', (workspace/'ZesuSsz/Automation/MemoryAccess.v').read_text())
            self.assertEqual((automation/'Hooks.v').read_text(), self.hooks)
            self.assertEqual((automation/'MemoryAccess.v').read_text(), self.module)

            self.assertEqual(result['instrumentation']['protocol'], 'bounded-kernel-v1')
            self.assertIn(package.BRIDGE.replace('.v', '.vo'), targets)
            self.assertIn(package.READER_TARGET, targets)
            self.assertIn(package.WRITER_TARGET, targets)
            self.assertIn(package.BRIDGE_IMPORT, Path(result['source']).read_text())
            for descriptor in result['entry_descriptors'].values():
                self.assertIn('trace_bounded_ltac1_guard', descriptor['typed_guard']['command'])
                self.assertEqual(descriptor['trials'][-1]['clause'], 'whole-rule')
                self.assertEqual(sum(row['clause'] == 'whole-rule' for row in descriptor['trials']), 1)


if __name__ == "__main__": unittest.main()
