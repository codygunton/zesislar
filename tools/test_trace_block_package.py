"""Test independent package preparation without a build or native proof."""
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).parent/'block'))
import trace_block_package as package


class PackageTests(unittest.TestCase):
    def setUp(self):
        self.directory=tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root=Path(self.directory.name)

    def source_tree(self):
        for name in package.FILES:
            path=self.root/package.FILTERED/name
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text('exact source '+name)
        (self.root/'META.p0-filtered-trace.template').write_text('directory="."\n# DUNE_GEN\n')

    def artifacts(self):
        build=self.root/'_build/agents/test'
        for name in ('install/default/lib/p0-filtered-trace/trace-observer/filtered_trace_plugin.cmxs',
                     'default/'+package.BRIDGE.replace('.v','.vo'),'default/'+package.WRITER_TARGET):
            path=build/name
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes(('compiled '+name).encode())
        return build

    def test_overlay_lists_every_filtered_file_and_preserves_legacy(self):
        self.source_tree()
        legacy=self.root/'tools/block/TracePlugin/trace_block_plugin.ml'
        legacy.write_bytes(b'legacy bytes')
        names=package.overlay_files(self.root)
        self.assertEqual(len(names),7)
        self.assertNotIn(str(legacy.relative_to(self.root)),names)
        self.assertEqual(legacy.read_bytes(),b'legacy bytes')

    def test_missing_or_linked_package_source_rejects(self):
        self.source_tree()
        path=self.root/package.BRIDGE
        path.unlink()
        with self.assertRaisesRegex(ValueError,'absent or linked'):
            package.overlay_files(self.root)
        path.symlink_to(self.root/'META.p0-filtered-trace.template')
        with self.assertRaisesRegex(ValueError,'absent or linked'):
            package.overlay_files(self.root)

    def test_configuration_is_idempotent_and_keeps_existing_package(self):
        project=self.root/'dune-project';project.write_text('(lang dune 3.8)\n(package (name legacy))\n')
        theory=self.root/'ZesuSsz/dune';theory.parent.mkdir();theory.write_text('(coq.theory (name ZesuSsz) (theories iris stdpp RecordUpdate Ltac2))\n')
        package.configure(self.root)
        once=(project.read_bytes(),theory.read_bytes())
        package.configure(self.root)
        self.assertEqual(once,(project.read_bytes(),theory.read_bytes()))
        self.assertIn('(package (name legacy))',project.read_text())
        self.assertEqual(project.read_text().count('(name p0-filtered-trace)'),1)
        self.assertIn('Ltac2 P0Filtered))',theory.read_text())

    def test_unknown_theory_boundary_rejects(self):
        (self.root/'dune-project').write_text('(lang dune 3.8)\n')
        theory=self.root/'ZesuSsz/dune';theory.parent.mkdir();theory.write_text('(coq.theory (name Other))\n')
        with self.assertRaisesRegex(ValueError,'unsupported boundary'):
            package.configure(self.root)

    def test_runtime_copies_exact_bridge_and_binds_compiled_inputs(self):
        build=self.artifacts()
        result=package.runtime_inputs(self.root,build)
        package.validate_runtime(dict(result,workspace=str(self.root)))
        self.assertEqual(Path(result['observer_runtime']['bridge']['path']).read_bytes(),
                         (build/'default'/package.BRIDGE.replace('.v','.vo')).read_bytes())
        self.assertEqual(set(result),{'observer_runtime','chunk_writer'})
        self.assertEqual(result,package.runtime_inputs(self.root,build))

    def test_missing_runtime_and_changed_bridge_reject(self):
        build=self.artifacts();result=package.runtime_inputs(self.root,build)
        Path(result['observer_runtime']['bridge']['path']).write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError,'differs from the compiled'):
            package.runtime_inputs(self.root,build)
        with self.assertRaisesRegex(ValueError,'changed'):
            package.validate_runtime(dict(result,workspace=str(self.root)))
        with self.assertRaisesRegex(ValueError,'complete filtered runtime'):
            package.validate_runtime({'workspace':str(self.root)})

    def test_external_build_or_runtime_artifact_rejects(self):
        self.artifacts()
        with self.assertRaisesRegex(ValueError,'leaves its workspace'):
            package.runtime_inputs(self.root/'_build',self.root)
        build=self.artifacts();result=package.runtime_inputs(self.root,build)
        result['observer_runtime']['bridge']['path']=str(self.root/'missing')
        with self.assertRaises((ValueError,OSError)):
            package.validate_runtime(dict(result,workspace=str(self.root)))

    def test_no_old_bridge_or_package_is_selected(self):
        self.assertEqual(package.BRIDGE_IMPORT,'From P0Filtered Require Import TraceObserver.')
        self.assertNotIn('zesu-signature-gates',package.FILTERED)
        self.assertTrue(package.BRIDGE.startswith('tools/block/TracePlugin/Filtered/'))


if __name__=='__main__':unittest.main()
