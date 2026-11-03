"""Exercise measured DAG weights through the physical-scope selection."""
import unittest
from unittest.mock import patch

from entry_chain import binding
from declaration_parallel_plan import attach
from scope_bookings import compiler_environment, compiler_resources, GIB
import test_declaration_parallel as Parallel
import test_declaration_resources as Resources


class DagScopeClaims(unittest.TestCase):
    def boundary(self, peak=None):
        measured = Resources.DeclarationResourceTests()
        measured.setUp()
        self.addCleanup(measured.doCleanups)
        profile = measured.profile(peak=peak) if peak is not None else None
        case = Parallel.GuardedAdapterTests()
        original = case.configure

        def configure(f):
            # Both banks select the same pinned, nonexecutable compiler fixture.
            old = binding(f.compiler)
            f.compiler = measured.f.compiler
            f.runtime['physical_compiler'] = binding(f.compiler)
            f.runtime['bindings'] = [binding(f.compiler) if row == old else row
                                     for row in f.runtime['bindings']]
            original(f)
            config = {'declarations_only': True, 'prepared_workspace': str(f.root),
                      'jobs': [{'phase': 'prerequisites', 'claim_bytes': 64 * GIB,
                                'physical_fence_bytes': 64 * GIB,
                                'ordered_modules': ['Example.Control']}],
                      'proof_runtime': {'module_files': f.runtime['module_files']},
                      'cache_import_graph': f.runtime['cache_import_graph'],
                      'physical_compiler': binding(f.compiler),
                      'effective_compiler_version': {'compiler': binding(f.compiler)},
                      'physical_flags': f.runtime['physical_flags']}
            dune = f.compiler.with_name('dune')
            with patch('declaration_parallel_plan.shutil.which', return_value=str(dune)):
                f.runtime['declaration_dag'] = attach(config, measurements=profile)
            f.runtime['canonical_admission']['minimum_claim_bytes'] = config['jobs'][0]['claim_bytes']
            f.runtime['compiler_scope_bookings'] = compiler_resources(f.runtime, {}, f.root, f.root)

        case.configure = configure
        case.setUp()
        self.addCleanup(case.doCleanups)
        expected = max(GIB, (peak * 1024 * 3 + 1) // 2) if peak is not None else 16 * GIB
        captured = []

        def runner(command, **options):
            launch = options['env']
            self.assertEqual(launch['ZESU_MODULE_CLAIM_BYTES'], str(expected))
            self.assertEqual(launch['ZESU_MODULE_LIMIT_GIB'], '64')
            # This is the public compiler's real final environment selector.
            inherited = dict(launch, ZESU_CONTROLLER_ROLE='entry-pilot-mcp',
                             ZESU_CONTROLLER_AUTHORITY_SHA256='old-controller',
                             ZESU_MODULE_MEMORY_PROFILE='unbound-root-profile')
            selected = compiler_environment(case.f.runtime, binding(case.f.source), inherited)
            self.assertEqual(selected['ZESU_MODULE_CLAIM_BYTES'], str(expected))
            self.assertEqual(selected['ZESU_MODULE_LIMIT_GIB'], '64')
            for key in ('ZESU_CONTROLLER_ROLE', 'ZESU_CONTROLLER_AUTHORITY_SHA256',
                        'ZESU_MODULE_MEMORY_PROFILE'):
                self.assertNotIn(key, selected)
            captured.append(selected)
            return case.physical_runner(command, **options)

        adapter = case.adapter(runner=runner)
        result = adapter.execute(lambda: 256 * GIB)
        self.assertEqual(list(result['receipts']), ['Example.Control'])
        self.assertEqual(len(captured), 1)
        self.assertEqual(len(case.case.manager.rows), 1)
        self.assertEqual(case.f.runtime['canonical_admission']['physical_fence_bytes'], 64 * GIB)

    def test_completed_measurement_reaches_the_physical_scope(self):
        self.boundary(900000)

    def test_tiny_completed_measurement_keeps_one_gib(self):
        self.boundary(1)

    def test_unmeasured_module_keeps_sixteen_gib(self):
        self.boundary()


if __name__ == '__main__': unittest.main()
