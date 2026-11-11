"""Exercise the ELF regeneration tools on synthetic inputs."""
import gzip
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE / 'platform')]
import check_test_traces  # noqa: E402
import layout  # noqa: E402
import recipe  # noqa: E402
import region_windows  # noqa: E402
from test_manifest import small_elf  # noqa: E402

GIB = 1024 ** 3
ROM = (0x80000000, 0x88000000)
ADAPTER = """ Execute() => if zisk_contains(a, w, 2147483648, 2148597112)
   if zisk_contains(a, w, 2684354560, 3221225472)
           zisk_contains(a, w, 2148597120, 2148632184)
 zisk_contains(a, w, 1073741824, 2147483648) |
 zisk_contains(a, w, 2147483648, 2148597112) |
 zisk_contains(a, w, 2148597120, 2148632184) |
"""
SMOKE = """CASES = [
 ("executable_text", "fetch", 0x80000000, "fetch", 16),
 ("read_only_data", "ld", 0x8010fd80, "read", 16),
 ("heap", "ld", 0xa0d34520, "read", 16),
 ("text_data_read", "ld", 0x80000000, "load_fault", 16),
 ("oversized_input_end", "ld", 0x80000000, "load_fault", 0x50000000),
 ("rodata_write", "sd", 0x8010fd80, "store_fault", 16),
 ("ram_end_crossing", "ld", 0xbffffffc, "load_fault", 16),
 ("text_end_crossing", "fetch", 0x8010fd76, "fetch_fault", 16),
 ("rodata_end_crossing", "ld", 0x80118674, "load_fault", 16),
]
"""
NEW_TEXT, NEW_RODATA = (0x80000000, 0x8010f5e4), (0x8010f5f0, 0x80117ef0)


class LayoutTests(unittest.TestCase):
    def test_adapter_ranges_follow_the_elf_and_keep_ram_and_input(self):
        result = layout.render_adapter(ADAPTER, NEW_TEXT, NEW_RODATA, ROM)
        self.assertEqual(result.count('2147483648, 2148595172'), 2)
        self.assertEqual(result.count('2148595184, 2148630256'), 2)
        self.assertIn('2684354560, 3221225472', result)
        self.assertIn('1073741824, 2147483648', result)
        self.assertEqual(layout.render_adapter(ADAPTER, (0x80000000, 0x8010fd78), (0x8010fd80, 0x80118678), ROM),
                         ADAPTER)

    def test_adapter_with_a_third_rom_range_refuses(self):
        with self.assertRaises(ValueError):
            layout.render_adapter(ADAPTER + 'zisk_contains(a, w, 2147483660, 2147483670)\n',
                                  NEW_TEXT, NEW_RODATA, ROM)

    def test_smoke_addresses_follow_the_elf(self):
        addresses = layout.smoke_addresses(NEW_TEXT, NEW_RODATA, {'ZKVM_HEAP_POS': 0xa0d34520})
        result = layout.render_smoke(SMOKE, addresses)
        for line in ('("read_only_data", "ld", 0x8010f5f0,', '("rodata_write", "sd", 0x8010f5f0,',
                     '("text_end_crossing", "fetch", 0x8010f5e2,', '("rodata_end_crossing", "ld", 0x80117eec,',
                     '("ram_end_crossing", "ld", 0xbffffffc,'):
            self.assertIn(line, result)
        with self.assertRaisesRegex(ValueError, 'lacks cases'):
            layout.render_smoke(SMOKE.replace('heap', 'stack'), addresses)

    def test_extents_require_one_text_and_one_rodata_segment(self):
        segments = [{'start': 1, 'end': 2, 'flags': 1, 'file_bytes': 1}, {'start': 3, 'end': 4, 'flags': 4, 'file_bytes': 1}]
        self.assertEqual(layout.extents(segments), ((1, 2), (3, 4)))
        with self.assertRaises(ValueError):
            layout.extents(segments[:1])


class RegionWindowTests(unittest.TestCase):
    MACHINE = {'mapRamBase': 0xa0000000, 'mapRamSize': 0x20000000, 'mapInputBufferAddress': 0x40000000,
               'mapInputCapacity': 0x40000000, 'mapRodataBase': 0x8010f5f0, 'mapRodataEnd': 0x80117ef0}

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.policy = self.root / 'eql-policy'
        (self.policy / 'sources').mkdir(parents=True)
        packet = {'source_declarations': [{'file': {'path': 'old/Machine.v', 'sha256': 'old'},
            'closed_region_values': {'RODATA': {'lower': 'mapRodataBase defaultMap', 'upper': 'mapRodataEnd defaultMap',
                                                'lo': 0x8010fd80, 'hi': 0x80118678},
                                     'RAM': {'lower': 'mapRamBase defaultMap', 'upper': 'machineRamEnd defaultMap',
                                             'lo': 0xa0000000, 'hi': 0xc0000000}}}]}
        payload = (json.dumps(packet, indent=2) + '\n').encode()
        archive = gzip.compress(payload, compresslevel=9, mtime=0)
        (self.policy / 'regions.json.gz').write_bytes(archive)
        source_map = {'schema': 'source.region-path-map.v1', 'paths': {},
                      'archives': {'regions.json.gz': {'sha256': hashlib.sha256(archive).hexdigest(),
                                                       'payload_sha256': hashlib.sha256(payload).hexdigest()}},
                      'input_files': {'elf': {'path': 'zesu-zisk.elf', 'sha256': 'new-elf'}}}
        (self.policy / 'PATH-MAP.json').write_text(json.dumps(source_map, indent=2) + '\n')
        self.pins = self.root / 'pins.mk'
        map_sha = hashlib.sha256((self.policy / 'PATH-MAP.json').read_bytes()).hexdigest()
        self.pins.write_text(f'--per-load-regions {self.policy.name}/regions.json.gz \\\n'
                             f'  --per-load-regions-sha256 {hashlib.sha256(payload).hexdigest()} \\\n'
                             f'  --region-source-map {self.policy.name}/PATH-MAP.json \\\n'
                             f'  --region-source-map-sha256 {map_sha}\n')
        self.machine = self.root / 'Machine.v'
        self.machine.write_text('(* map *)\n')
        root, region_windows.ROOT = region_windows.ROOT, self.root
        self.addCleanup(setattr, region_windows, 'ROOT', root)

    def test_expressions_use_the_selected_map(self):
        self.assertEqual(region_windows.evaluate('machineRamEnd defaultMap', self.MACHINE), 0xc0000000)
        self.assertEqual(region_windows.evaluate('mapInputBufferAddress defaultMap + mapInputCapacity defaultMap',
                                                 self.MACHINE), 0x80000000)
        with self.assertRaises(ValueError):
            region_windows.evaluate('mapRamBase forkMap', self.MACHINE)

    def test_a_stale_window_fails_and_rewrite_reextracts_it(self):
        found = region_windows.problems(self.policy, self.MACHINE, 'new-elf', [self.pins])
        self.assertEqual(len(found), 1)
        self.assertIn('RODATA window 0x8010fd80..0x80118678', found[0])
        self.assertTrue(region_windows.rewrite(self.policy, self.MACHINE, self.machine, [self.pins]))
        self.assertEqual(region_windows.problems(self.policy, self.MACHINE, 'new-elf', [self.pins]), [])
        _, packet, source_map = region_windows.load(self.policy)
        declaration = packet['source_declarations'][0]
        self.assertEqual(declaration['closed_region_values']['RODATA']['lo'], 0x8010f5f0)
        self.assertEqual(declaration['file']['path'], 'Machine.v')
        self.assertTrue((self.policy / source_map['paths']['Machine.v']['path']).is_file())
        self.assertFalse(region_windows.rewrite(self.policy, self.MACHINE, self.machine, [self.pins]))

    def test_a_map_for_another_elf_or_a_stale_pin_fails(self):
        self.assertIn('binds ELF', region_windows.problems(self.policy, dict(self.MACHINE, mapRodataBase=0x8010fd80,
                      mapRodataEnd=0x80118678), 'other-elf', [self.pins])[0])
        _, _, source_map = region_windows.load(self.policy)
        payload = source_map['archives']['regions.json.gz']['payload_sha256']
        self.pins.write_text(self.pins.read_text().replace(payload, 'f' * 64))
        found = region_windows.problems(self.policy, dict(self.MACHINE, mapRodataBase=0x8010fd80,
                                        mapRodataEnd=0x80118678), 'new-elf', [self.pins])
        self.assertTrue(any('pins' in item for item in found))


class TestTraceFixtureTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        root = Path(self.directory.name)
        self.build, self.fixtures = root / 'build', root / 'fixtures'
        (self.build / 'platform').mkdir(parents=True)
        self.fixtures.mkdir()
        (self.build / 'zesu-zisk.elf').write_bytes(small_elf())
        (self.build / 'platform/riscv64-zisk.ir').write_text('snapshot\n')
        (root / 'ZesuSsz').mkdir()
        (root / 'ZesuSsz/riscv64_zesu.toml').write_text('config\n')
        self.root = root
        for suffix in ('.isla', '.v'):
            (self.fixtures / ('Ret' + suffix)).write_text('trace\n')
        digest = check_test_traces.digest
        self.metadata = {'elf_sha256': digest(self.build / 'zesu-zisk.elf'),
                         'snapshot_sha256': digest(self.build / 'platform/riscv64-zisk.ir'),
                         'config_sha256': digest(root / 'ZesuSsz/riscv64_zesu.toml'),
                         'fixtures': [{'module': 'Ret', 'address': 0x80000000, 'opcode': '00008067',
                                       'isla_sha256': digest(self.fixtures / 'Ret.isla'),
                                       'rocq_sha256': digest(self.fixtures / 'Ret.v')}]}

    def problems(self):
        (self.fixtures / 'metadata.json').write_text(json.dumps(self.metadata))
        return check_test_traces.problems(self.fixtures, self.build, self.root)

    def test_matching_fixture_passes(self):
        self.assertEqual(self.problems(), [])

    def test_a_moved_instruction_or_a_new_snapshot_fails(self):
        self.metadata['fixtures'][0]['opcode'] = '05053803'
        self.assertIn('holds 00008067, not the fixture opcode 05053803', self.problems()[0])
        self.metadata['fixtures'][0].update(opcode='00008067', address=0x90000000)
        self.assertIn('holds no code', self.problems()[0])
        self.metadata['fixtures'][0]['address'] = 0x80000000
        self.metadata['snapshot_sha256'] = 'old'
        self.assertIn('snapshot_sha256', self.problems()[0])


class RecipeTests(unittest.TestCase):
    def test_trace_only_rows_update_by_name_or_path_and_none_are_added(self):
        inputs = {'eql/build/eql.dump': {'path': 'build/eql.dump', 'sha256': 'old'},
                  'regions/elf': {'path': 'build/zesu-zisk.elf', 'sha256': 'old'}}
        fragment = {'dump': {'path': '/repo/build/eql.dump', 'sha256': 'new-dump'},
                    'elf': {'path': '/repo/build/zesu-zisk.elf', 'sha256': 'new-elf'},
                    'per_load_regions': {'path': '/repo/build/regions.json.gz', 'sha256': 'x', 'payload_sha256': 'y'}}
        recipe.update_group_inputs(inputs, 'eql', fragment, Path('/repo'))
        recipe.update_group_inputs(inputs, 'regions', {'elf': fragment['elf']}, Path('/repo'))
        self.assertEqual(inputs, {'eql/build/eql.dump': {'path': 'build/eql.dump', 'sha256': 'new-dump'},
                                  'regions/elf': {'path': 'build/zesu-zisk.elf', 'sha256': 'new-elf'}})

    def test_a_trace_record_keeps_old_keys_and_completes_the_binding(self):
        old = {'kind': 'trace_only', 'generation_provenance': {'run': 1}, 'manifest_binding_pending': False}
        new = {'kind': 'trace_only', 'elf_sha256': 'e', 'manifest_binding_pending': True}
        self.assertEqual(list(recipe.trace_record(old, new).items()),
                         [('kind', 'trace_only'), ('generation_provenance', {'run': 1}),
                          ('manifest_binding_pending', False), ('elf_sha256', 'e')])

    def test_verification_reports_bound_native_coverage(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name) / 'verification.json'
        path.write_text(json.dumps({'trace_generation': 'not run', 'proof_status': 'not proved'}))
        row = {'elf_sha256': 'e', 'instruction_count': 4, 'generated_count': 3, 'full_closure_coverage': False,
               'unsupported_runtime_boundaries': [{'pc': '0x1'}], 'instruction_modules_validated': True,
               'manifest_binding_pending': False, 'commitments': {}}
        recipe.summarize_traces(path, {'artifact_identity': 'id', 'traces': {'decodeItem': row, 'closure': row}})
        report = json.loads(path.read_text())
        self.assertEqual(report['trace_generation'],
                         '3/4 decodeItem traces; 3/4 closure traces; CSR 0x813 remains unmodeled')
        self.assertEqual(report['trace_coverage']['closure']['bound_artifact_identity'], 'id')
        self.assertNotIn('commitments', report['trace_coverage']['closure'])


if __name__ == '__main__':
    unittest.main()
