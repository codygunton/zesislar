"""Exercise manifest refusal without external checkouts or a compiler installation."""
import copy
import json
from pathlib import Path
import struct
import tempfile
import unittest
from unittest.mock import patch

import manifest


def small_elf():
    names = b'\0.text\0.shstrtab\0'
    ident = b'\x7fELF\x02\x01\x01'+bytes(9)
    header = struct.pack('<16sHHIQQQIHHHHHH', ident, 2, 243, 1, 0x80000000,
                         64, 144, 0, 64, 56, 1, 64, 3, 2)
    segment = struct.pack('<IIQQQQQQ', 1, 1, 120, 0x80000000, 0x80000000, 4, 4, 4)
    prefix = header+segment+bytes.fromhex('67800000')+names
    sections = bytes(64)
    sections += struct.pack('<IIQQQQIIQQ', 1, 1, 6, 0x80000000, 120, 4, 0, 0, 4, 0)
    sections += struct.pack('<IIQQQQIIQQ', 7, 3, 0, 0, 124, len(names), 0, 0, 1, 0)
    return prefix+bytes(144-len(prefix))+sections


class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.out = self.root/'out'
        self.out.mkdir()
        self.pins = {'zesu': 'zesu-pin', 'guest': 'guest-pin', 'zisk': 'zisk-pin'}
        sources = {}
        for name, pin in self.pins.items():
            path = self.root/name
            path.mkdir()
            sources[name] = {'path': str(path), 'commit': pin, 'tree': name+'-tree',
                            'patch_sha256': manifest.hashlib.sha256(b'').hexdigest()}
        inputs = {}

        def add(name, path):
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(name)
            inputs[name] = manifest.file_record(path)

        for name in ['Makefile', 'build.zig', 'build.zig.zon', 'src/zisk_host.zig']:
            add('guest/'+name, self.root/'guest/zisk'/name)
        add('linker', self.root/'guest/zisk/zisk.ld')
        for name in ['runtime', 'object']:
            add(name, self.root/name)
        for name in ['rustc', 'cargo', 'cargo-zisk', 'zig', *[c[0] for c in manifest.REPORTS.values()]]:
            add('compiler/'+name, self.root/'compiler'/name)
        for name in manifest.LEGACY_TOOLS:
            add('legacy/'+name, self.root/'legacy'/name)
        build = self.root/'build'
        self.recipe = {
            'sources': sources, 'zig_version': '0.16.0', 'jobs': 2, 'build_dir': str(build),
            'zig_executable': inputs['compiler/zig']['path'],
            'zig_executable_sha256': inputs['compiler/zig']['sha256'],
            'object_command': ['zig', 'build', 'rv64im-object', '-Doptimize=ReleaseFast', '-j2',
                               '--cache-dir', str(build/'zig-local'), '--global-cache-dir', str(build/'zig-global')],
            'link_command': ['zig', 'build', '-Doptimize=ReleaseFast',
                             f'-Dzesu_obj={self.root}/zesu/zig-out/lib/zesu.o', '-j2',
                             '--global-cache-dir', str(build/'zig-global')],
            'inputs': inputs, 'adapters': {}, 'preserved_inputs': [],
            'schema_versions': {'manifest': 1, 'elf_layout': 1},
            'link_without_exit_adapter': {'passed': True, 'host_sha256': inputs['guest/src/zisk_host.zig']['sha256']},
            'runtime_provenance': {'container_image_id': 'sha256:3c7565636c6516f21c630b4b7e803de59574e9381b50e2b4ae082b2b20751318',
                                   'source_commit': self.pins['zisk'], 'command': manifest.RUNTIME_COMMAND},
            'linker_script_sha256': inputs['linker']['sha256'],
            'runtime_library_sha256': inputs['runtime']['sha256'],
            'stock_object_sha256': inputs['object']['sha256'], 'derived': {}}
        (self.out/'zesu-zisk.elf').write_bytes(small_elf())
        self.recipe['elf_sha256'] = manifest.digest(self.out/'zesu-zisk.elf')
        for name in [*manifest.REPORTS, 'PROVENANCE.md']:
            (self.out/name).write_text('report\n')
        manifest.refresh(self.out, self.recipe)
        self.addCleanup(patch.stopall)
        patch('manifest.subprocess.check_output', side_effect=self.command).start()
        patch('manifest.normalized_report', return_value='report\n').start()

    def command(self, args, **kwargs):
        if args[0] == 'git':
            name = Path(args[2]).name
            if args[3] == 'diff': return b''
            return (name+'-tree\n') if args[-1] == 'HEAD^{tree}' else self.pins[name]+'\n'
        if args[-1] == 'version': return '0.16.0\n'
        raise AssertionError(args)

    def test_valid(self):
        manifest.check(self.out, self.pins)

    def add_project_artifact(self):
        path = self.root/'generated/trace.v'
        path.parent.mkdir()
        path.write_text('selected trace\n')
        self.recipe['project_root'] = str(self.root)
        self.recipe['project_derived'] = {'generated/trace.v': {
            'path': str(path), 'artifact_identity': self.recipe['artifact_identity'],
            'schema_version': 1}}
        manifest.refresh(self.out, self.recipe)
        return path

    def test_project_artifact(self):
        self.add_project_artifact()
        manifest.check(self.out, self.pins)

    def test_changed_project_artifact(self):
        self.add_project_artifact().write_text('changed trace\n')
        with self.assertRaisesRegex(ValueError, 'generated/trace.v differs'):
            manifest.check(self.out, self.pins)

    def test_project_artifact_escape(self):
        self.add_project_artifact()
        binding = self.recipe['project_derived']['generated/trace.v']
        binding['path'] = str(self.root/'elsewhere.v')
        with self.assertRaisesRegex(ValueError, 'project path'):
            manifest.refresh(self.out, self.recipe)

    def test_platform_changes_identity(self):
        before = manifest.artifact_identity(self.recipe)
        self.recipe['platform'] = {'kind': 'dedicated-zisk-platform-layer'}
        self.assertNotEqual(before, manifest.artifact_identity(self.recipe))

    def test_missing_disassembly(self):
        report = self.out/'disassembly.objdump'
        report.unlink()
        manifest.check(self.out, self.pins)
        self.assertEqual(report.read_text(), 'report\n')

    def test_wrong_regenerated_disassembly(self):
        report = self.out/'disassembly.objdump'
        report.unlink()
        with patch('manifest.normalized_report', return_value='changed\n'):
            with self.assertRaisesRegex(ValueError, 'disassembly.objdump regeneration'):
                manifest.check(self.out, self.pins)
        self.assertFalse(report.exists())

    def test_corrupt_disassembly(self):
        report = self.out/'disassembly.objdump'
        report.write_text('changed\n')
        with self.assertRaisesRegex(ValueError, 'disassembly.objdump'):
            manifest.check(self.out, self.pins)
        self.assertEqual(report.read_text(), 'changed\n')

    def test_changed_recipe(self):
        for field, value in [('object_command', ['zig', 'build', 'zisk-object']),
                             ('adapters', {'exit.zig': 'unapproved'})]:
            with self.subTest(field=field):
                bad = copy.deepcopy(self.recipe)
                bad[field] = value
                manifest.refresh(self.out, bad)
                with self.assertRaises(ValueError): manifest.check(self.out, self.pins)

    def test_changed_compiler(self):
        Path(self.recipe['zig_executable']).write_text('changed')
        with self.assertRaisesRegex(ValueError, 'Zig executable'):
            manifest.check(self.out, self.pins)

    def test_changed_instruction(self):
        path = self.out/'zesu-zisk.elf'
        data = bytearray(path.read_bytes())
        data[120] ^= 0x10
        path.write_bytes(data)
        with self.assertRaisesRegex(ValueError, 'ELF'):
            manifest.check(self.out, self.pins)

    def test_stale_derived(self):
        self.recipe['derived']['cfg.json'] = {'artifact_identity': 'old', 'schema_version': 1}
        with self.assertRaisesRegex(ValueError, 'Stale derived'):
            manifest.refresh(self.out, self.recipe)

    def test_missing_checksum(self):
        sums = self.out/'SHA256SUMS'
        sums.write_text(''.join(line+'\n' for line in sums.read_text().splitlines() if 'symbols.txt' not in line))
        with self.assertRaisesRegex(ValueError, 'Missing checksum'):
            manifest.check(self.out, self.pins)


if __name__ == '__main__':
    unittest.main()
