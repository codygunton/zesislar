"""Record and check the inputs and derived files of one stock ELF."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

from elftools.elf.elffile import ELFFile

REPORTS = {
    'disassembly.objdump': ['riscv64-elf-objdump', '-d'],
    'symbols.txt': ['riscv64-elf-readelf', '-Ws'],
    'elf-layout.txt': ['riscv64-elf-readelf', '-h', '-l', '-S'],
}
RUNTIME_COMMAND = ['cargo', '+zisk', 'build', '-p', 'ziskos-staticlib',
    '--target', 'riscv64ima-zisk-zkvm-elf', '--release', '--locked',
    '--config', 'profile.release.lto="fat"']
LEGACY_TOOLS = ['riscv64-linux-gnu-as', 'riscv64-linux-gnu-ld',
                'riscv64-linux-gnu-nm', 'riscv64-linux-gnu-objdump', 'z3']


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def file_record(path):
    path = Path(path).resolve()
    return {'path': str(path), 'sha256': digest(path)}


def normalized_report(command, elf):
    elf = Path(elf).resolve()
    text = subprocess.check_output([*command, elf.name], cwd=elf.parent, text=True)
    return ''.join(line.rstrip()+'\n' for line in text.splitlines())


def elf_layout(path):
    with Path(path).open('rb') as stream:
        elf = ELFFile(stream)
        segments = [dict(segment.header) for segment in elf.iter_segments()]
        sections = []
        for section in elf.iter_sections():
            record = {'name': section.name, **dict(section.header)}
            if section['sh_type'] != 'SHT_NOBITS':
                record['sha256'] = hashlib.sha256(section.data()).hexdigest()
            sections.append(record)
        return {'entry': elf['e_entry'], 'machine': elf['e_machine'],
                'flags': elf['e_flags'], 'segments': segments, 'sections': sections}


def artifact_identity(recipe):
    """Derived files bind to inputs and ELF, without a circular manifest hash."""
    fields = ['sources', 'zig_version', 'object_command', 'link_command',
              'linker_script_sha256', 'runtime_library_sha256',
              'stock_object_sha256', 'elf_sha256', 'adapters',
              'zig_executable_sha256', 'inputs', 'runtime_provenance', 'schema_versions']
    fields += [name for name in ['platform', 'machine_map'] if name in recipe]
    payload = {key: recipe[key] for key in fields}
    return hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()


def record_build(args, recipe, previous):
    """Extend the existing recipe; retain the independently built runtime inputs."""
    recipe['build_dir'] = str(args.build_dir)
    for name, source in recipe['sources'].items():
        path = getattr(args, name)
        source['path'] = str(path)
        source['tree'] = subprocess.check_output(
            ['git', '-C', str(path), 'rev-parse', 'HEAD^{tree}'], text=True).strip()
        source['patch_sha256'] = hashlib.sha256(b'').hexdigest()
    inputs = {name: record for name, record in previous['inputs'].items()
              if name.startswith('compiler/') and name.split('/')[-1] in ['rustc', 'cargo', 'cargo-zisk']}
    for name in ['Makefile', 'build.zig', 'build.zig.zon', 'src/zisk_host.zig']:
        inputs['guest/'+name] = file_record(args.guest/'zisk'/name)
    inputs['linker'] = file_record(args.guest/'zisk/zisk.ld')
    inputs['runtime'] = file_record(args.runtime_library)
    inputs['object'] = file_record(args.zesu/'zig-out/lib/zesu.o')
    for name in ['zig', 'riscv64-elf-objdump', 'riscv64-elf-readelf']:
        inputs['compiler/'+name] = file_record(shutil.which(name))
    for name in ['build.py', 'manifest.py']:
        inputs['builder/'+name] = file_record(Path(__file__).parent/name)
    for name in LEGACY_TOOLS:
        inputs['legacy/'+name] = file_record(Path(__file__).resolve().parents[2]/'bin'/name)
    recipe['inputs'] = inputs
    recipe['legacy_tool_policy'] = 'Retain the committed bin tools with explicit hashes for existing trace regeneration. The selected ELF build uses the separately recorded Zig and ELF tools.'
    recipe['runtime_provenance'] = previous['runtime_provenance']
    recipe['schema_versions'] = {'manifest': 1, 'elf_layout': 1}
    recipe['invalidated_derived'] = sorted(previous.get('derived', {}))
    recipe['derived'] = {}
    for name, command in REPORTS.items():
        (args.out/name).write_text(normalized_report(command, args.out/'zesu-zisk.elf'))
    refresh(args.out, recipe)


def refresh(out, recipe):
    out = Path(out)
    recipe['artifact_identity'] = artifact_identity(recipe)
    recipe['elf_layout'] = elf_layout(out/'zesu-zisk.elf')
    recipe['artifacts'] = {name: digest(out/name)
        for name in ['zesu-zisk.elf', *REPORTS]}
    for name, binding in recipe.get('derived', {}).items():
        if binding['artifact_identity'] != recipe['artifact_identity']:
            raise ValueError(f'Stale derived artifact: {name}')
        recipe['artifacts'][name] = digest(out/name)
    for name, binding in recipe.get('project_derived', {}).items():
        if binding['artifact_identity'] != recipe['artifact_identity']:
            raise ValueError(f'Stale project artifact: {name}')
        binding['sha256'] = digest(project_artifact_path(recipe, name, binding))
    (out/'build-recipe.json').write_text(json.dumps(recipe, indent=2)+'\n')
    sums = {**recipe['artifacts'], 'build-recipe.json': digest(out/'build-recipe.json')}
    for name in ['PROVENANCE.md', 'INVENTORY.md']:
        if (out/name).exists():
            sums[name] = digest(out/name)
    (out/'SHA256SUMS').write_text(''.join(f'{sha}  {name}\n' for name, sha in sorted(sums.items())))


def require_equal(actual, expected, label):
    if actual != expected:
        raise ValueError(f'{label} differs: {actual!r} != {expected!r}')


def project_artifact_path(recipe, name, binding):
    """Keep external generated artifacts inside the declared project root."""
    relative = Path(name)
    if relative.is_absolute() or '..' in relative.parts:
        raise ValueError(f'Invalid project artifact: {name}')
    root = Path(recipe['project_root']).resolve()
    path = (root/relative).resolve()
    if not path.is_relative_to(root):
        raise ValueError(f'Project artifact leaves its root: {name}')
    require_equal(Path(binding['path']).resolve(), path, f'{name} project path')
    return path


def check(out, pins):
    out = Path(out).resolve()
    recipe = json.loads((out/'build-recipe.json').read_text())
    require_equal(set(recipe['sources']), set(pins), 'Source set')
    for name, pin in pins.items():
        source = recipe['sources'][name]
        require_equal(source['commit'], pin, f'{name} pin')
        path = source['path']
        actual = subprocess.check_output(['git', '-C', path, 'rev-parse', 'HEAD'], text=True).strip()
        require_equal(actual, pin, f'{name} checkout')
        actual_tree = subprocess.check_output(['git', '-C', path, 'rev-parse', 'HEAD^{tree}'], text=True).strip()
        require_equal(actual_tree, source['tree'], f'{name} tree')
        patch = subprocess.check_output(['git', '-C', path, 'diff', '--binary', 'HEAD'])
        require_equal(patch, b'', f'{name} tracked source patch')
        require_equal(hashlib.sha256(patch).hexdigest(), source['patch_sha256'], f'{name} patch hash')
    require_equal(recipe['zig_version'], '0.16.0', 'Zig version')
    require_equal(subprocess.check_output([recipe['zig_executable'], 'version'], text=True).strip(), '0.16.0', 'Installed Zig')
    require_equal(digest(recipe['zig_executable']), recipe['zig_executable_sha256'], 'Zig executable')
    require_equal(recipe['adapters'], {}, 'Source adapters')
    jobs = recipe['jobs']
    if not isinstance(jobs, int) or not 1 <= jobs <= 48:
        raise ValueError('Invalid worker count')
    build_dir = Path(recipe['build_dir'])
    require_equal(recipe['object_command'], ['zig', 'build', 'rv64im-object',
        '-Doptimize=ReleaseFast', f'-j{jobs}', '--cache-dir', str(build_dir/'zig-local'),
        '--global-cache-dir', str(build_dir/'zig-global')], 'Object recipe')
    require_equal(recipe['link_command'], ['zig', 'build', '-Doptimize=ReleaseFast',
        f"-Dzesu_obj={recipe['sources']['zesu']['path']}/zig-out/lib/zesu.o", f'-j{jobs}',
        '--global-cache-dir', str(build_dir/'zig-global')], 'Link recipe')
    for name, record in recipe['inputs'].items():
        require_equal(digest(record['path']), record['sha256'], name)
    for name in ['Makefile', 'build.zig', 'build.zig.zon', 'src/zisk_host.zig']:
        record = recipe['inputs']['guest/'+name]
        expected_path = Path(recipe['sources']['guest']['path'])/'zisk'/name
        require_equal(Path(record['path']), expected_path, f'Author recipe: {name}')
    linker = Path(recipe['sources']['guest']['path'])/'zisk/zisk.ld'
    require_equal(Path(recipe['inputs']['linker']['path']), linker, 'Author linker script')
    require_equal(recipe['runtime_provenance']['container_image_id'],
        'sha256:3c7565636c6516f21c630b4b7e803de59574e9381b50e2b4ae082b2b20751318',
        'Runtime container identity')
    require_equal(recipe['runtime_provenance']['source_commit'], pins['zisk'], 'Runtime source')
    require_equal(recipe['runtime_provenance']['command'], RUNTIME_COMMAND, 'Runtime recipe')
    for name in ['rustc', 'cargo', 'cargo-zisk', 'zig', 'riscv64-elf-objdump', 'riscv64-elf-readelf']:
        if 'compiler/'+name not in recipe['inputs']:
            raise ValueError(f'Missing compiler identity: {name}')
    for name in LEGACY_TOOLS:
        if 'legacy/'+name not in recipe['inputs']:
            raise ValueError(f'Missing retained tool identity: {name}')
    for record in recipe['preserved_inputs']:
        require_equal(digest(record['archive_path']), record['sha256'], 'Preserved input')
    for key, name in [('linker_script_sha256', 'linker'),
                      ('runtime_library_sha256', 'runtime'), ('stock_object_sha256', 'object')]:
        require_equal(recipe[key], recipe['inputs'][name]['sha256'], key)
    guest_host = recipe['inputs']['guest/src/zisk_host.zig']['sha256']
    require_equal(recipe['link_without_exit_adapter'], {'passed': True, 'host_sha256': guest_host}, 'Unmodified host link')
    require_equal(recipe['elf_sha256'], digest(out/'zesu-zisk.elf'), 'ELF')
    require_equal(recipe['elf_layout'], elf_layout(out/'zesu-zisk.elf'), 'ELF layout and section bytes')
    require_equal(recipe['artifact_identity'], artifact_identity(recipe), 'Artifact identity')
    historical = recipe.get('historical_reports')
    if historical:
        old_elf = subprocess.check_output(['git', '-C', str(Path(__file__).resolve().parents[2]),
            'show', historical['source_commit']+':build/stock-zisk/zesu-zisk.elf'])
        require_equal(hashlib.sha256(old_elf).hexdigest(), historical['source_elf_sha256'], 'Historical ELF')
    if recipe.get('invalidated_derived'):
        raise ValueError(f"Derived artifacts need regeneration: {recipe['invalidated_derived']}")
    for name, binding in recipe.get('derived', {}).items():
        require_equal(binding['artifact_identity'], recipe['artifact_identity'], f'{name} identity')
        if not binding.get('schema_version'):
            raise ValueError(f'Missing schema version: {name}')
        if name not in recipe['artifacts']:
            raise ValueError(f'Unchecked derived artifact: {name}')
    for name, sha in recipe['artifacts'].items():
        if name == 'disassembly.objdump' and not (out/name).exists():
            report = normalized_report(REPORTS[name], out/'zesu-zisk.elf').encode()
            require_equal(hashlib.sha256(report).hexdigest(), sha, f'{name} regeneration')
            (out/name).write_bytes(report)
        require_equal(digest(out/name), sha, name)
    listed = {}
    for line in (out/'SHA256SUMS').read_text().splitlines():
        sha, name = line.split(None, 1)
        if name in listed or Path(name).is_absolute() or '..' in Path(name).parts:
            raise ValueError(f'Invalid checksum entry: {name}')
        listed[name] = sha
        require_equal(digest(out/name), sha, name)
    for name in [*recipe['artifacts'], 'build-recipe.json', 'PROVENANCE.md']:
        if name not in listed:
            raise ValueError(f'Missing checksum entry: {name}')
    for name, command in REPORTS.items():
        actual = normalized_report(command, out/'zesu-zisk.elf')
        require_equal((out/name).read_text(), actual, f'{name} regeneration')
    for name, binding in recipe.get('project_derived', {}).items():
        require_equal(binding['artifact_identity'], recipe['artifact_identity'], f'{name} identity')
        if not binding.get('schema_version'):
            raise ValueError(f'Missing schema version: {name}')
        require_equal(digest(project_artifact_path(recipe, name, binding)), binding['sha256'], name)
    count = len(recipe['artifacts']) + len(recipe.get('project_derived', {}))
    print(f"Checked {count} artifacts and {len(recipe['inputs'])} inputs: {recipe['artifact_identity']}")
    return recipe
