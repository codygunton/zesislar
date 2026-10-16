"""Prepare the bounded package without replacing either older observer package."""
from pathlib import Path
import hashlib
import json
import re
import shutil

BOUNDED = 'tools/block/TracePlugin/Bounded'
BRIDGE = BOUNDED + '/TraceObserver.v'
BRIDGE_IMPORT = 'From P0Bounded Require Import TraceObserver.'
READER_TARGET = BOUNDED + '/trace-observer/kernel_reader.exe'
# MCP feedback uses the unchanged, reviewed streaming writer.
from trace_block_package import WRITER_TARGET
FILES = ('dune', 'TraceObserver.v', 'trace-observer/dune',
         'trace-observer/bounded_trace_plugin.ml', 'trace-observer/kernel_artifact.ml',
         'trace-observer/kernel_store.ml', 'trace-observer/kernel_display.ml',
         'trace-observer/kernel_capture.ml', 'trace-observer/kernel_reader.ml',
         'trace-observer/kernel_control.ml', 'trace-observer/artifact_control.ml',
         'trace-observer/trace_block_chunks.ml')
INSTALL_TARGETS = ('p0-bounded-trace.install', READER_TARGET, WRITER_TARGET)
PROTOCOL = 'bounded-kernel-v1'


def overlay_files(owner):
    import trace_block_package
    names = [BOUNDED + '/' + name for name in FILES]
    names += trace_block_package.overlay_files(owner)
    for name in names:
        path = Path(owner) / name
        if path.is_symlink() or not path.is_file():
            raise ValueError('A bounded package source is absent or linked: ' + name)
    return names


def configure(workspace):
    workspace = Path(workspace)
    nested = workspace / BOUNDED / 'dune-project'
    if nested.exists() or nested.is_symlink():
        raise ValueError('The bounded package must use the root Dune project.')
    project = workspace / 'dune-project'
    text = project.read_text()
    for package in ('p0-filtered-trace', 'p0-bounded-trace'):
        if re.search(r'\(package\s+\(name\s+' + package + r'\)', text) is None:
            text += '\n(package (name ' + package + ') (depends coq-core))\n'
    project.write_text(text)
    theory = workspace / 'ZesuSsz/dune'
    text = theory.read_text()
    if not re.search(r'\bP0Bounded\b', text):
        text, count = re.subn(r'\bRecordUpdate\s+Ltac2(?:\s+P0Filtered)?\s*\)\)',
                             'RecordUpdate Ltac2 P0Bounded))', text)
        if count != 1:
            raise ValueError('The bounded theory dependency has an unsupported boundary.')
        theory.write_text(text)
    return ('dune-project', 'ZesuSsz/dune')


def reference(path, *, sized=True):
    path = Path(path)
    with path.open('rb') as stream:
        digest = hashlib.file_digest(stream, 'sha256').hexdigest()
    result = {'path': str(path), 'sha256': digest}
    if sized:
        result['bytes'] = path.stat().st_size
    return result


def canonical_artifacts(paths):
    """Bind each resolved runtime path once and retain every alias association."""
    artifacts, aliases = {}, []
    for path in sorted(set(map(Path, paths))):
        resolved = path.resolve(strict=True)
        if not resolved.is_file():
            raise ValueError('A bounded runtime artifact is not a regular file.')
        checked = reference(resolved)
        previous = artifacts.setdefault(str(resolved), checked)
        if previous != checked:
            raise ValueError('A bounded runtime alias changed its hash or size.')
        aliases.append({'path': str(path), 'canonical': checked})
    return [artifacts[key] for key in sorted(artifacts)], aliases


def runtime_inputs(workspace, build):
    workspace, build = Path(workspace).resolve(strict=True), Path(build).resolve(strict=True)
    if not build.is_relative_to(workspace):
        raise ValueError('The bounded private build leaves its workspace.')
    package = build / 'install/default/lib/p0-bounded-trace'
    plugin = package / 'trace-observer/bounded_trace_plugin.cmxs'
    codec = package / 'kernel-codec/kernel_codec.cmxs'
    reader = build / 'default' / READER_TARGET
    compiled_bridge = build / 'default' / BRIDGE.replace('.v', '.vo')
    writer = build / 'default' / WRITER_TARGET
    required = (plugin, codec, reader, compiled_bridge, writer)
    for path in required:
        if not path.is_file() or not path.resolve(strict=True).is_relative_to(workspace):
            raise ValueError('A bounded runtime artifact is absent or outside its workspace: ' + str(path))
    coqpath = workspace / '_build/trace-native/coqpath'
    bridge = coqpath / 'P0Bounded/TraceObserver.vo'
    bridge.parent.mkdir(parents=True, exist_ok=True)
    if bridge.is_symlink():
        raise ValueError('The bounded bridge cannot be a symlink.')
    if bridge.exists() and reference(bridge)['sha256'] != reference(compiled_bridge)['sha256']:
        raise ValueError('The bounded bridge differs from its compiled source.')
    if not bridge.exists():
        shutil.copy2(compiled_bridge, bridge)
    pinned = Path('/home/cody/islaris/_opam')
    paths = list(required) + [bridge]
    for directory in (pinned / 'lib', build / 'install/default/lib'):
        if not directory.is_dir():
            raise ValueError('A pinned runtime directory is absent: ' + str(directory))
        paths.extend(path for path in directory.rglob('*')
                     if path.is_file() and (path.name == 'META' or path.suffix in ('.cmxs', '.cma')))
    paths.extend(pinned / 'bin' / name for name in ('coqc', 'coqtop', 'pet', 'ocamlc', 'ocamlopt'))
    artifacts, aliases = canonical_artifacts(paths)
    payload = {'schema': 1, 'policy': PROTOCOL, 'artifacts': artifacts}
    digest = hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()
    toolchain = workspace / '_build/trace-native' / ('BOUNDED-TOOLCHAIN-' + digest + '.json')
    serialized = (json.dumps(payload, sort_keys=True, indent=2) + '\n').encode()
    if toolchain.is_symlink() or (toolchain.exists() and toolchain.read_bytes() != serialized):
        raise ValueError('The immutable bounded inventory changed.')
    toolchain.write_bytes(serialized)
    alias_path = toolchain.with_name(toolchain.stem + '-ALIASES.json')
    alias_bytes = (json.dumps({'schema': 1, 'aliases': aliases}, sort_keys=True, indent=2) + '\n').encode()
    if alias_path.is_symlink() or (alias_path.exists() and alias_path.read_bytes() != alias_bytes):
        raise ValueError('The immutable bounded alias correspondence changed.')
    alias_path.write_bytes(alias_bytes)
    result = {'observer_runtime': {'surface_policy': PROTOCOL,
              'plugin': reference(plugin, sized=False), 'bridge': reference(bridge, sized=False),
              'coqpath': str(coqpath), 'kernel_reader': reference(reader),
              'kernel_toolchain': reference(toolchain)}, 'chunk_writer': reference(writer, sized=False)}
    validate_runtime(dict(result, workspace=str(workspace)))
    return result


def validate_runtime(request):
    """Use the same inventory checks as backend startup without writing evidence."""
    from trace_block_kernel_runtime import bounded_kernel, checked_reference
    runtime = request.get('observer_runtime')
    if not bounded_kernel(request) or set(runtime) != {
            'surface_policy', 'plugin', 'bridge', 'coqpath', 'kernel_reader', 'kernel_toolchain'}:
        raise ValueError('The preparation lacks its complete bounded runtime.')
    workspace = Path(request['workspace']).resolve(strict=True)
    for item in (runtime['plugin'], runtime['bridge'], request.get('chunk_writer')):
        if not isinstance(item, dict) or set(item) != {'path', 'sha256'}:
            raise ValueError('The bounded plugin, bridge, or writer reference has unsupported fields.')
        path = Path(item['path'])
        if not path.is_absolute() or not path.resolve(strict=True).is_relative_to(workspace):
            raise ValueError('A bounded plugin, bridge, or writer leaves its workspace.')
        if not path.is_file() or reference(path, sized=False) != item:
            raise ValueError('A bounded plugin, bridge, or writer changed its exact reference.')
    coqpath = Path(runtime['coqpath']).resolve(strict=True)
    if not coqpath.is_relative_to(workspace):
        raise ValueError('The bounded COQPATH leaves its workspace.')
    if Path(runtime['bridge']['path']).resolve() != coqpath / 'P0Bounded/TraceObserver.vo':
        raise ValueError('The bounded bridge differs from its owned P0Bounded path.')
    reader = checked_reference(runtime['kernel_reader'], workspace=workspace)
    toolchain = checked_reference(runtime['kernel_toolchain'], workspace=workspace)
    value = json.loads(Path(toolchain['path']).read_text())
    if value.get('schema') != 1 or not isinstance(value.get('artifacts'), list):
        raise ValueError('The bounded inventory schema is invalid.')
    rows = [checked_reference(row) for row in value['artifacts']]
    by_path = {row['path']: row for row in rows}
    if len(rows) != len(by_path) or toolchain['path'] in by_path:
        raise ValueError('The bounded inventory repeats a path or references itself.')
    for item in (runtime['plugin'], runtime['bridge'], reader, request['chunk_writer']):
        name = str(Path(item['path']).resolve(strict=True))
        if name not in by_path or by_path[name]['sha256'] != item['sha256']:
            raise ValueError('The bounded inventory omits a requested artifact.')
    for name in ('coqc', 'ocamlc', 'pet'):
        if str((Path('/home/cody/islaris/_opam/bin') / name).resolve(strict=True)) not in by_path:
            raise ValueError('The bounded inventory omits a pinned executable.')
