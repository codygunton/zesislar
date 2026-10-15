"""Install the filtered diagnostic package without replacing the legacy package."""

from pathlib import Path
import re
import shutil

FILTERED = 'tools/block/TracePlugin/Filtered'
BRIDGE = FILTERED + '/TraceObserver.v'
BRIDGE_IMPORT = 'From P0Filtered Require Import TraceObserver.'
FILES = ('dune', 'TraceObserver.v', 'chunk_control.ml', 'trace-observer/dune',
         'trace-observer/filtered_trace_plugin.ml', 'trace-observer/trace_block_chunks.ml')
WRITER_TARGET = FILTERED + '/chunk_control.exe'


def overlay_files(owner):
    """Name every source file needed by the independent filtered package."""
    names = [FILTERED + '/' + name for name in FILES] + ['META.p0-filtered-trace.template']
    for name in names:
        path = Path(owner)/name
        if path.is_symlink() or not path.is_file():
            raise ValueError('A filtered package source is absent or linked: ' + name)
    return names


def configure(workspace):
    """Add only the diagnostic package and theory dependency to the copy."""
    workspace = Path(workspace)
    project = workspace/'dune-project'
    text = project.read_text()
    if re.search(r'\(package\s+\(name\s+p0-filtered-trace\)', text) is None:
        text += '\n(package (name p0-filtered-trace) (depends coq-core))\n'
        project.write_text(text)
    theory = workspace/'ZesuSsz/dune'
    text = theory.read_text()
    if not re.search(r'\bLtac2\s+P0Filtered\s*\)\)', text):
        text, count = re.subn(r'\bRecordUpdate\s+Ltac2\s*\)\)', 'RecordUpdate Ltac2 P0Filtered))', text)
        if count != 1:
            raise ValueError('The diagnostic theory dependency has an unsupported boundary.')
        theory.write_text(text)
    return ('dune-project', 'ZesuSsz/dune')


def runtime_inputs(workspace, build):
    """Copy the compiled bridge to an owned COQPATH and bind runtime bytes."""
    from trace_block_seal import file_sha256
    workspace, build = Path(workspace).resolve(strict=True), Path(build).resolve(strict=True)
    if not build.is_relative_to(workspace):
        raise ValueError('The filtered private build leaves its workspace.')
    plugin = build/'install/default/lib/p0-filtered-trace/trace-observer/filtered_trace_plugin.cmxs'
    compiled_bridge = build/'default'/BRIDGE.replace('.v', '.vo')
    writer = build/'default'/WRITER_TARGET
    for path in (plugin, compiled_bridge, writer):
        if not path.is_file() or not path.resolve(strict=True).is_relative_to(workspace):
            raise ValueError('A filtered runtime artifact is absent or outside its workspace: ' + str(path))
    coqpath = workspace/'_build/trace-native/coqpath'
    bridge = coqpath/'P0Filtered/TraceObserver.vo'
    bridge.parent.mkdir(parents=True, exist_ok=True)
    if bridge.is_symlink():
        raise ValueError('The runtime bridge cannot be a symlink.')
    if bridge.exists():
        if file_sha256(bridge) != file_sha256(compiled_bridge):
            raise ValueError('The retained runtime bridge differs from the compiled bridge.')
    else:
        shutil.copy2(compiled_bridge, bridge)
    def reference(path):
        return {'path': str(path), 'sha256': file_sha256(path)}
    result = {'observer_runtime': {'plugin': reference(plugin), 'bridge': reference(bridge), 'coqpath': str(coqpath)},
              'chunk_writer': reference(writer)}
    validate_runtime(dict(result, workspace=str(workspace)))
    return result


def validate_runtime(request):
    """Reject an incomplete cached runtime before the MCP server starts."""
    from trace_block_seal import checked_reference
    workspace = Path(request['workspace']).resolve(strict=True)
    runtime = request.get('observer_runtime')
    if not isinstance(runtime, dict) or set(runtime) != {'plugin', 'bridge', 'coqpath'}:
        raise ValueError('The preparation lacks its complete filtered runtime.')
    coqpath = Path(runtime['coqpath']).resolve(strict=True)
    if not coqpath.is_relative_to(workspace):
        raise ValueError('The filtered COQPATH leaves its workspace.')
    for reference in (runtime['plugin'], runtime['bridge'], request.get('chunk_writer')):
        path = checked_reference(reference).resolve(strict=True)
        if not path.is_relative_to(workspace):
            raise ValueError('A filtered runtime artifact leaves its workspace.')
    if Path(runtime['bridge']['path']).resolve() != coqpath/'P0Filtered/TraceObserver.vo':
        raise ValueError('The runtime bridge differs from the owned P0Filtered path.')
