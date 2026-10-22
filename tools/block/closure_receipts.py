"""Bind closure objects and retain read-only physical compiler observations."""
import asyncio
from datetime import datetime, timezone
import json
from pathlib import Path
import re

from promotion_verification import digest, live


class ObjectBindings:
    def __init__(self, baseline, candidate):
        self.baseline = baseline
        self.candidate = candidate
        self.transitions = []

    @staticmethod
    def snapshot(arm):
        root = Path(arm['build_dir']).resolve() / 'default'
        result = {}
        for path in root.rglob('*.vo'):
            if not path.resolve().is_relative_to(Path(arm['workspace']).resolve()):
                raise ValueError('A closure object leaves its workspace.')
            result[str(path)] = digest(path)
        return result

    def check(self):
        for label, arm in [('baseline', self.baseline), ('candidate', self.candidate)]:
            expected = {row['path']: row['sha256'] for row in arm['objects']}
            if self.snapshot(arm) != expected:
                raise ValueError('A bound ' + label + ' object changed outside an accepted compilation.')

    def after(self, tool, arguments, result):
        expected_baseline = {row['path']: row['sha256'] for row in self.baseline['objects']}
        if self.snapshot(self.baseline) != expected_baseline:
            raise ValueError('A bound baseline object changed during verification.')
        expected = {row['path']: row['sha256'] for row in self.candidate['objects']}
        actual = self.snapshot(self.candidate)
        changed = {path for path in expected.keys() | actual.keys() if expected.get(path) != actual.get(path)}
        allowed = set()
        if tool == 'rocq_compile_file' and result and result.get('success') is True:
            root = Path(self.candidate['workspace']).resolve()
            source = Path(arguments['file']).resolve()
            if not source.is_relative_to(root) or Path(arguments['workspace']).resolve() != root:
                raise ValueError('A compilation names a different candidate workspace.')
            allowed.add(str(Path(self.candidate['build_dir']).resolve() / 'default' /
                            source.relative_to(root).with_suffix('.vo')))
        if not changed.issubset(allowed) or any(path not in actual for path in changed):
            raise ValueError('A dependency object changed without its successful compilation.')
        for path in sorted(changed):
            self.transitions.append(dict(path=path, before=expected.get(path), after=actual[path], tool=tool))
        self.candidate['objects'] = [dict(path=path, sha256=value) for path, value in sorted(actual.items())]


def validate_physical_receipt(row, executable, *, require_context=True):
    if row.get('executable') != executable['path'] or row.get('executable_sha256') != executable['sha256']:
        raise ValueError('The physical compiler identity differs from its binding.')
    if type(row.get('pid')) is not int or row['pid'] <= 0 or type(row.get('start_ticks')) is not int:
        raise ValueError('The physical compiler receipt has no exact process identity.')
    if row.get('memory_max_bytes') != 64 * 1024**3 or row.get('memory_swap_max_bytes') != 0:
        raise ValueError('The physical compiler memory or swap limit differs.')
    if not re.fullmatch(r'Max cpu time\s+unlimited\s+unlimited\s+seconds\s*', row.get('cpu_limit_line', '')):
        raise ValueError('The physical compiler CPU time is not unlimited.')
    controls = row.get('cpu_quota_controls')
    group = row.get('cgroup')
    if not isinstance(group, str) or not group.startswith('/') or '..' in Path(group).parts:
        raise ValueError('The physical compiler has no valid cgroup path.')
    current = Path('/sys/fs/cgroup') / group.lstrip('/')
    paths = []
    while True:
        paths.append(str(current / 'cpu.max'))
        if current == Path('/sys/fs/cgroup'):
            break
        current = current.parent
    if not isinstance(controls, list) or [entry.get('path') for entry in controls] != paths:
        raise ValueError('The physical compiler CPU quota ancestry is incomplete.')
    present = False
    for entry in controls:
        if type(entry.get('present')) is not bool:
            raise ValueError('A CPU quota control has no presence record.')
        if entry['present']:
            present = True
            if not re.fullmatch(r'max [1-9][0-9]*', entry.get('value', '')):
                raise ValueError('The physical compiler has a CPU quota.')
        elif 'value' in entry:
            raise ValueError('An absent CPU quota control has a value.')
    if not present:
        raise ValueError('The effective CPU quota is unavailable.')
    if not require_context:
        return  # Earlier admission receipts did not retain the physical cwd.
    if not isinstance(row.get('argv'), list) or not row['argv'] or row['argv'][0] != executable['path']:
        raise ValueError('The physical compiler argv differs.')
    if not isinstance(row.get('cwd'), str) or not Path(row['cwd']).is_absolute():
        raise ValueError('The physical compiler cwd is unavailable.')


def compiler_receipt(pid):
    directory = Path('/proc') / str(pid)
    fields = (directory / 'stat').read_text().rsplit(')', 1)[1].split()
    start, ppid = int(fields[19]), int(fields[1])
    executable = str((directory / 'exe').resolve(strict=True))
    group = next(line.split(':', 2)[2] for line in (directory / 'cgroup').read_text().splitlines()
                 if line.startswith('0::'))
    current = Path('/sys/fs/cgroup') / group.lstrip('/')
    controls = []
    while True:
        path = current / 'cpu.max'
        try:
            controls.append(dict(path=str(path), present=True, value=path.read_text().strip()))
        except FileNotFoundError:
            controls.append(dict(path=str(path), present=False))
        if current == Path('/sys/fs/cgroup'):
            break
        current = current.parent
    scope = Path('/sys/fs/cgroup') / group.lstrip('/')
    row = dict(pid=pid, start_ticks=start, ppid=ppid, executable=executable,
        executable_sha256=digest(executable),
        argv=[value.decode() for value in (directory / 'cmdline').read_bytes().split(b'\0') if value],
        cwd=str((directory / 'cwd').resolve(strict=True)), cgroup=group,
        memory_max_bytes=int((scope / 'memory.max').read_text()),
        memory_swap_max_bytes=int((scope / 'memory.swap.max').read_text()),
        cpu_limit_line=next(line for line in (directory / 'limits').read_text().splitlines()
                            if line.startswith('Max cpu time')), cpu_quota_controls=controls,
        observed_UTC=datetime.now(timezone.utc).isoformat())
    if not live(row):
        raise ProcessLookupError('The sampled compiler exited during observation.')
    return row


class ClosureObserver:
    """Never signal a process. Report observer failures after the MCP call ends."""
    def __init__(self, objects, executable, directory):
        self.objects, self.executable = objects, executable
        self.directory = Path(directory)
        self.directory.mkdir(parents=True, exist_ok=False)
        self.operations = []

    async def start(self, label, owner, tool, arguments):
        self.objects.check()
        if digest(self.executable['path']) != self.executable['sha256']:
            raise ValueError('The bound physical compiler changed.')
        token = dict(label=label, owner=owner, tool=tool, arguments=arguments,
                     sequence=len(self.operations), observed_compilers=[], observer_errors=[],
                     observer_error_count=0)
        stop = asyncio.Event()
        async def sample():
            seen = set()
            while not stop.is_set():
                try:
                    pending = [owner]
                    while pending:
                        parent = pending.pop()
                        if not live(parent):
                            continue
                        children = Path('/proc') / str(parent['pid']) / 'task' / str(parent['pid']) / 'children'
                        for text in children.read_text().split():
                            pid = int(text)
                            proc = Path('/proc') / text
                            fields = (proc / 'stat').read_text().rsplit(')', 1)[1].split()
                            child = dict(pid=pid, start_ticks=int(fields[19]))
                            if int(fields[1]) != parent['pid'] or not live(parent):
                                continue
                            pending.append(child)
                            if str((proc / 'exe').resolve(strict=True)) == self.executable['path']:
                                key = (pid, child['start_ticks'])
                                if key not in seen:
                                    row = compiler_receipt(pid)
                                    row['observed_parent'] = parent
                                    token['observed_compilers'].append(row)
                                    seen.add(key)
                except (FileNotFoundError, ProcessLookupError):
                    pass  # Confirmed process exit supplies no receipt.
                except Exception as error:
                    token['observer_error_count'] += 1
                    if len(token['observer_errors']) < 32:
                        token['observer_errors'].append(dict(type=type(error).__name__, message=str(error)))
                await asyncio.sleep(.005)
        token['_stop'] = stop
        token['_task'] = asyncio.create_task(sample())
        return token

    async def finish(self, token, result):
        token.pop('_stop').set()
        await token.pop('_task')
        token['result_success'] = bool(result and result.get('success') is True)
        self.operations.append(token)
        try:
            if token['observer_errors']:
                raise ValueError('The physical compiler observer recorded a metadata failure.')
            for row in token['observed_compilers']:
                validate_physical_receipt(row, self.executable)
            if token['tool'] in {'rocq_verify', 'rocq_compile_file'} and not token['observed_compilers']:
                raise ValueError('The proof operation has no physical compiler receipt.')
            self.objects.after(token['tool'], token['arguments'], result)
            token['limits_validated'] = True
        except BaseException as error:
            token['acceptance_error'] = dict(type=type(error).__name__, message=str(error))
            raise
        finally:
            path = self.directory / (f"{token['sequence']:04d}-" + token['label'] + '.json')
            with path.open('x') as stream:
                stream.write(json.dumps(token, indent=2) + '\n')
