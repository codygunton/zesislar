"""Enter the shared workload parent before any preparation or proof input read."""
from pathlib import Path
import os
import subprocess
import sys

PARENT = 'zesuworkloads.slice'
PARENT_BYTES = 175 * 1024**3


def contained(*, proc=Path('/proc/self/cgroup'), cgroups=Path('/sys/fs/cgroup')):
    rows = [line.split(':', 2)[2] for line in proc.read_text().splitlines()
            if line.startswith('0::')]
    if len(rows) != 1:
        raise ValueError('The command lacks one cgroup-v2 identity.')
    parts = Path(rows[0].lstrip('/')).parts
    if PARENT not in parts:
        return False
    parent = cgroups.joinpath(*parts[:parts.index(PARENT) + 1])
    if ((parent / 'memory.max').read_text().strip() != str(PARENT_BYTES)
            or (parent / 'memory.swap.max').read_text().strip() != '0'):
        raise ValueError('The shared command parent lacks its exact memory backstop.')
    return True


def require():
    if not contained():
        raise ValueError('The shared operation must run inside zesuworkloads.slice.')


def enter(script, arguments, *, check=contained, run=subprocess.run, execute=os.execvpe):
    if check():
        return
    script = Path(script).absolute()
    guard = script.parents[3] / 'tools/resource_guard.sh'
    run([str(guard), 'parent-setup'], check=True)
    environment = dict(os.environ)
    environment.setdefault('XDG_RUNTIME_DIR', '/run/user/' + str(os.getuid()))
    environment.setdefault('DBUS_SESSION_BUS_ADDRESS',
                           'unix:path=' + environment['XDG_RUNTIME_DIR'] + '/bus')
    command = ['systemd-run', '--user', '--scope', '--quiet', '--collect',
               '--slice=' + PARENT, '--unit=zesu-block-command-' + str(os.getuid()) + '-' + str(os.getpid()),
               '-p', 'MemorySwapMax=0', '--', str(guard), 'parent-exec', '--',
               sys.executable, '-B', str(script), *arguments]
    execute(command[0], command, environment)
    raise RuntimeError('The scope launcher returned without replacing the command.')
