"""Run one coqc compile in its own resource-guard scope (diagnostic only).

The wall limit, when given, sits inside the scope (`scope NAME -- timeout S coqc ...`),
so admission waits never count against it. The compiler output is stamped with
seconds since start ('<elapsed> <line>'), the format that the census parsers read."""
from pathlib import Path
import os
import subprocess
import time

TOOLS = Path(__file__).resolve().parents[1]


def guard_path():
    return os.environ.get('ZESU_RESOURCE_GUARD', str(TOOLS / 'resource_guard.sh'))


def coqc_args(args_json, timed=False):
    import json
    args = json.loads(Path(args_json).read_text())
    return args if timed else [a for a in args if a != '-time']


def command(tag, args, filename, limit_s=None):
    cmd = [guard_path(), 'scope', tag, '--']
    if limit_s:
        cmd += ['timeout', str(limit_s)]
    return cmd + list(args) + [filename]


def compile_file(path, tag, args, limit_s=None, stamp=False, extra_env=None, attempts=2):
    """Compile PATH in its directory; write PATH.log. Return a result dict:
    status pass|fail|timeout|killed|error, returncode, seconds, attempts. `error` means the
    compiler reported no error (a guard or setup failure), not a proof result; it is
    retried up to ATTEMPTS times in all."""
    for n in range(1, attempts + 1):
        res = _compile_once(path, tag, args, limit_s, stamp, extra_env)
        if res['status'] != 'error':
            break
    res['attempts'] = n
    return res


def _compile_once(path, tag, args, limit_s, stamp, extra_env):
    path = Path(path)
    log = path.with_suffix('.log')
    for cache in path.parent.glob('.*.cache'):
        cache.unlink()
    env = dict(os.environ, **(extra_env or {}))
    start = time.monotonic()
    try:
        with log.open('w') as out:
            proc = subprocess.Popen(command(tag, args, path.name, limit_s), cwd=path.parent, env=env,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            t0 = time.monotonic()
            for raw in proc.stdout:
                line = raw.decode('utf-8', 'replace').rstrip('\n')
                out.write(('%.3f %s\n' % (time.monotonic() - t0, line)) if stamp else line + '\n')
                out.flush()
            code = proc.wait()
    finally:
        for suf in ('.vo', '.vok', '.vos', '.glob'):
            path.with_suffix(suf).unlink(missing_ok=True)
        (path.parent / ('.' + path.stem + '.aux')).unlink(missing_ok=True)
        for cache in path.parent.glob('.*.cache'):
            cache.unlink()
    text = log.read_text(errors='replace')
    return dict(status=classify(code, text), returncode=code, seconds=round(time.monotonic() - start, 1))


def classify(code, text):
    if code == 0:
        return 'pass'
    if code == 124:
        return 'timeout'
    if code in (137, -9):
        return 'killed'
    if 'Error' in text:
        return 'fail'
    return 'error'
