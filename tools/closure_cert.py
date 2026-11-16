#!/usr/bin/env python3
"""Certify that one generated block caller closes: write CLOSURE.json, or NOT-CLOSED.json with the reason.

usage: closure_cert.py CASE --caller PATH --build DIR [--log LOG] [--measure FILE] [--head REV]
                       [--out DIR] [--limit-gib N] [--cpu SECONDS] [--coqc PATH]

Without --log the tool compiles PATH itself: the bank's Dune coqc recipe (DIR/coqc_recipe.json) with
-time and -o into OUT, under `resource_guard.sh batch` and `scope`, measured by tools/measure.py.
With --log it reads that run instead: LOG is the output tools/measure.py recorded (measure.json.log)
and FILE (default: the measure.json beside LOG) is its record. Launch a compile with
`tools/bg --heavy NAME python3 tools/closure_cert.py ...`.

CLOSURE.json is written only when all of these hold:
- PATH is byte-identical to the generated tools/block/generated/*/Caller<CASE>.v at the bank's head
  (the HEAD of the bank's workspace, or --head), and to the file coqc compiled;
- coqc's own exit status in the measure record is 0 (never a guard, perf or shell wrapper's exit);
- the log holds the -time record of the theorem's `Qed.` and of `Print Assumptions <theorem>.`, and
  that command printed "Closed under the global context";
- the coqc command has only -Q/-R/-I load paths inside the bank or the compiler's own installation,
  no -l/-require/-load-vernac-source or other option, and no COQPATH/ROCQPATH outside the bank;
- every .v under the bank load paths that is tracked at the head is byte-identical to it, no other
  .v there redefines a tactic (`Ltac ... ::=`, `Ltac2 Set`), and no .vo there lacks its .v.
It records head, bank, the hashes, CPU and peak memory. Any other outcome writes NOT-CLOSED.json.
Exit status: 0 closed, 1 not closed, 2 usage.

A compliance record (tools/block/render_open_blocks.py) moves a block to closed only with a valid
certificate at tools/block/closures/<callers directory>/<CASE>/CLOSURE.json whose head is an ancestor
of the record's head (record_problems below).
"""
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

TOOLS = Path(__file__).resolve().parent
SCHEMA = 'closure/1'
CLOSED_TEXT = 'Closed under the global context'
GENERATED = 'tools/block/generated'
RECORDS = 'tools/block/closures'
# Option -> number of arguments. Anything else in a certified coqc command refuses the certificate.
OPTIONS = {'-q': 0, '-boot': 0, '-time': 0, '-w': 1, '-native-compiler': 1, '-o': 1, '-I': 1, '-Q': 2, '-R': 2}
LOAD_OPTIONS = ('-I', '-Q', '-R')
CHARS = re.compile(r'^Chars (\d+) - (\d+) \[')
ASSUMPTION_HEADERS = ('Axioms:', 'Section Variables:', 'Opaque constants:', 'Transparent constants:')
REDEFINITION = re.compile(rb"\bLtac\s+[\w.']+(?:\s+[\w']+)*\s*::=|\bLtac2\s+Set\b")


class NotClosed(Exception):
    """The run does not certify a closure; the message is the reason."""


def sha256(path):
    digest = hashlib.sha256()
    with open(path, 'rb') as handle:
        for block in iter(lambda: handle.read(1 << 20), b''):
            digest.update(block)
    return digest.hexdigest()


def git_blob_id(data):
    return hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest()


def git(workspace, *args, check=True):
    result = subprocess.run(['git', '-C', str(workspace), *args], capture_output=True)
    if check and result.returncode:
        raise NotClosed('git ' + ' '.join(args) + ' failed: ' + result.stderr.decode(errors='replace').strip())
    return result


def bank_workspace(build):
    """The git workspace a bank was built from (Dune's private build record, else the enclosing repo)."""
    record = Path(build) / 'dune-build-dir.json'
    if record.is_file():
        workspace = json.loads(record.read_text()).get('workspace')
        if workspace:
            return Path(workspace)
    top = git(build, 'rev-parse', '--show-toplevel', check=False)
    if top.returncode:
        raise NotClosed(str(build) + ' is not inside a git workspace; pass --head with a bank inside one')
    return Path(top.stdout.decode().strip())


def resolve_head(workspace, head):
    return git(workspace, 'rev-parse', '--verify', (head or 'HEAD') + '^{commit}').stdout.decode().strip()


def theorem(caller_bytes):
    """(name, Qed byte span, Print Assumptions byte span) of the caller's certified theorem."""
    printed = list(re.finditer(rb'Print\s+Assumptions\s+([\w.\']+)\s*\.', caller_bytes))
    if not printed:
        raise NotClosed('the caller has no Print Assumptions command')
    name = printed[-1].group(1)
    lemma = re.search(rb'\b(?:Lemma|Theorem)\s+' + re.escape(name) + rb'\b', caller_bytes)
    if lemma is None:
        raise NotClosed('the caller does not state ' + name.decode())
    qed = re.compile(rb'\bQed\.').search(caller_bytes, lemma.end())
    if qed is None or qed.start() > printed[-1].start():
        raise NotClosed(name.decode() + ' does not end in Qed before its Print Assumptions')
    return name.decode(), qed.span(), printed[-1].span()


def check_log(text, name, qed, assumptions):
    lines = text.splitlines()
    spans = [(index, (int(match[1]), int(match[2]))) for index, line in enumerate(lines)
             if (match := CHARS.match(line))]
    qed_at = next((index for index, span in spans if span == qed), None)
    if qed_at is None:
        raise NotClosed('the log has no -time record of the Qed of %s (chars %d-%d)' % ((name,) + qed))
    printed = next((index for index, span in spans if span == assumptions and index > qed_at), None)
    if printed is None:
        raise NotClosed('the log has no -time record of Print Assumptions %s after its Qed' % name)
    previous = max(index for index, _ in spans if index < printed)
    output = [line.strip() for line in lines[previous + 1:printed]]
    if CLOSED_TEXT not in output or any(line.startswith(ASSUMPTION_HEADERS) for line in output):
        raise NotClosed('Print Assumptions %s did not print "%s"' % (name, CLOSED_TEXT))


def inside(path, roots):
    return any(path == root or path.is_relative_to(root) for root in roots)


def check_command(command, cwd, caller, build, coqc_prefix):
    """Return the bank load-path directories of a certified coqc command and its source argument."""
    build, cwd = Path(build).resolve(), Path(cwd)
    external = [coqc_prefix / 'lib'] if coqc_prefix else []
    sources, loads, index = [], [], 1
    while index < len(command):
        argument = command[index]
        if argument.endswith('.v') and not argument.startswith('-'):
            sources.append(argument)
            index += 1
            continue
        if argument not in OPTIONS:
            raise NotClosed('coqc option %s is not allowed in a certified compile' % argument)
        values = command[index + 1:index + 1 + OPTIONS[argument]]
        if len(values) != OPTIONS[argument]:
            raise NotClosed('coqc option %s lacks its argument' % argument)
        if argument in LOAD_OPTIONS:
            directory = (cwd / values[0]).resolve()
            if inside(directory, [build]):
                loads.append(directory)
            elif not inside(directory, external):
                raise NotClosed('load path %s %s is outside the bank %s' % (argument, directory, build))
        index += 1 + OPTIONS[argument]
    if [(cwd / source).resolve() for source in sources] != [Path(caller).resolve()]:
        raise NotClosed('coqc compiled %s, not the caller %s' % (sources, caller))
    return loads, sources[0]


def check_environment(environment, build, coqc_prefix):
    build = Path(build).resolve()
    for name in ('COQPATH', 'ROCQPATH', 'OCAMLPATH'):
        allowed = [build] + ([coqc_prefix / 'lib'] if name == 'OCAMLPATH' and coqc_prefix else [])
        for entry in filter(None, environment.get(name, '').split(os.pathsep)):
            if not inside(Path(entry).resolve(), allowed):
                raise NotClosed('%s entry %s is outside the bank' % (name, entry))


def check_bank(build, loads, workspace, head):
    """Every bank source on the load path is the head's, and nothing else redefines a tactic."""
    default = Path(build).resolve() / 'default'
    listing = git(workspace, 'ls-tree', '-r', '-z', head).stdout.decode()
    tracked = {}
    for entry in filter(None, listing.split('\0')):
        meta, path = entry.split('\t', 1)
        if path.endswith('.v'):
            tracked[path] = meta.split()[2]
    files = sorted({path for directory in loads for path in directory.rglob('*.v*')
                    if path.suffix in ('.v', '.vo') and path.is_file()})
    fingerprint = hashlib.sha256()
    for path in files:
        if path.suffix == '.vo':
            if not path.with_suffix('.v').is_file():
                raise NotClosed('bank object %s has no source' % path)
            continue
        data = path.read_bytes()
        relative = path.relative_to(default).as_posix() if path.is_relative_to(default) else None
        if relative in tracked:
            if git_blob_id(data) != tracked[relative]:
                raise NotClosed('bank source %s differs from %s at %s' % (path, relative, head[:12]))
        elif REDEFINITION.search(data):
            raise NotClosed('%s redefines a tactic and is not a source at %s' % (path, head[:12]))
        fingerprint.update(str(path.relative_to(Path(build).resolve())).encode() + b' '
                           + git_blob_id(data).encode() + b'\n')
    return fingerprint.hexdigest()


def generated_caller(workspace, head, case, data):
    """The generated caller at head that the caller copies byte for byte."""
    names = git(workspace, 'ls-tree', '-r', '--name-only', '-z', head, '--', GENERATED).stdout.decode()
    pattern = re.compile(re.escape(GENERATED) + r'/[^/]+/Caller' + re.escape(case) + r'\.v')
    candidates = [name for name in names.split('\0') if pattern.fullmatch(name)]
    if not candidates:
        raise NotClosed('no generated Caller%s.v exists at %s' % (case, head[:12]))
    for name in candidates:
        if git(workspace, 'cat-file', 'blob', head + ':' + name).stdout == data:
            return name
    raise NotClosed('the caller differs from the generated %s at %s' % (', '.join(candidates), head[:12]))


def certify(case, caller, build, measure_path, log_path=None, head=None):
    """Return the certificate record; raise NotClosed with the reason, a partial record attached."""
    facts = {'case': case, 'caller': str(Path(caller).resolve()), 'bank': str(Path(build).resolve())}
    try:
        caller_bytes = Path(caller).read_bytes()
        facts['caller_sha256'] = hashlib.sha256(caller_bytes).hexdigest()
        workspace = bank_workspace(build)
        facts['workspace'] = str(workspace)
        facts['head'] = resolve_head(workspace, head)
        facts['generated_caller'] = generated_caller(workspace, facts['head'], case, caller_bytes)
        facts['theorem'], qed, assumptions = theorem(caller_bytes)
        measure_path = Path(measure_path)
        if not measure_path.is_file():
            raise NotClosed('no measure record %s: the compile did not run under tools/measure.py' % measure_path)
        measure = json.loads(measure_path.read_text())
        facts['measure'], facts['measure_sha256'] = str(measure_path.resolve()), sha256(measure_path)
        if measure.get('schema') != 'measure/1':
            raise NotClosed('%s is not a tools/measure.py record' % measure_path)
        code = measure.get('returncode')
        facts['coqc_returncode'] = code
        if 'cpu_user' in measure:
            facts['cpu_seconds'] = round(measure['cpu_user'] + measure['cpu_sys'], 1)
            facts['max_rss_kib'] = measure['max_rss_kib']
            facts['peak_gib'] = round(measure['max_rss_kib'] / 2**20, 2)
            facts['wall_seconds'] = round(measure['wall'], 1)
        if code is None:
            raise NotClosed('the compile has no coqc exit status (killed or still running)')
        if code != 0:
            raise NotClosed('coqc exit %d' % code)
        command, cwd = measure['command'], Path(measure['cwd'])
        coqc = Path(measure.get('executable') or cwd / command[0]).resolve()
        facts['coqc'] = {'path': str(coqc), 'sha256': sha256(coqc), 'command': command, 'cwd': str(cwd)}
        prefix = coqc.parent.parent
        loads, source = check_command(command, cwd, caller, build, prefix)
        check_environment(measure.get('environment', {}), build, prefix)
        if measure.get('inputs', {}).get(source) != facts['caller_sha256']:
            raise NotClosed('the compiled source is not byte-identical to the caller')
        log_path = Path(log_path or measure['log'])
        if not log_path.is_file() or sha256(log_path) != measure.get('log_sha256'):
            raise NotClosed('%s is not the coqc output recorded in %s' % (log_path, measure_path))
        facts['log'], facts['log_sha256'] = str(log_path.resolve()), measure['log_sha256']
        check_log(log_path.read_text(errors='replace'), facts['theorem'], qed, assumptions)
        facts['bank_sources_sha256'] = check_bank(build, loads, workspace, facts['head'])
        output = command[command.index('-o') + 1] if '-o' in command else Path(source).with_suffix('.vo')
        output = (cwd / output).resolve()
        if not output.is_file():
            raise NotClosed('the compiled object %s is missing' % output)
        facts['vo'] = {'path': str(output), 'sha256': sha256(output)}
    except NotClosed as error:
        error.facts = facts
        raise
    return facts


def write_verdict(out, record):
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    name, other = ('CLOSURE.json', 'NOT-CLOSED.json') if record['verdict'] == 'CLOSED' else ('NOT-CLOSED.json', 'CLOSURE.json')
    (out / other).unlink(missing_ok=True)
    pending = out / (name + '.pending')
    pending.write_text(json.dumps(record, indent=1, sort_keys=True) + '\n')
    pending.replace(out / name)
    return out / name


def verdict(case, caller, build, measure, log=None, head=None, out=None):
    """Certify, write CLOSURE.json or NOT-CLOSED.json into out, and return the record."""
    try:
        record = dict(certify(case, caller, build, measure, log, head), verdict='CLOSED')
    except NotClosed as error:
        record = dict(getattr(error, 'facts', {'case': case}), verdict='NOT-CLOSED', reason=str(error))
    record.update(schema=SCHEMA, certified_utc=datetime.now(timezone.utc).isoformat(),
                  tool_sha256=sha256(__file__))
    if out is not None:
        record['file'] = str(write_verdict(out, record))
    return record


def done_line(record):
    """The run's last line: coqc's own exit status and the certificate verdict."""
    code = record.get('coqc_returncode')
    line = 'RUN-DONE case=%s coqc_rc=%s verdict=%s' % (record['case'], 'none' if code is None else code,
                                                       record['verdict'])
    if record['verdict'] != 'CLOSED':
        line += ' reason=' + json.dumps(record['reason'])
    return line


def recipe_command(build, coqc, caller, output):
    """The bank's Dune coqc command for one caller, with -time and -o, and its working directory."""
    sys.path.insert(0, str(TOOLS))
    from coqc_recipe import remember_recipe
    from dune_build_dir import physical_working_dir
    build = Path(build).resolve()
    recipe = remember_recipe(build)
    if recipe is None:
        raise SystemExit('no coqc recipe in %s: build a proof target in the bank first' % build)
    flags, arguments = [], iter(recipe['command'][1:])
    for argument in arguments:
        if argument == '-o':
            next(arguments, None)
        elif not argument.endswith('.v'):
            flags.append(argument)
    working = Path(recipe['working_dir'] or build / 'default')
    if not working.is_absolute():
        working = bank_workspace(build) / working
    working = Path(physical_working_dir(build, str(working)))
    return [str(coqc), '-time', *flags, '-o', str(output), str(Path(caller).resolve())], working


def compile_caller(case, caller, build, out, limit_gib=16, cpu=None, coqc=None, name=None):
    """Compile the caller in the bank under the resource guard. Returns the guard's exit status,
    which says nothing about coqc: read coqc's status from out/measure.json."""
    out = Path(out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    for stale in ('measure.json', 'measure.json.log', 'CLOSURE.json', 'NOT-CLOSED.json'):
        (out / stale).unlink(missing_ok=True)
    coqc = coqc or shutil.which('coqc')
    if coqc is None:
        raise SystemExit('no coqc on PATH; pass --coqc')
    command, working = recipe_command(build, Path(coqc).resolve(), caller, out / ('Caller' + case + '.vo'))
    guard = os.environ.get('ZESU_RESOURCE_GUARD', str(TOOLS / 'resource_guard.sh'))
    name = name or 'cert-' + case
    environment = {key: value for key, value in os.environ.items() if key not in ('COORD_AGENT', 'COORD_ROOT')}
    ocamlpath = Path(build) / 'coqc-ocamlpath.json'
    if ocamlpath.is_file():
        environment['OCAMLPATH'] = json.loads(ocamlpath.read_text())['OCAMLPATH']
    cpu_limit = str(cpu) if cpu else 'unlimited'
    environment.update(ZESU_MODULE_CLAIM_BYTES=str(limit_gib * 1024**3 * 9 // 10),
                       ZESU_MODULE_LIMIT_GIB=str(limit_gib), ZESU_GATE_MODULE_LIMIT_GIB=str(limit_gib),
                       ZESU_PROOF_CPU_LIMIT=cpu_limit, ZESU_SCOPE_CPU=cpu_limit,
                       OCAMLRUNPARAM='s=32M,a=2,o=40')
    scope = [guard, 'scope', name] + (['--cpu', str(cpu)] if cpu else []) + ['--']
    wrapped = [guard, 'batch', name, '--', *scope, sys.executable, str(TOOLS / 'measure.py'),
               str(out / 'measure.json'), '--', *command]
    with (out / 'run.log').open('w') as log:
        return subprocess.run(wrapped, cwd=working, env=environment, stdout=log, stderr=subprocess.STDOUT).returncode


def record_problems(workspace, callers_dir, cases, head='HEAD'):
    """Why the closed cases of a compliance record lack valid certificates (empty: all valid).

    callers_dir: the generated callers directory, relative to workspace. Certificates live at
    tools/block/closures/<callers_dir name>/<case>/CLOSURE.json."""
    workspace, callers_dir = Path(workspace), Path(callers_dir)
    try:
        head = resolve_head(workspace, head)
    except NotClosed as error:
        return [str(error)]
    problems = []
    for case in cases:
        path = Path(RECORDS) / callers_dir.name / case / 'CLOSURE.json'
        caller = (callers_dir / ('Caller' + case + '.v')).as_posix()
        try:
            if not (workspace / path).is_file():
                raise NotClosed('missing')
            record = json.loads((workspace / path).read_text())
            if record.get('schema') != SCHEMA or record.get('verdict') != 'CLOSED' or record.get('case') != case:
                raise NotClosed('not a CLOSED certificate of ' + case)
            if record.get('generated_caller') != caller:
                raise NotClosed('certifies %s, not %s' % (record.get('generated_caller'), caller))
            cert_head = record.get('head') or ''
            if not re.fullmatch(r'[0-9a-f]{40}', cert_head) or git(
                    workspace, 'merge-base', '--is-ancestor', cert_head, head, check=False).returncode:
                raise NotClosed('head %s is not an ancestor of %s' % (cert_head[:12], head[:12]))
            blob = git(workspace, 'cat-file', 'blob', cert_head + ':' + caller, check=False)
            if blob.returncode or hashlib.sha256(blob.stdout).hexdigest() != record.get('caller_sha256'):
                raise NotClosed('caller hash differs from %s at %s' % (caller, cert_head[:12]))
        except (NotClosed, ValueError) as error:
            problems.append('%s: %s' % (path, error))
    return problems


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('case')
    parser.add_argument('--caller', type=Path, required=True)
    parser.add_argument('--build', type=Path, required=True)
    parser.add_argument('--log', type=Path, help='read this measured run instead of compiling')
    parser.add_argument('--measure', type=Path)
    parser.add_argument('--head', help='the commit the bank was built from (default: its workspace HEAD)')
    parser.add_argument('--out', type=Path, help='where the verdict goes (default: the log or caller directory)')
    parser.add_argument('--limit-gib', type=int, default=16)
    parser.add_argument('--cpu', type=int)
    parser.add_argument('--coqc', type=Path)
    options = parser.parse_args(argv)
    out = options.out or (options.log.parent if options.log else options.caller.parent)
    if GENERATED in out.resolve().as_posix():
        parser.error('the verdict would land in a generated callers directory; pass --out')
    if options.log is None:
        compile_caller(options.case, options.caller, options.build, out, options.limit_gib, options.cpu, options.coqc)
        measure = Path(out) / 'measure.json'
    else:
        measure = options.measure or (options.log.with_suffix('') if options.log.suffix == '.log'
                                      and options.log.with_suffix('').is_file() else options.log.parent / 'measure.json')
    record = verdict(options.case, options.caller, options.build, measure, options.log, options.head, out)
    print(done_line(record), flush=True)
    if record['verdict'] == 'CLOSED':
        callers = Path(record['generated_caller']).parent.name
        print('record: cp %s %s/%s/%s/CLOSURE.json' % (record['file'], RECORDS, callers, options.case))
    return 0 if record['verdict'] == 'CLOSED' else 1


if __name__ == '__main__':
    sys.exit(main())
