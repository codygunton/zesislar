#!/usr/bin/env python3
"""Check that a caller's proof search does not depend on imports placed after ZesuSsz.Automation2.All.

Importing a module re-adds the original body of every tactic it defines (Coq's `open_md`), so a
library import after the umbrella undoes any `Ltac <library tactic> ::=` override whose tactic that
import reaches: `From Coq Require Import Lia.` restored Coq's `lia` over Automation2's override and
flipped decodeParentHeader 0300 from 9 leftover goals to Qed. Automation2 therefore calls its own
`zesu_lia` (LiaHook). This tool compiles the unmodified caller and one copy per extra import (the
line goes after the caller's final import), all with ZESU_TELEMETRY=1, and compares their
proof-search streams: the ordered (kind, site, stage) of every telemetry record (steps,
alternatives, solver calls: a library tactic that reaches the library `lia` instead of `zesu_lia`
drops its `lia` records). Failed-alternative and backtrack records are left out: telemetry prints
them only above 1 ms CPU, so they vary with load. Equal streams and equal coqc status: the proof
does not depend on that import.

usage (launch with `tools/bg --heavy NAME python3 tools/import_invariance.py ...`):
  import_invariance.py --case CASE --caller FILE --build BANK --out DIR [--limit-gib N]
                       [--import LINE ...]
Writes DIR/<variant>/{Caller<CASE>.v,run.log,measure.json} and DIR/IMPORT-INVARIANCE.json.
Exit 0: every stream equals the unmodified caller's; 1: a stream differs; 2: a compile did not run.
"""
import argparse
import json
import os
import re
import sys
from pathlib import Path

DEFAULT_IMPORTS = (
    'From Coq Require Import Lia.',
    'From stdpp Require Import tactics.',
    'From iris.proofmode Require Import proofmode.',
)
IMPORT_LINE = re.compile(r'^\s*(?:From\s+\S+\s+)?(?:Require(?:\s+(?:Import|Export))?|Import|Export)\s')
SEARCH_RECORD = re.compile(r'^@@T kind=(\S+) site=(\S+) stage=(\S+)')
# Telemetry prints these only above 1 ms CPU (Automation2/Telemetry.v), so their presence follows
# machine load: two runs of the same proof differ in them.
TIMING_FILTERED = frozenset({'altfail', 'backtrack', 'stepbacktrack'})


def insert_after_imports(text, line):
    """The caller with LINE after its final import command (one import per line, as generated)."""
    lines = text.splitlines()
    last = max((index for index, row in enumerate(lines) if IMPORT_LINE.match(row)), default=None)
    if last is None:
        raise ValueError('the caller has no import command')
    return '\n'.join(lines[:last + 1] + [line] + lines[last + 1:]) + '\n'


def search_stream(log_text):
    """The ordered proof-search records of a telemetry log, without the timing-filtered kinds."""
    return [match.groups() for match in map(SEARCH_RECORD.match, log_text.splitlines())
            if match and match.group(1) not in TIMING_FILTERED]


def first_difference(base, other):
    """Index of the first differing record, or None when the streams are equal."""
    for index, (left, right) in enumerate(zip(base, other)):
        if left != right:
            return index
    return None if len(base) == len(other) else min(len(base), len(other))


def compile_variant(case, caller, build, out, limit_gib):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import closure_cert
    os.environ['ZESU_TELEMETRY'] = '1'
    closure_cert.compile_caller(case, caller, build, out, limit_gib=limit_gib,
                                name=f'invariance-{case}-{out.name}')
    measure = out / 'measure.json'
    code = json.loads(measure.read_text()).get('returncode') if measure.is_file() else None
    return code, search_stream((out / 'run.log').read_text(errors='replace'))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--case', required=True)
    parser.add_argument('--caller', type=Path, required=True)
    parser.add_argument('--build', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--limit-gib', type=int, default=16)
    parser.add_argument('--import', dest='imports', action='append')
    args = parser.parse_args()
    out = args.out.resolve()
    source = args.caller.read_text()
    imports = args.imports or list(DEFAULT_IMPORTS)
    variants = [('unmodified', source, None)] + [
        (f'import{index}', insert_after_imports(source, line), line)
        for index, line in enumerate(imports, 1)]
    results = {}
    for name, text, _ in variants:
        directory = out / name
        directory.mkdir(parents=True, exist_ok=True)
        caller = directory / f'Caller{args.case}.v'
        caller.write_text(text)
        results[name] = compile_variant(args.case, caller, args.build, directory, args.limit_gib)
    base_code, base_stream = results['unmodified']
    report = {'case': args.case, 'caller': str(args.caller.resolve()), 'unmodified_returncode': base_code,
              'unmodified_records': len(base_stream), 'variants': []}
    status = 0 if base_stream else 2
    for name, _, line in variants[1:]:
        code, stream = results[name]
        difference = first_difference(base_stream, stream)
        report['variants'].append({'name': name, 'import': line, 'returncode': code,
                                   'records': len(stream), 'first_difference': difference})
        if code is None or base_code is None:
            status = max(status, 2)
        elif difference is not None or code != base_code:
            status = max(status, 1)
    report['verdict'] = {0: 'invariant', 1: 'import-dependent', 2: 'not-run'}[status]
    (out / 'IMPORT-INVARIANCE.json').write_text(json.dumps(report, indent=1) + '\n')
    print(json.dumps(report, indent=1))
    return status


if __name__ == '__main__':
    sys.exit(main())
