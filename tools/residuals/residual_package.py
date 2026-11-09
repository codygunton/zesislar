"""Turn a residual-mode census log into goal dirs and a manifest (diagnostic only).

A candidate is a pure goal where the selected-facts solver did not close it:
either a pure goal left open after the residual pass (RES-TRY open), or an
outermost failed `Lia.lia` / `tactics.bv_solve` call dumped during the proof
(FAIL-BEGIN ... FAIL-END). Candidates with the same selected statement merge.
Goal ids are `<block>-<n>` in log order over all unique candidates, so the id
list depends only on the log. Every candidate keeps its goal dir; the whole-context
control only marks it `true` (control passed) or `unknown` (control did not pass).
This module writes no proof for a goal; the control is a fixed solver call."""
from pathlib import Path
import hashlib
import json
import re
import shutil

SLOT = '(* PROOF-SLOT: replace this line and the Admitted below with the proof script and Qed. *)'
CONTROL_TACTIC = '''Proof.
  intros.
  first [ LinearFirstLia.zesu_lia_linear_first3
        | bv_simplify_arith; bv_saturate_unsigned;
          unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, bv_unsigned in *;
          simpl; LinearFirstLia.zesu_lia_linear_first3 ].
Qed.
'''
CONTROL_TEXT = ('control: whole-context library solver (LinearFirstLia.zesu_lia_linear_first3, then the stdpp '
                'bv_solve unfolding with it) on goal_full.v, same bank')
LINE = re.compile(r'^(\d+\.\d+) (.*)$')
HYP = re.compile(r'RES-HYP (\S+) d=(\d) prop=(\d) n=(\d+) v=(.*?) ::$')
CONCL = re.compile(r'RES-CONCL n=(\d+) v=(.*?) ::$')
DUMP_LAYERS = ('Lia.lia', 'tactics.bv_solve')
SPATIAL_HEADER = 'block\tn\tkind\treason\tgoal_head\n'


def _census_lines(log):
    for raw in Path(log).read_text(errors='replace').splitlines():
        m = LINE.match(raw)
        if m and m.group(2).startswith('CENSUS '):
            yield m.group(2)[7:]


def _goal_line(cur, body):
    """Add one RES-HYP/RES-TYPE/RES-BODY/RES-CONCL/RES-TEXT line to goal dump CUR."""
    if body.startswith('RES-HYP '):
        hm = HYP.match(body)
        cur['hyps'].append(dict(id=hm.group(1), d=hm.group(2) == '1', prop=hm.group(3) == '1',
                                n=int(hm.group(4)), vars=hm.group(5).split(), type=None, body=None))
    elif body.startswith('RES-TYPE '):
        cur['hyps'][-1]['type'] = body[9:]
    elif body.startswith('RES-BODY '):
        cur['hyps'][-1]['body'] = body[9:]
    elif body.startswith('RES-CONCL '):
        cm = CONCL.match(body)
        cur['concl'] = dict(n=int(cm.group(1)), vars=cm.group(2).split(), text=None)
    elif body.startswith('RES-TEXT '):
        cur['concl']['text'] = body[9:]


def parse_residual(log):
    """The residual pass: try results, and the readable and robust dumps of each open goal."""
    tries, passes, cur, infail = [], {'readable': [], 'robust': []}, None, False
    for body in _census_lines(log):
        if body.startswith('FAIL-BEGIN '):
            infail = True
        elif body.startswith('FAIL-END'):
            infail = False
        elif infail:
            continue
        elif body.startswith('RES-TRY '):
            tries.append(body.split('reason=')[1].strip() if 'reason=' in body else 'solved')
        elif body.startswith('RES-BEGIN '):
            kv = dict(x.split('=', 1) for x in body.split()[1:])
            cur = dict(kind=kv['kind'], hyps=[], concl=None)
            passes[kv['pass']].append(cur)
        elif cur is not None:
            _goal_line(cur, body)
    opened = [t for t in tries if t != 'solved']
    if not (len(opened) == len(passes['readable']) == len(passes['robust'])):
        raise ValueError('pass mismatch: %d open, %d readable, %d robust' % (
            len(opened), len(passes['readable']), len(passes['robust'])))
    return tries, opened, passes


def parse_fail_dumps(log):
    """Outermost failure dumps: a dump whose layer runs inside another open dump-layer
    call is skipped; that outer call dumps its own goal if it fails too."""
    dumps, stack, cur = [], [], None
    for body in _census_lines(log):
        if cur is not None:
            if body.startswith('FAIL-END'):
                if not any(f in DUMP_LAYERS for f in stack):
                    dumps.append(cur)
                cur = None
            else:
                _goal_line(cur, body)
            continue
        if body.startswith('B '):
            stack.append(body.split()[1])
        elif body.startswith('E '):
            layer = body.split()[1]
            for k in range(len(stack) - 1, -1, -1):
                if stack[k] == layer:
                    del stack[k:]
                    break
        elif body.startswith('FAIL-BEGIN '):
            cur = dict(kind='pure', layer=body.split()[1], hyps=[], concl=None)
    return dumps


def entry_vars(caller_src, bank):
    names = {'args', 'returnAddress'}
    for mod in sorted(set(re.findall(r'ZesuSsz\.Generated\.[\w.]+Entries', caller_src))):
        f = Path(bank) / (mod.replace('.', '/') + '.v')
        if f.exists():
            for m in re.finditer(r'∃((?:\s*\([\w\' ]+ : [^()]+\))+)\s*,', f.read_text()):
                names |= set(re.findall(r'\(([\w\']+) :', m.group(1)))
    return names


def select(rob, limit, evars):
    """Facts that share a variable with the goal (two steps), facts above LIMIT nodes
    dropped, facts only about entry variables, and the binders they need."""
    hyps = rob['hyps']
    index = {h['id']: i for i, h in enumerate(hyps)}
    facts = [i for i, h in enumerate(hyps) if h['prop'] and not h['d'] and h['n'] <= limit and h['type']]
    mark, scope = {}, set(rob['concl']['vars'])
    for _ in range(2):
        new = [i for i in facts if i not in mark and set(hyps[i]['vars']) & scope]
        for i in new:
            mark[i] = 'selected'
            scope |= set(hyps[i]['vars'])
    for i in facts:
        vs = set(hyps[i]['vars'])
        if i not in mark and vs and vs <= evars:
            mark[i] = 'entry'
    need = set(rob['concl']['vars'])
    for i in mark:
        need |= set(hyps[i]['vars'])
    while True:
        extra = set()
        for v in need:
            if v in index:
                extra |= set(hyps[index[v]]['vars']) - need
        if not extra:
            break
        need |= extra
    keep = sorted(set(index[v] for v in need if v in index) | set(mark))
    return keep, mark


def statement(name, hyps, keep, concl_text):
    parts, group = [], []

    def flush():
        if group:
            parts.append('forall ' + ' '.join(group) + ',')
            group.clear()
    for i in keep:
        h = hyps[i]
        if h['d'] and h['body'] is not None:
            flush()
            parts.append('let %s : %s := %s in' % (h['id'], h['type'], h['body']))
        else:
            group.append('(%s : %s)' % (h['id'], h['type']))
    flush()
    return 'Lemma %s :\n  %s\n  %s.\n' % (name, '\n  '.join(parts), concl_text)


def prefix_of(caller_src):
    m = re.search(r'^(Lemma|Theorem) ', caller_src, re.M)
    return caller_src[:m.start()].rstrip() + '\n'


def candidates(log, block, fact_limit, evars):
    """Return (tries, spatial rows, unique candidates). Each candidate carries its
    goal id, statement digest, source, copy count, and selection."""
    tries, opened, passes = parse_residual(log)
    spatial, cands = [], []
    for k, (reason, read, rob) in enumerate(zip(opened, passes['readable'], passes['robust'])):
        if rob['kind'] != 'pure':
            head = ' '.join((read['concl']['text'] or '').split())[:200].replace('\t', ' ')
            spatial.append(dict(block=block, n=k, kind=rob['kind'], reason=reason, goal_head=head))
        else:
            cands.append(dict(source='left open at the end (%s)' % reason, dump=rob))
    for dmp in parse_fail_dumps(log):
        if dmp['concl'] and dmp['concl']['text']:
            cands.append(dict(source='failed %s call during the proof' % dmp['layer'], dump=dmp))
    seen, uniq = {}, []
    for c in cands:
        keep, mark = select(c['dump'], fact_limit, evars)
        body = statement('X', c['dump']['hyps'], keep, c['dump']['concl']['text']).split(':', 1)[1]
        digest = hashlib.sha256(body.encode()).hexdigest()[:16]
        if digest in seen:
            seen[digest]['copies'] += 1
            continue
        c.update(keep=keep, mark=mark, sha=digest, copies=1, id='%s-%d' % (block, len(uniq) + 1))
        seen[digest] = c
        uniq.append(c)
    return tries, spatial, uniq


def stage_files(c, block, prefix, d):
    """Write goal.v, goal_full.v, control.v and render.v of candidate C into D."""
    rob = c['dump']
    name = 'residual_%s_%s' % (block, c['sha'])
    stmt = statement(name, rob['hyps'], c['keep'], rob['concl']['text'])
    full_keep = [i for i, h in enumerate(rob['hyps']) if h['type'] is not None]
    full = statement(name + '_full', rob['hyps'], full_keep, rob['concl']['text'])
    d.mkdir(parents=True, exist_ok=True)
    (d / 'goal.v').write_text(prefix + '\n' + stmt + 'Proof.\n' + SLOT + '\nAdmitted.\n')
    (d / 'goal_full.v').write_text(prefix + '\n' + full + 'Proof.\n' + SLOT + '\nAdmitted.\n')
    (d / 'control.v').write_text(prefix + '\n' + full + CONTROL_TACTIC)
    (d / 'render.v').write_text(prefix + '\n' + stmt + 'Admitted.\nSet Printing Width 160.\nCheck %s.\n' % name)
    return name


CHECK_SH = r'''#!/bin/bash
# Compile proof.v (goal.v with the slot filled) against the bank, read-only.
# Prints PASS or FAIL only; the compiler output goes to check.log.
cd "$(dirname "$0")" || exit 2
[ -f proof.v ] || { echo FAIL; exit 1; }
python3 -I - <<'PY' || { echo "statement or token check failed" > check.log; echo FAIL; exit 1; }
import re, sys
goal, proof = open('goal.v').read(), open('proof.v').read()
head = goal[:goal.index('(* PROOF-SLOT')]
if not proof.startswith(head):
    sys.exit(1)
rest = proof[len(head):]
if re.search(r'\b(Admitted|admit|Axiom|Abort|timeout|Timeout|give_up|Parameter)\b', rest):
    sys.exit(1)
if rest.count('Qed.') != 1 or not rest.rstrip().endswith('Qed.'):
    sys.exit(1)
PY
export PATH=@PATH@ OCAMLPATH=@OCAMLPATH@
export ZESU_MODULE_LIMIT_GIB=16 ZESU_GATE_MODULE_LIMIT_GIB=16 ZESU_BATCH_LIMIT=200G ZESU_PROOF_CPU_LIMIT=unlimited ZESU_SCOPE_CPU=unlimited
rm -f .lia.cache .nia.cache
# One guard scope under its own writer identity; book 1 GiB (measured peak 0.78 GiB).
ZESU_WRITER_ID=residual-@ID@ ZESU_MODULE_CLAIM_BYTES=1073741824 \
  @GUARD@ scope residual-check-@ID@ -- timeout 600 @COQC@ proof.v > check.log 2>&1
rc=$?
rm -f proof.vo proof.vok proof.vos proof.glob .proof.aux .lia.cache .nia.cache
if [ $rc -eq 0 ]; then echo PASS; else echo FAIL; exit 1; fi
'''


def _q(x):
    return "'%s'" % x.replace("'", "'\\''")


def check_sh(gid, args, guard, path_env, ocamlpath):
    return (CHECK_SH.replace('@ID@', gid).replace('@COQC@', ' '.join(_q(x) for x in args))
            .replace('@GUARD@', _q(guard)).replace('@PATH@', _q(path_env)).replace('@OCAMLPATH@', _q(ocamlpath)))


def truth_of(control_status):
    return 'true' if control_status == 'pass' else 'unknown'


def readable_statement(render_log, name):
    log = Path(render_log).read_text(errors='replace') if Path(render_log).exists() else ''
    readable = log[log.rfind(name):] if name in log else ''
    return '\n'.join(l for l in readable.splitlines() if not l.startswith(('Warning', 'Cannot open', '[')))


def write_goal_dir(out, c, block, stage, result, args, guard, path_env, fact_limit, ocamlpath):
    """Copy the staged goal of candidate C into OUT/<id>/ with check.sh, FACTS.md, CONTROL."""
    rob, gid = c['dump'], c['id']
    d = out / gid
    d.mkdir()
    for fn in ('goal.v', 'goal_full.v'):
        shutil.copyfile(stage / fn, d / fn)
    (d / 'check.sh').write_text(check_sh(gid, args, guard, path_env, ocamlpath))
    (d / 'check.sh').chmod(0o755)
    name = 'residual_%s_%s' % (block, c['sha'])
    facts = [i for i in c['keep'] if rob['hyps'][i]['prop']]
    props = sum(1 for h in rob['hyps'] if h['prop'])
    truth = truth_of(result['control']['status'])
    note = ('' if truth == 'true' else
            '\nControl: the whole-context control did not pass (%s), so this goal may be false.\n'
            % result['control']['status'])
    (d / 'FACTS.md').write_text(
        '# %s\n\nSource: block %s, %s; seen %d time(s). Selected %d of %d hypotheses '
        '(%d Props in the full context): facts that share a variable with the goal (two steps), '
        'facts above %d term nodes dropped, plus facts only about the entry variables.\n%s\n'
        'Selected facts: %s\n\n## Statement (readable)\n\n```\n%s\n```\n' % (
            gid, block, c['source'], c['copies'], len(c['keep']), len(rob['hyps']), props, fact_limit, note,
            ', '.join('%s (%s)' % (rob['hyps'][i]['id'], c['mark'].get(i, 'dependency')) for i in facts) or 'none',
            readable_statement(stage / 'render.log', name).strip()))
    (d / 'CONTROL').write_text('%s\nresult: %s\ntruth: %s\nseconds: %s\n' % (
        CONTROL_TEXT, result['control']['status'].upper(), truth, result['control']['seconds']))
    return d


def goal_record(c, result):
    rob = c['dump']
    return dict(id=c['id'], sha=c['sha'], source=c['source'], copies=c['copies'], hyps=len(rob['hyps']),
                props=sum(1 for h in rob['hyps'] if h['prop']), selected=len(c['keep']),
                goal_reparses=result['goal']['status'] == 'pass',
                control=result['control']['status'], truth=truth_of(result['control']['status']),
                control_seconds=result['control']['seconds'], goal_seconds=result['goal']['seconds'])


def write_spatial(out, spatial):
    rows = ''.join('%s\t%d\t%s\t%s\t%s\n' % (r['block'], r['n'], r['kind'], r['reason'], r['goal_head'])
                   for r in spatial)
    (out / 'spatial.tsv').write_text(SPATIAL_HEADER + rows)


TIMING_KEYS = ('run_times', 'control_seconds', 'goal_seconds', 'started_utc', 'finished_utc')


def signature(manifest):
    """The manifest without run times: two runs of one bank and block must agree on it."""
    def strip(x):
        if isinstance(x, dict):
            return {k: strip(v) for k, v in x.items() if k not in TIMING_KEYS}
        if isinstance(x, list):
            return [strip(v) for v in x]
        return x
    return strip(manifest)


def compare(a, b):
    """Return the list of differences between two manifests' signatures (empty when equal)."""
    sa, sb = signature(a), signature(b)
    diffs = []
    for k in sorted(set(sa) | set(sb)):
        if k in ('out', 'ocamlpath'):
            continue
        if sa.get(k) != sb.get(k):
            diffs.append(k)
    return diffs
