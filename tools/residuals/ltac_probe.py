"""Read the live Ltac bodies of a caller's import context, then keep the faithful ones.

probe(): print every Ltac in the caller context (Probe1: signatures, Probe2: bodies,
Locate: full paths). Writes ltacs.json and fullnames.json, the census_gen inputs.
verify(): generate the census file in verify mode, compile it, and exclude each
wrapped name whose copied body fails to parse or prints differently from the
original. Writes exclude.txt and verify.json.

Both steps start from an empty directory and use no earlier probe as a seed, so
the same bank and caller give the same result."""
from pathlib import Path
import json
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import census_gen  # noqa: E402
import guarded  # noqa: E402
import ltac_bodies  # noqa: E402

SHADOW = ('Module CensusShadow. Ltac lia := idtac. Ltac nia := idtac. Ltac bv_solve := idtac. '
          'End CensusShadow.\nImport CensusShadow.\n')


def _run(out, name, text, args, tag):
    v = out / (name + '.v')
    v.write_text(text)
    res = guarded.compile_file(v, '%s-%s' % (tag, name.lower()), args, limit_s=600, stamp=True)
    text = v.with_suffix('.log').read_text(errors='replace')
    if res['status'] in ('error', 'timeout'):
        raise SystemExit('probe: %s.v ended with %s (rc %d); see %s' % (name, res['status'], res['returncode'],
                                                                         v.with_suffix('.log')))
    return text, res


def error_at(text, filename):
    """(line, message) of the first error in FILENAME, or None. A `File ...` line
    counts only when the next line starts the error; warnings also name lines."""
    lines = body_lines(text)
    pat = re.compile(r'^File "\./%s", line (\d+), characters \d+-\d+:$' % re.escape(filename))
    for i, l in enumerate(lines[:-1]):
        m = pat.match(l)
        if m and lines[i + 1].startswith('Error'):
            msg = ' '.join(x.strip() for x in lines[i + 1:i + 4])
            return int(m.group(1)), msg
    return None


def body_lines(text):
    return [l.split(' ', 1)[1] if ' ' in l else '' for l in text.splitlines()]


def signature_names(log1):
    lines = body_lines(log1)
    start = max(i for i, l in enumerate(lines) if l.startswith('Ltac Coq.micromega.Lia.lia'))
    j = start + 1
    while j < len(lines) and (lines[j].startswith(' ') or lines[j] in ('', 'Hooks') or lines[j].startswith('Redefined')):
        j += 1
    names = []
    for l in lines[j:]:
        if l.strip() and not l.startswith(' ') and not l.startswith('File ') and not l.startswith('Warning'):
            n = l.split()[0]
            if n not in ('lia', 'nia', 'bv_solve') and n not in names:
                names.append(n)
    return names


def probe(caller, out, args, tag):
    caller, out = Path(caller), Path(out)
    out.mkdir(parents=True, exist_ok=True)
    src = caller.read_text()
    header = src[:re.search(r'^(Definition|Lemma|Theorem) ', src, re.M).start()].rstrip() + '\n'
    compiles = 0
    log1, res1 = _run(out, 'Probe1', header + SHADOW + 'Print Ltac Coq.micromega.Lia.lia.\nPrint Ltac Signatures.\n',
                   args, tag)
    compiles += 1
    if res1['status'] != 'pass':
        raise SystemExit('probe: Probe1.v failed; see %s' % (out / 'Probe1.log'))
    names = signature_names(log1)
    dropped = []
    # Drop names that do not resolve (wrapped signature lines), one compile per bad name.
    for _ in range(400):
        log2, res2 = _run(out, 'Probe2', header + SHADOW + ''.join('Print Ltac %s.\n' % n for n in names), args, tag)
        compiles += 1
        err = error_at(log2, 'Probe2.v')
        if err is None:
            if res2['status'] != 'pass':
                raise SystemExit('probe: Probe2.v failed outside a name; see %s' % (out / 'Probe2.log'))
            break
        bad = err[0] - (header + SHADOW).count('\n') - 1
        if not 0 <= bad < len(names):
            raise SystemExit('probe: Probe2.v error outside the name list: %s' % err[1])
        dropped.append(names.pop(bad))
        print('probe: drop %s (%s)' % (dropped[-1], err[1][:80]), flush=True)
    else:
        raise SystemExit('probe: Probe2 still fails after 400 drops')
    bodies = ltac_bodies.parse(out / 'Probe2.log')
    bodies.update(ltac_bodies.parse(out / 'Probe1.log'))
    users = {}
    for name, body in bodies.items():
        toks = sorted(set(ltac_bodies.TOK.findall(body.split(':=', 1)[1] if ':=' in body else body)))
        if toks:
            users[name] = toks
    (out / 'ltacs.json').write_text(json.dumps({'bodies': bodies, 'users': users}, indent=1, sort_keys=True))
    want = sorted(users) + [n for n in ('PureFacts.zesu_saturate_derived_facts', 'zesu_branch_guard_derived_facts')
                            if n in bodies]
    log3, res3 = _run(out, 'Locate', header + ''.join('Locate Ltac %s.\n' % n for n in want), args, tag)
    if res3['status'] != 'pass':
        raise SystemExit('probe: Locate.v failed; see %s' % (out / 'Locate.log'))
    compiles += 1
    ents = []
    for l in body_lines(log3):
        if l.startswith('Ltac'):
            ents.append(l[4:].strip())
        elif l.startswith('  ') and ents:
            ents[-1] = (ents[-1] + ' ' + l.strip()).strip()
    full, i = {}, 0
    for n in want:
        got = None
        while i < len(ents):
            e = ents[i]
            p = e.split()[0]
            mm = re.search(r'is (\S+)\)', e)
            if not (p == n or p.endswith('.' + n)):
                break
            if (mm and mm.group(1) == n) or not mm:
                got = got or p
            i += 1
        full[n] = got
    (out / 'fullnames.json').write_text(json.dumps(full, indent=1, sort_keys=True))
    return dict(names=len(names), dropped=len(dropped), bodies=len(bodies), solver_users=len(users),
                located=sum(1 for v in full.values() if v), compiles=compiles)


def _body_of(record):
    lines = record.split('\n')
    first = re.sub(r'^Ltac \S+((?: [\w\']+)*) :=', r'ARGS\1 :=', lines[0])
    rest = []
    for line in lines[1:]:
        if line.startswith('Redefined by:'):
            break
        rest.append(line)
    return ' '.join(' '.join([first] + rest).split())


def verify(caller, probe_dir, work, args, tag):
    caller, probe_dir, work = Path(caller), Path(probe_dir), Path(work)
    work.mkdir(parents=True, exist_ok=True)
    stem = 'Verify' + re.sub(r'\W', '', caller.stem)
    vfile, log = work / (stem + '.v'), work / (stem + '.log')
    excluded, reasons, compiles = [], {}, 0
    for _ in range(200):
        census_gen.main([str(caller), str(vfile), '--mode', 'verify', '--ltacs', str(probe_dir / 'ltacs.json'),
                         '--fullnames', str(probe_dir / 'fullnames.json'), '--exclude', ','.join(excluded)])
        res = guarded.compile_file(vfile, '%s-verify' % tag, args, limit_s=600, stamp=True)
        compiles += 1
        text = log.read_text(errors='replace')
        err = error_at(text, stem + '.v')
        if err is None:
            if res['status'] != 'pass':
                raise SystemExit('verify: %s.v ended with %s (rc %d); see %s' % (
                    stem, res['status'], res['returncode'], log))
            break
        line = err[0]
        src = vfile.read_text().splitlines()
        name = None
        for i in range(line - 1, -1, -1):
            d = re.match(r'Ltac (census_\S+)_body', src[i])
            if d:
                name = d.group(1)
                break
        wrapped = json.loads(Path(str(vfile) + '.wrapped.json').read_text())
        real = [w['name'] for w in wrapped if 'census_' + re.sub(r'\W', '_', w['name']) == name]
        if not real:
            raise SystemExit('verify: error outside a body at line %d: %s' % (line, err[1]))
        excluded.append(real[0])
        reasons[real[0]] = 'parse: ' + err[1][:300]
        print('verify: exclude %s (%s)' % (real[0], err[1][:80]), flush=True)
    else:
        raise SystemExit('verify: the verify file still fails after 200 exclusions')
    orig = ltac_bodies.parse(probe_dir / 'Probe2.log')
    orig.update(ltac_bodies.parse(probe_dir / 'Probe1.log'))
    printed = ltac_bodies.parse(log)
    wrapped = json.loads(Path(str(vfile) + '.wrapped.json').read_text())
    ok = 0
    for w in wrapped:
        key = [k for k in printed if k.endswith(re.sub(r'\W', '_', 'census_' + w['name']) + '_body')]
        o = orig.get(w['name'])
        if not key or o is None:
            excluded.append(w['name'])
            reasons[w['name']] = 'not printed'
            continue
        if _body_of(printed[key[0]]) != _body_of(o):
            excluded.append(w['name'])
            reasons[w['name']] = 'mismatch'
            continue
        ok += 1
    (work / 'exclude.txt').write_text(','.join(excluded))
    (work / 'verify.json').write_text(json.dumps(dict(faithful=ok, excluded=reasons), indent=1, sort_keys=True))
    return dict(faithful=ok, excluded=len(excluded), compiles=compiles), excluded
