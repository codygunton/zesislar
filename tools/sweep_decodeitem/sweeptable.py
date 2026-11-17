#!/usr/bin/env python3
"""sweeptable.py MAINTAG BRANCHTAG : markdown table of instructions:u per block, both sides, closed flags.
A side may join tags with '+' (a closed run wins). Tags live under OUT/sweep/ (see sweep_paths.py)."""
import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import instr
import sweep_paths


def side1(tag):
    dirs = sorted(d for d in (sweep_paths.out_root() / 'sweep' / tag).iterdir() if d.is_dir())
    return {d.name: instr.row(d) for d in dirs}


def side(tags):
    rows = {}
    for tag in tags.split('+'):
        for k, r in side1(tag).items():
            if r.get('closed') or k not in rows: rows[k] = r
    return rows


def main(argv):
    m, b = side(argv[1]), side(argv[2])
    print("| block | main G | branch G | change | main | branch |")
    print("|---|---:|---:|---:|---|---|")
    tm = tb = 0
    for k in sorted(set(m) | set(b)):
        x, y = m.get(k, {}), b.get(k, {})
        xi, yi = x.get('instr_G'), y.get('instr_G')
        tm += xi or 0; tb += yi or 0
        ch = f"{100 * (yi - xi) / xi:+.1f}%" if xi and yi else "n/a"
        print(f"| {k} | {xi} | {yi} | {ch} | {'closed' if x.get('closed') else 'OPEN'} | {'closed' if y.get('closed') else 'OPEN'} |")
    print(f"| total | {tm:.1f} | {tb:.1f} | {100 * (tb - tm) / tm:+.2f}% | {sum(v['closed'] for v in m.values())}/{len(m)} | {sum(v['closed'] for v in b.values())}/{len(b)} |")


if __name__ == '__main__':
    main(sys.argv)
