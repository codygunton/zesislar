#!/usr/bin/env python3
"""instr.py DIR... : per run dir, closed flag, instructions:u (G), zesu_block2 and Qed user s."""
import json, re, sys, pathlib


def row(d):
    log = next((x for x in d.glob('*.log') if not x.name.startswith('batch')), None); ps = d / 'perf-stat.txt'
    txt = log.read_text(errors='replace') if log else ''
    ins = None
    if ps.exists():
        for line in ps.read_text().splitlines():
            f = line.split(',')
            if len(f) > 2 and f[2].startswith('instructions') and f[0].isdigit(): ins = int(f[0]) / 1e9
    def s(w):
        m = re.findall(r'\[' + re.escape(w) + r'\] [0-9.]+ secs \(([0-9.]+)u', txt); return float(m[-1]) if m else None
    closed = ('Error' not in txt) and any(d.glob('*.vo'))
    return dict(dir=str(d), closed=closed, instr_G=round(ins, 1) if ins else None, block2=s('zesu_block2.'), qed=s('Qed.'))


if __name__ == '__main__':
    for d in map(pathlib.Path, sys.argv[1:]):
        print(json.dumps(row(d)))
