#!/usr/bin/env python3
"""mksweep.py TAG BANK CALLERDIR [BLOCK,...] : one jobs.json per sweep batch under OUT/sweep/TAG/ (fresh dirs).
Every block runs in its own guard batch (a batch shares one aggregate limit). Callers are offset-named
(PR #236: Caller<block - CALLER_BASE>.v, CALLER_BASE defaults to 6960); CALLER_BASE= (empty) reads Caller<block>.v.
Results keep the address names."""
import json, os, sys, pathlib, shutil
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import sweep_paths

LIGHT = [["6974", "69e8", "6a14"], ["697c", "69e0", "6a64", "6ab4"], ["6a6c", "6aa8", "6a08"], ["6ad8", "6a00", "69d8"],
         ["6960", "69a4", "6a38"]]
HEAVY = {"698c": 8, "69b0": 7, "6a24": 12, "6a40": 9, "6a78": 10, "6ac4": 11, "6ae0": 10, "6b08": 9}


def main(argv):
    tag, bank, cdir = argv[1], pathlib.Path(argv[2]), pathlib.Path(argv[3])
    only = set(argv[4].split(',')) if len(argv) > 4 else None
    args = json.loads((bank / 'ARGS.json').read_text())
    light = [[b] for g in LIGHT for b in g if not only or b in only]
    heavy = {b: c for b, c in HEAVY.items() if not only or b in only}
    root = sweep_paths.out_root() / 'sweep' / tag
    root.mkdir(parents=True, exist_ok=False)
    base = os.environ.get('CALLER_BASE', '6960')
    fname = (lambda b: f"Caller{int(b, 16) - int(base, 16):04x}.v") if base else (lambda b: f"Caller{b}.v")
    batches = [(b[0], b, 4, 16) for b in light] + [(b, [b], c, 24) for b, c in heavy.items()]
    for name, blocks, claim, limit in batches:
        jobs = []
        for b in blocks:
            d = root / b; d.mkdir()
            shutil.copyfile(cdir / fname(b), d / fname(b))
            jobs.append(dict(name=f"{tag}-{b}", cwd=str(d), cmd=args + [fname(b)], perf="stat"))
        (root / f"jobs-{name}.json").write_text(json.dumps(jobs, indent=1))
        print(name, claim, limit, ' '.join(blocks))


if __name__ == '__main__':
    main(sys.argv)
