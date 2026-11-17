#!/usr/bin/env python3
"""runjobs.py JOBS.json : run each job {name, cwd, cmd} in its own guard scope (this checkout's guard), in parallel;
append rows to <jobs dir>/results.jsonl. A job directory must be fresh (no solver caches); nothing is deleted."""
import json, os, subprocess, sys, time
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, str(Path(__file__).resolve().parent))
import sweep_paths


def run(j, out, guard):
    d = Path(j['cwd']); d.mkdir(parents=True, exist_ok=True)
    if list(d.glob('.*.cache')) + list(d.glob('*.cache')):
        raise SystemExit(f"{d} holds solver caches; use a fresh directory")
    t0 = time.monotonic()
    with (d / f"{j['name']}.log").open('w') as f:
        perf = ['perf', 'stat', '-x,', '-e', 'instructions:u', '-o', str(d / 'perf-stat.txt'), '--'] if j.get('perf') == 'stat' else []
        p = subprocess.Popen([str(guard), 'scope', f"mq-{j['name']}", '--'] + perf + j['cmd'], cwd=d, stdout=f, stderr=subprocess.STDOUT)
        _, st, ru = os.wait4(p.pid, 0)
    row = dict(name=j['name'], rc=os.waitstatus_to_exitcode(st), wall_s=round(time.monotonic() - t0, 1),
               user_s=round(ru.ru_utime, 1), max_rss_gib=round(ru.ru_maxrss / 2**20, 2))
    with out.open('a') as f: f.write(json.dumps(row) + '\n')
    print(json.dumps(row), flush=True); return row


def main(argv):
    jobs_file = Path(argv[1]).resolve(); jobs = json.loads(jobs_file.read_text())
    out, guard = jobs_file.parent / 'results.jsonl', sweep_paths.guard()
    with ThreadPoolExecutor(max_workers=len(jobs)) as pool: rows = list(pool.map(lambda j: run(j, out, guard), jobs))
    print('DONE', sum(r['rc'] == 0 for r in rows), 'of', len(rows), flush=True)


if __name__ == '__main__':
    main(sys.argv)
