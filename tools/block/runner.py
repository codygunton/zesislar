"""Run a compiler probe in a guarded 8 GiB systemd scope."""
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from coqc_recipe import remember_recipe


def compiler_stats(root):
    pending, seen = [str(root)], set()
    cpu, rss = 0.0, 0
    while pending:
        pid = pending.pop()
        if pid in seen:
            continue
        seen.add(pid)
        try:
            proc = Path("/proc") / pid
            pending.extend((proc / "task" / pid / "children").read_text().split())
            if "coqc" not in (proc / "comm").read_text():
                continue
            fields = (proc / "stat").read_text().rsplit(")", 1)[1].split()
            cpu += (int(fields[11]) + int(fields[12])) / os.sysconf("SC_CLK_TCK")
            rss += int(fields[21]) * os.sysconf("SC_PAGE_SIZE") / 1048576
        except (OSError, ValueError):
            continue
    return cpu, rss


def run(source, build_dir, cap):
    recipe = remember_recipe(build_dir)
    if not recipe:
        raise RuntimeError("The build directory has no compiler recipe.")
    flags, skip = [], False
    for arg in recipe["command"][1:]:
        if skip:
            skip = False
        elif arg == "-o":
            skip = True
        elif not arg.endswith(".v"):
            flags.append(arg)
    env = os.environ.copy()
    for key in ("ARISTOTLE_API_KEY", "OPEN_ROUTER_API_KEY", "PROVER_API_KEY", "ZESU_WRITER_ID"):
        env.pop(key, None)
    env["ZESU_MODULE_LIMIT_GIB"] = "8"
    started = time.monotonic()
    samples, cpu, peak, limit = [], 0.0, 0.0, None
    compiler_started = None
    with tempfile.TemporaryDirectory(prefix="block-run-") as tmp, source.with_suffix(".out").open("w") as log:
        command = [str(ROOT / "tools/resource_guard.sh"), "scope", "worker-build-2-block", "--cpu", str(cap + 30), "--",
                   recipe["command"][0], *flags, "-o", str(Path(tmp) / (source.stem + ".vo")), str(source.resolve())]
        process = subprocess.Popen(command, cwd=recipe["working_dir"], env=env, stdout=log, stderr=subprocess.STDOUT)
        try:
            while process.poll() is None:
                current_cpu, rss = compiler_stats(process.pid)
                cpu, peak = max(cpu, current_cpu), max(peak, rss)
                if compiler_started is None and (current_cpu or rss):
                    compiler_started = time.monotonic()
                elapsed = time.monotonic() - (compiler_started or started)
                samples.append([round(elapsed, 1), round(rss)])
                if compiler_started is not None and rss and elapsed >= cap:
                    limit = "time"
                    process.terminate()
                    break
                time.sleep(1)
            try:
                rc = process.wait(timeout=20)
            except subprocess.TimeoutExpired:
                process.kill()
                rc = process.wait()
        finally:
            if process.poll() is None:
                process.terminate()
                process.wait()
    if rc in (152, -24):
        limit = "time"
    return dict(rc=rc, wall=round(time.monotonic()-(compiler_started or started), 1),
                wait=round((compiler_started or started)-started, 1), cpu=round(cpu, 1),
                peak_mib=round(peak), limit=limit, rss_samples=samples)
