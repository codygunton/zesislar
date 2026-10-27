#!/usr/bin/env python3
"""Reserve a measured canonical claim and run an unlocked stock gate."""

import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import uuid

from coqc_findlib import preflight


TARGETS = {"check-fast", "check-iris"}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False) as stream:
        temporary = Path(stream.name)
        json.dump(value, stream, indent=2)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    try:
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


@contextmanager
def locked(path):
    with Path(path).open("a") as stream:
        fcntl.flock(stream, fcntl.LOCK_EX)
        yield


def read(path):
    return json.loads(Path(path).read_text())


def identity(pid):
    try:
        raw = (Path("/proc") / str(pid) / "stat").read_text()
        fields = raw[raw.rfind(")") + 2:].split()
    except FileNotFoundError:
        return None
    return {"pid": pid, "startticks": int(fields[19]), "state": fields[0]}


def alive(actor):
    current = identity(actor["pid"])
    return bool(current and current["startticks"] == actor["startticks"]
                and current["state"] not in {"Z", "X"})


def select_peak(history, target):
    """Prefer the last green matching gate; otherwise use the largest peak."""
    rows = []
    for row in history.get("runs", []):
        peak = row.get("aggregate_peak_bytes")
        if row.get("target") not in TARGETS or type(peak) is not int or peak <= 0:
            continue
        rows.append(row)
    matching = [row for row in rows if row["target"] == target and row.get("success") is True]
    if matching:
        selected = max(matching, key=lambda row: row["completed_ns"])
        reason = "previous_green_matching_gate"
    elif rows:
        selected = max(rows, key=lambda row: row["aggregate_peak_bytes"])
        reason = "largest_recorded_gate_peak"
    else:
        raise ValueError("No recorded aggregate gate peak exists. Supply a measured gate history.")
    return {"reason": reason, "measurement": selected,
            "claim_bytes": (selected["aggregate_peak_bytes"] * 3 + 1) // 2}


def active_claims(ledger):
    """Count every fixed claim and every unverified legacy reservation."""
    result = dict(ledger["fixed_claims"])
    if any(type(value) is not int or value < 0 for value in result.values()):
        raise ValueError("A canonical fixed claim is invalid.")
    for name, amount in ledger.get("region_claims", {}).items():
        if type(amount) is not int or amount < 0:
            raise ValueError("A canonical legacy claim is invalid.")
        released = ledger.get("released_region_claims", {}).get(name)
        if (released and released.get("bytes") == amount
                and digest(released["receipt"]) == released["sha256"]):
            continue
        result["legacy:" + name] = amount
    return result


def memory_available():
    fields = dict(line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines())
    return int(fields["MemAvailable"].split()[0]) * 1024


def reserve(policy, owner, receipt, *, available=memory_available, pause=time.sleep):
    while True:
        with locked(policy["lock"]):
            ledger = read(policy["ledger"])
            claims = active_claims(ledger)
            key = policy["claim_key"]
            if ledger["fixed_claims"].get(key, 0):
                raise ValueError("This canonical gate claim already exists.")
            free = available()
            record = {"owner": owner, "claim_key": key, "claim_bytes": policy["claim_bytes"],
                      "MemAvailable_bytes": free, "budget_bytes": free * 7 // 10,
                      "active_claim_bytes": sum(claims.values()), "time_ns": time.time_ns()}
            record["admitted"] = record["active_claim_bytes"] + record["claim_bytes"] <= record["budget_bytes"]
            save(receipt, record)
            if record["admitted"]:
                ledger["fixed_claims"][key] = policy["claim_bytes"]
                ledger.setdefault("correctness_gate_owners", {})[key] = owner
                ledger.setdefault("correctness_gate_admissions", {})[key] = record
                save(policy["ledger"], ledger)
                return record
        pause(60)


def aggregate_closed(batch):
    for actor in batch.get("actors", []):
        if alive(actor):
            return False
    paths = set(batch.get("aggregate_paths", []))
    parent = Path("/sys/fs/cgroup/user.slice") / f"user-{os.getuid()}.slice" / f"user@{os.getuid()}.service"
    pid = batch.get("batch_pid")
    if pid:
        paths.update(str(path) for path in parent.glob(f"zesuaggregate{os.getuid()}p{pid}r*.slice"))
    for name in paths:
        path = Path(name)
        if path.exists() and "populated 1" in (path / "cgroup.events").read_text():
            return False
    return True


def release(receipt):
    receipt = Path(receipt).resolve()
    value = read(receipt)
    policy, owner = value["policy"], value["owner"]
    out = receipt.parent
    batch = read(out / "BATCH.json") if (out / "BATCH.json").is_file() else {"actors": []}
    if (out / "BATCH-PROCESS.json").is_file():
        process = read(out / "BATCH-PROCESS.json")
        batch.setdefault("actors", []).append(process)
        batch["batch_pid"] = process["pid"]
    if not aggregate_closed(batch):
        raise ValueError("The gate actors or aggregate remain live. The claim stays assigned.")
    with locked(policy["lock"]):
        ledger = read(policy["ledger"])
        key = policy["claim_key"]
        assigned_owner = ledger.get("correctness_gate_owners", {}).get(key)
        if assigned_owner is None and key not in ledger["fixed_claims"]:
            if (out / "ADMISSION.json").is_file() and read(out / "ADMISSION.json").get("admitted"):
                raise ValueError("An admitted gate lost its canonical ownership record.")
            result = {"released": True, "never_admitted": True, "claim_key": key,
                      "bytes": 0, "owner": owner, "receipt_sha256": digest(receipt)}
            save(out / "RELEASE.json", result)
            return result
        if ledger.get("correctness_gate_owners", {}).get(key) != owner:
            raise ValueError("The canonical gate claim owner changed.")
        previous = ledger.get("correctness_gate_releases", {}).get(key)
        if ledger["fixed_claims"].get(key, 0) == 0:
            if not previous or previous["owner"] != owner or previous["receipt_sha256"] != digest(receipt):
                raise ValueError("The released gate claim lacks its exact release receipt.")
            return previous
        if ledger["fixed_claims"][key] != policy["claim_bytes"]:
            raise ValueError("The canonical gate claim amount changed.")
        closure = {"all_owned_actors_closed": True, "batch": batch, "time_ns": time.time_ns()}
        save(out / "CLOSURE.json", closure)
        result = {"released": True, "claim_key": key, "bytes": policy["claim_bytes"],
                  "owner": owner, "receipt_sha256": digest(receipt), "closure": str(out / "CLOSURE.json")}
        ledger["fixed_claims"][key] = 0
        ledger.setdefault("correctness_gate_releases", {})[key] = result
        save(policy["ledger"], ledger)
    save(out / "RELEASE.json", result)
    return result


def registry(*arguments):
    subprocess.run([sys.executable, str(Path(__file__).with_name("run_registry.py")),
                    *arguments], check=True)


def inside(out):
    request = read(out / "REQUEST.json")
    registry("register-job", "--pid", str(os.getpid()), "--startticks", str(identity(os.getpid())["startticks"]))
    group = next(line.split(":", 2)[2] for line in Path("/proc/self/cgroup").read_text().splitlines()
                 if line.startswith("0::"))
    relative = Path(group.lstrip("/"))
    parts = relative.parts
    index = next(i for i, item in enumerate(parts) if item.startswith("zesuaggregate") and item.endswith(".slice"))
    aggregate = Path("/sys/fs/cgroup").joinpath(*parts[:index + 1])
    save(out / "BATCH.json", {"actors": [identity(os.getpid())], "aggregate_paths": [str(aggregate)]})
    started = time.monotonic()
    try:
        return subprocess.run(request["command"], cwd=request["workspace"],
                              env=gate_environment(os.environ), check=False).returncode
    finally:
        cpu = dict(line.split() for line in (aggregate / "cpu.stat").read_text().splitlines())
        save(out / "METRICS.json", {"aggregate_peak_bytes": int((aggregate / "memory.peak").read_text()),
              "CPU_seconds": int(cpu["usage_usec"]) / 1e6, "aggregate_wall_seconds": time.monotonic() - started,
              "measurement_scope": "Complete owned stock aggregate before guard cleanup."})


def gate_environment(environment):
    return dict(environment, ZESU_PROOF_CACHE='off')


def run(args):
    os.environ['ZESU_PROOF_CACHE'] = 'off'
    run_started = int(os.environ.get("ZESU_GATE_STARTED_MONOTONIC_NS", time.monotonic_ns()))
    workspace = Path.cwd().resolve()
    if not os.environ.get("ZESU_RUN_ID"):
        os.environ["ZESU_GATE_STARTED_MONOTONIC_NS"] = str(run_started)
        command = [sys.executable, str(Path(__file__).with_name("run_registry.py")), "run", "--kind", "correctness-gate",
                   "--owner", os.environ.get("COORD_AGENT", "local")]
        if os.environ.get("ZESU_SUPERSEDES_RUN"):
            command += ["--supersedes", os.environ["ZESU_SUPERSEDES_RUN"]]
        os.execv(sys.executable, [*command, "--", sys.executable, str(Path(__file__).resolve()), *sys.argv[1:]])
    run_id = os.environ["ZESU_RUN_ID"]
    out = workspace / "_build/agents/correctness-gates" / run_id
    out.mkdir(parents=True, exist_ok=False)
    build = (workspace / args.build_dir).resolve()
    checked = preflight(workspace, build)
    common = Path(subprocess.check_output(["git", "rev-parse", "--path-format=absolute", "--git-common-dir"], text=True).strip())
    base = common.parent
    history = Path(os.environ.get("ZESU_GATE_PEAK_HISTORY", base / "_build/correctness-gates/HISTORY.json"))
    history_data = read(history) if history.is_file() else {"schema": "zesu.gate-measurements.v1", "runs": []}
    try:
        basis = select_peak(history_data, args.target)
    except ValueError:
        if (args.target != "check-fast" or history_data.get("runs")
                or args.bootstrap_claim_bytes != 48 * 1024**3):
            raise
        basis = {"reason": "explicit_first_measurement_bootstrap", "claim_bytes": args.bootstrap_claim_bytes,
                 "measurement": None, "qualification": "Explicit provisional reservation. This is not a measured peak."}
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        raise ValueError("The correctness gate command is absent.")
    ledger = Path(os.environ.get("ZESU_CANONICAL_LEDGER", base / "_build/agents/worker-build-2/native-region-release-v1/LEDGER.json"))
    policy = {"ledger": str(ledger), "lock": str(ledger.with_name("LEDGER.lock")),
              "claim_key": "CorrectnessGate_" + uuid.uuid4().hex, "claim_bytes": basis["claim_bytes"]}
    owner = {"pid": os.getpid(), "startticks": identity(os.getpid())["startticks"], "run_id": run_id}
    save(out / "REQUEST.json", {"policy": policy, "owner": owner, "workspace": str(workspace), "build": str(build),
          "target": args.target, "command": command, "basis": basis, "preflight": checked})
    request = out / "REQUEST.json"
    registry("register-claim", "--claim-id", policy["claim_key"], "--", sys.executable,
             str(Path(__file__).resolve()), "release", "--receipt", str(request))
    admission_started = time.monotonic()
    reserve(policy, owner, out / "ADMISSION.json")
    admission_wall = time.monotonic() - admission_started
    guard = Path(os.environ.get("ZESU_RESOURCE_GUARD", workspace / "tools/resource_guard.sh")).resolve()
    env = dict(gate_environment(os.environ), ZESU_IO="gate", ZESU_RUN_REGISTRY_TOOL=str(Path(__file__).with_name("run_registry.py")),
               ZESU_REGISTRY_PYTHON=sys.executable)
    child = subprocess.Popen([str(guard), "batch", args.target, "--", sys.executable,
                              str(Path(__file__).resolve()), "inside", str(out)], cwd=workspace, env=env)
    actor = identity(child.pid)
    if actor:
        save(out / "BATCH-PROCESS.json", actor)
    status = child.wait()
    metrics = read(out / "METRICS.json") if (out / "METRICS.json").exists() else {}
    result = {"target": args.target, "success": status == 0, "exit_code": status,
              "wall_seconds": (time.monotonic_ns() - run_started) / 1e9,
              "admission_wall_seconds": admission_wall, "completed_ns": time.time_ns(), **metrics}
    save(out / "RESULT.json", result)
    if metrics.get("aggregate_peak_bytes"):
        history.parent.mkdir(parents=True, exist_ok=True)
        with locked(history.with_suffix(".lock")):
            records = read(history) if history.is_file() else {"schema": "zesu.gate-measurements.v1", "runs": []}
            records.setdefault("runs", []).append({**result, "result_path": str(out / "RESULT.json"),
                                                   "result_sha256": digest(out / "RESULT.json")})
            save(history, records)
    release(request)
    registry("claim-released", "--claim-id", policy["claim_key"])
    print(json.dumps({"result": str(out / "RESULT.json"), **result}))
    return status


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="action", required=True)
    execute = commands.add_parser("run")
    execute.add_argument("--target", choices=sorted(TARGETS), required=True)
    execute.add_argument("--build-dir", type=Path, required=True)
    execute.add_argument("--bootstrap-claim-bytes", type=int,
                         default=int(os.environ.get("ZESU_GATE_BOOTSTRAP_CLAIM_BYTES", "0")))
    execute.add_argument("command", nargs=argparse.REMAINDER)
    close = commands.add_parser("release")
    close.add_argument("--receipt", type=Path, required=True)
    nested = commands.add_parser("inside")
    nested.add_argument("output", type=Path)
    args = parser.parse_args()
    try:
        if args.action == "release":
            release(args.receipt)
            return 0
        return inside(args.output) if args.action == "inside" else run(args)
    except (ValueError, OSError) as error:
        if args.action == "run" and os.environ.get("ZESU_RUN_ID"):
            out = Path.cwd() / "_build/agents/correctness-gates" / os.environ["ZESU_RUN_ID"]
            out.mkdir(parents=True, exist_ok=True)
            save(out / "RESULT.json", {"target": args.target, "success": False,
                  "status": "setup_failed", "error": str(error), "admission_completed":
                  (out / "ADMISSION.json").is_file() and read(out / "ADMISSION.json").get("admitted", False)})
            if not (out / "REQUEST.json").is_file():
                save(out / "RELEASE.json", {"released": True, "never_admitted": True, "bytes": 0})
        parser.exit(2, f"correctness gate setup: {error}\n")


if __name__ == "__main__":
    raise SystemExit(main())
