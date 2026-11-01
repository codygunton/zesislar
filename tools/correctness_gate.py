#!/usr/bin/env python3
"""Reserve a measured canonical claim and run an unlocked stock gate."""

import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import uuid

from coqc_findlib import preflight
from module_memory import measurement_claim
from block.harness.code.admission_memory import projection


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


CACHE_MODES = {"uncached", "cache_enabled", "unknown"}


def measurement_provenance(history):
    """Bind declarations to existing results without changing legacy rows."""
    declarations = {}
    rows = [(row.get("target"), row.get("result_sha256")) for row in history.get("runs", [])]
    provenance = history.get("measurement_provenance", [])
    if not isinstance(provenance, list):
        raise ValueError("Measurement provenance declarations must be a list.")
    for declaration in provenance:
        if not isinstance(declaration, dict) or set(declaration) != {"target", "result_sha256", "mode", "authority"}:
            raise ValueError("A measurement provenance declaration has invalid fields.")
        sha256 = declaration["result_sha256"]
        if (not isinstance(declaration["target"], str) or declaration["target"] not in TARGETS
                or not isinstance(sha256, str)
                or len(sha256) != 64 or any(char not in "0123456789abcdef" for char in sha256)
                or not isinstance(declaration["mode"], str) or declaration["mode"] not in CACHE_MODES
                or not isinstance(declaration["authority"], str) or not declaration["authority"].strip()):
            raise ValueError("A measurement provenance declaration is invalid.")
        key = (declaration["target"], sha256)
        if key not in rows or key in declarations:
            raise ValueError("A measurement provenance declaration is unmatched or duplicated.")
        declarations[key] = declaration
    return declarations


def cache_provenance(row, declarations):
    """Unknown and cache-enabled measurements cannot size an uncached gate."""
    declared = declarations.get((row.get("target"), row.get("result_sha256")))
    recorded = row.get("cache_provenance")
    if recorded is not None:
        if (not isinstance(recorded, dict) or set(recorded) != {"mode", "authority"}
                or not isinstance(recorded["mode"], str) or recorded["mode"] not in CACHE_MODES
                or not isinstance(recorded["authority"], str) or not recorded["authority"].strip()):
            raise ValueError("A recorded cache provenance is invalid.")
        if declared and recorded["mode"] not in {"unknown", declared["mode"]}:
            raise ValueError("Recorded and declared cache provenance conflict.")
    return declared or recorded or {"mode": "unknown", "authority": "Legacy result has no cache provenance."}


def select_peak(history, target, *, claim_ceiling_bytes=0, physical_fence_bytes=120 * 1024**3, expected_identity=None):
    """Use only completed matching uncached gates for measured admission."""
    if target not in TARGETS:
        raise ValueError("The gate target is invalid.")
    if type(claim_ceiling_bytes) is not int or claim_ceiling_bytes < 0:
        raise ValueError("The declared gate claim ceiling must be a nonnegative integer.")
    declarations = measurement_provenance(history)
    rows = []
    for row in history.get("runs", []):
        if row.get("target") != target:
            continue
        provenance = cache_provenance(row, declarations)
        peak = row.get("aggregate_peak_bytes")
        if (isinstance(expected_identity, dict) and expected_identity
                and row.get("workload_identity") == expected_identity
                and provenance["mode"] == "uncached" and row.get("success") is True
                and type(row.get("exit_code")) is int and row["exit_code"] == 0
                and type(row.get("completed_ns")) is int and row["completed_ns"] > 0
                and type(peak) is int and peak > 0):
            rows.append((row, provenance))
    if rows:
        selected, provenance = max(rows, key=lambda item: item[0]["aggregate_peak_bytes"])
        return {"reason": "largest_uncached_matching_gate_peak", "measurement": selected,
                "measurement_provenance": provenance,
                "claim_bytes": measurement_claim(physical_fence_bytes, selected["aggregate_peak_bytes"],
                                                  completed=True, matching=True)}
    return {"reason": "full_physical_fence", "measurement": None,
            "claim_bytes": max(claim_ceiling_bytes, measurement_claim(physical_fence_bytes)),
            "qualification": "No completed uncached measurement binds the exact current workload identity. Reserve the full aggregate fence."}


def select_admission_basis(history, target, command, physical_fence_bytes, claim_ceiling_bytes=0):
    if type(claim_ceiling_bytes) is not int or claim_ceiling_bytes < 0:
        raise ValueError('The declared gate claim ceiling must be a nonnegative integer.')
    from gate_family import select as measured_family
    basis = measured_family(target, command, physical_fence_bytes)
    if basis is None:
        basis = select_peak(history, target, claim_ceiling_bytes=claim_ceiling_bytes,
                            physical_fence_bytes=physical_fence_bytes)
    basis['claim_bytes'] = max(claim_ceiling_bytes, basis['claim_bytes'])
    return basis


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
            record.update(projection(ledger, claims, policy["claim_bytes"], free))
            save(receipt, record)
            if record["admitted"]:
                ledger["fixed_claims"][key] = policy["claim_bytes"]
                ledger.setdefault("correctness_gate_owners", {})[key] = owner
                ledger.setdefault("claim_locations", {})[key] = {"kind": "gate", "owner": owner,
                    "output_path": str(Path(receipt).parent)}
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
        paths.update(str(path) for path in (parent / "zesuworkloads.slice").glob(
            f"zesuworkloads-aggregate{os.getuid()}p{pid}r*.slice"))
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
    index = next(i for i, item in enumerate(parts) if item.startswith(("zesuaggregate", "zesuworkloads-aggregate")) and item.endswith(".slice"))
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


def batch_fence_bytes(environment):
    """Read the guard gate route, which overrides the ordinary batch limit."""
    value = environment.get("ZESU_GATE_LIMIT", "120G")
    match = re.fullmatch(r"([1-9][0-9]*)([KMGT]?)", value)
    if not match:
        raise ValueError("The batch memory fence must use bytes or an integer K/M/G/T suffix.")
    return int(match[1]) * 1024 ** ("KMGT".index(match[2]) + 1 if match[2] else 0)


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
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        raise ValueError("The correctness gate command is absent.")
    basis = select_admission_basis(history_data, args.target, command,
                                   batch_fence_bytes(os.environ), args.claim_ceiling_bytes)
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
              "admission_wall_seconds": admission_wall, "completed_ns": time.time_ns(),
              "cache_provenance": {"mode": "unknown",
                  "authority": "The stock runner disables the proof cache but does not establish an uncached Dune build."},
              **metrics}
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
    execute.add_argument("--claim-ceiling-bytes", "--bootstrap-claim-bytes", dest="claim_ceiling_bytes", type=int,
                         default=int(os.environ.get("ZESU_GATE_CLAIM_CEILING_BYTES",
                                     os.environ.get("ZESU_GATE_BOOTSTRAP_CLAIM_BYTES", "0"))),
                         help="Explicit claim ceiling when no matching uncached measurement exists.")
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
