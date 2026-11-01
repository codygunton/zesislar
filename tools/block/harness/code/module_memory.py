"""Estimate compiler reservations from retained module measurements.

These estimates are admission weights, not physical memory limits. Callers
must keep the existing compiler fences and serialize reservation changes.
"""

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import shlex
import tempfile

_directory = Path(__file__).resolve().parent
_staged_tools = _directory.parent if _directory.name == 'block' else None
if _staged_tools is not None:
    _slots = _staged_tools / 'det/coqc_slots.py'
    if (_staged_tools.name != 'tools' or not _slots.is_file()
            or not _slots.resolve().is_relative_to(_staged_tools.resolve())):
        raise ImportError('The staged module memory helper lacks its owned det dependency.')
    _spec = importlib.util.spec_from_file_location('_zesu_owned_coqc_slots', _slots)
    _module = importlib.util.module_from_spec(_spec)
    _spec.loader.exec_module(_module)
    compiler_pids = _module.compiler_pids
else:
    try:
        from .det.coqc_slots import compiler_pids
    except ImportError:
        from det.coqc_slots import compiler_pids


if _staged_tools is not None:
    _admission = _directory / 'admission_memory.py'
    if not _admission.is_file() or not _admission.resolve().is_relative_to(_staged_tools.resolve()):
        raise ImportError('The staged module memory helper lacks its owned admission dependency.')
    _spec = importlib.util.spec_from_file_location('_zesu_owned_admission_memory', _admission)
    _module = importlib.util.module_from_spec(_spec)
    _spec.loader.exec_module(_module)
    evaluate, ScopeReader = _module.evaluate, _module.ScopeReader
    confirm_shell, release_shell = _module.confirm_shell, _module.release_shell
    current_projection = _module.current_projection
    mark_shell = _module.mark_shell
    refresh_shell_growth = _module.refresh_shell_growth
    check_test_ledger = _module.check_test_ledger
    read_shell_bookings = _module.read_shell_bookings
    select_guard_aggregate_limit = _module.select_guard_aggregate_limit
else:
    from admission_memory import evaluate, ScopeReader, confirm_shell, release_shell, current_projection, mark_shell, refresh_shell_growth, check_test_ledger, read_shell_bookings, select_guard_aggregate_limit

GIB = 1024 ** 3
SCHEMA = "zesu.module-memory.v1"


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def positive_integer(value, label):
    if type(value) is not int or value <= 0:
        raise ValueError(f"The {label} must be a positive integer.")
    return value


def measurement_claim(fence_bytes, peak_bytes=None, *, completed=False, matching=False):
    """Use a smaller claim only for a completed matching measurement."""
    positive_integer(fence_bytes, "physical memory fence")
    if completed is not True or matching is not True:
        return fence_bytes
    if type(peak_bytes) is not int or peak_bytes <= 0:
        return fence_bytes
    return (peak_bytes * 3 + 1) // 2


def module_source(arguments):
    """Refuse ambiguous compiler commands and paths outside the build root."""
    sources = [argument for argument in arguments if argument.endswith(".v")]
    if len(sources) != 1:
        raise ValueError("The compiler command must identify exactly one source.")
    source = PurePosixPath(sources[0])
    if source.is_absolute() or ".." in source.parts or sources[0] != source.as_posix():
        raise ValueError("The module source must use a normalized relative path.")
    return source.as_posix()


def make_profile(observations, gate_result, compiler, *, floor_bytes=GIB):
    """Retain maximum sampled peaks only from a successful complete gate."""
    if type(gate_result.get("exit_code")) is not int or gate_result["exit_code"] != 0:
        raise ValueError("The measurement gate must finish successfully.")
    positive_integer(floor_bytes, "reservation floor")
    compiler = Path(compiler).resolve(strict=True)
    modules = {}
    for observation in observations:
        if Path(observation["exe"]).resolve(strict=True) != compiler:
            raise ValueError("The measurement compiler differs from the bound compiler.")
        source = module_source(shlex.split(observation["command"]))
        fingerprint = digest(Path(observation["cwd"]) / source)
        peak = observation.get("observed_peak_rss_kib")
        if type(peak) is not int or peak < 0:
            raise ValueError("The sampled peak must be a nonnegative integer.")
        previous = modules.get(source)
        if previous is not None:
            if previous["source_sha256"] != fingerprint:
                raise ValueError("The module measurements bind different source bytes.")
            peak = max(peak, previous["sampled_peak_rss_kib"])
        modules[source] = {
            "source_sha256": fingerprint,
            "sampled_peak_rss_kib": peak,
            "claim_bytes": max(floor_bytes, (peak * 1024 * 3 + 1) // 2) if peak else None,
            "arguments": shlex.split(observation["command"])[1:],
        }
    return {"schema": SCHEMA, "compiler_sha256": digest(compiler),
            "floor_bytes": floor_bytes, "modules": modules, "measurement_complete": True,
            "qualification": "Sampled peaks are lower bounds. Dependencies can change memory use. "
                             "The physical compiler limits remain mandatory."}


def module_claim(profile, arguments, cwd, compiler, *, fallback_bytes=16 * GIB):
    """Use the full fallback when the source or compiler binding differs."""
    positive_integer(fallback_bytes, "fallback reservation")
    if profile.get("schema") != SCHEMA:
        raise ValueError("The module memory profile schema is unsupported.")
    try:
        source = module_source(arguments)
    except ValueError:
        return {"claim_bytes": fallback_bytes, "reason": "ambiguous_source"}
    row = profile["modules"].get(source)
    reason = "unknown_module"
    if row is not None:
        if profile["compiler_sha256"] != digest(compiler):
            reason = "changed_compiler"
        elif row["source_sha256"] != digest(Path(cwd) / source):
            reason = "changed_source"
        elif profile.get("measurement_complete") is not True:
            reason = "incomplete_measurement"
        elif row.get("arguments") != list(arguments):
            reason = "changed_arguments"
        elif row["claim_bytes"] is None:
            reason = "missing_peak"
        else:
            return {"claim_bytes": max(profile["floor_bytes"], measurement_claim(
                        fallback_bytes, row["sampled_peak_rss_kib"] * 1024, completed=True, matching=True)),
                    "reason": "measured_module", "source": source}
    return {"claim_bytes": fallback_bytes, "reason": reason, "source": source}


def admission(request_bytes, live_claims, available_bytes, *, headroom_bytes=20 * GIB,
              maximum_compilers=48, observations=None, slice_max_bytes=None):
    """Evaluate one fresh snapshot without mutating any reservation."""
    positive_integer(request_bytes, "requested reservation")
    positive_integer(available_bytes, "available memory")
    positive_integer(maximum_compilers, "compiler limit")
    if type(headroom_bytes) is not int or headroom_bytes < 0:
        raise ValueError("The memory headroom must be a nonnegative integer.")
    for claim in live_claims:
        positive_integer(claim, "live reservation")
    sizing = evaluate({str(index): value for index, value in enumerate(live_claims)},
                      request_bytes, available_bytes, observations=observations,
                      slice_max_bytes=slice_max_bytes, headroom_bytes=headroom_bytes)
    reason = ("compiler_limit" if len(live_claims) >= maximum_compilers else
              "memory_budget" if not sizing["fits"] else None)
    return dict(sizing, admission_pool="compiler", admitted=reason is None, reason=reason,
                compiler_count_after=len(live_claims) + 1)


def process_identity(proc, pid):
    """Read a live PID identity. Zombies cannot supply a memory sample."""
    try:
        fields = (proc / str(pid) / "stat").read_text().rsplit(")", 1)[1].split()
        if fields[0] in {"Z", "X", "x"}:
            return None
        return (int(fields[1]), fields[19])
    except (OSError, IndexError, ValueError):
        return None


def probe_measurement(marker, metadata, physical, proc):
    """Bind a probe's measured compiler peaks to its live reservation owner."""
    try:
        owner = int(marker.name.split(".", 1)[0])
        child = int(metadata["child"])
        expected_owner = metadata["owner_start"]
    except (KeyError, ValueError):
        return None
    owner_identity = process_identity(proc, owner)
    child_identity = process_identity(proc, child)
    if (owner_identity is None or owner_identity[1] != expected_owner
            or child_identity is None):
        return None
    if metadata.get("memory_probe_child_start", child_identity[1]) != child_identity[1]:
        return None
    identities = {owner: owner_identity, child: child_identity}
    current, visited = child, set()
    while current != owner:
        if current in visited:
            return None
        visited.add(current)
        identity = process_identity(proc, current)
        if identity is None or (current in identities and identities[current] != identity):
            return None
        identities[current] = identity
        current = identity[0]
    pending, visited, covered, peaks = [child], set(), set(), []
    while pending:
        pid = pending.pop()
        if pid in visited:
            continue
        visited.add(pid)
        identity = process_identity(proc, pid)
        if identity is None:
            if pid in physical:
                return None
            continue
        if pid in identities and identity != identities[pid]:
            return None
        identities[pid] = identity
        if pid in physical:
            try:
                status = (proc / str(pid) / "status").read_text().splitlines()
                peak = next(int(line.split()[1]) for line in status if line.startswith("VmHWM:"))
                peaks.append(positive_integer(peak, "observed probe peak") * 1536)
            except (OSError, StopIteration, ValueError):
                return None
            covered.add(pid)
        try:
            children = list(map(int, (proc / str(pid) / "task" / str(pid) / "children").read_text().split()))
        except OSError:
            children = []
        for descendant in children:
            found = process_identity(proc, descendant)
            if found is not None and found[0] == pid:
                identities[descendant] = found
                pending.append(descendant)
    if not peaks or any(process_identity(proc, pid) != identity for pid, identity in identities.items()):
        return None
    return {"claim_bytes": sum(peaks), "covered": covered, "child_start": child_identity[1]}


def reservation_claims(markers, *, proc=Path("/proc"), fallback_bytes=32 * GIB,
                       refresh=False, retained_claims=None):
    """Read live reservations under the caller's existing guard mutex.

    This reader never changes a marker. The unified ledger commits growth.
    The refresh argument remains compatible with old callers.
    Live samples cannot reduce the existing growth policy.
    """
    retained_claims = retained_claims or {}
    physical = compiler_pids(proc)
    covered, claims, growth, scopes = set(), [], [], {}
    reader = ScopeReader()
    for marker in markers:
        marker = Path(marker)
        lines = marker.read_text().splitlines()
        if not lines or lines[0] == "pending":
            continue
        values, metadata = {}, {"child": lines[0]}
        for line in lines[1:]:
            name, separator, value = line.partition("=")
            if separator and name in {"probe", "owner_start", "cpu", "memory_probe_child_start"}:
                if name in metadata:
                    raise ValueError("The reservation repeats an ownership field.")
                metadata[name] = value
            if separator and name in {"memory_claim_bytes", "memory_fence_bytes", "memory_gib", "memory_probe_claim_bytes"}:
                if name in values:
                    raise ValueError("The reservation repeats a memory field.")
                values[name] = positive_integer(int(value), "retained memory field")
        fence = values.get("memory_fence_bytes", values.get("memory_gib", max(64 * GIB, fallback_bytes) // GIB) * GIB)
        probe = metadata.get("probe")
        if probe in {"issue10", "issue10-cpu-only"}:
            expected_fence = (64 if probe == "issue10" else 6) * GIB
            if fence != expected_fence or metadata.get("cpu") != "unlimited":
                raise ValueError("The probe physical policy differs from its marker.")
            measured = probe_measurement(marker, metadata, physical, proc)
            if measured is None:
                claims.append(fence)
                continue
            covered.update(measured["covered"])
            previous = max(values.get("memory_probe_claim_bytes", 0), retained_claims.get(str(marker), 0))
            increased = max(fence, previous, measured["claim_bytes"])
            if proc == Path('/proc'):
                scopes[str(len(claims))] = reader.compiler(marker)
            claims.append(increased)
            if increased > previous:
                growth.append({"reservation": str(marker), "previous_bytes": previous,
                               "claim_bytes": increased, "probe": True})
            continue
        claim = max(values.get("memory_claim_bytes", fence), retained_claims.get(str(marker), 0))
        pending = [int(lines[0])] if lines[0].isdecimal() else []
        visited, peaks = set(), []
        while pending:
            pid = pending.pop()
            if pid in visited:
                continue
            visited.add(pid)
            if pid in physical:
                covered.add(pid)
                try:
                    status = (proc / str(pid) / "status").read_text().splitlines()
                    peak = next(int(line.split()[1]) for line in status if line.startswith("VmHWM:"))
                    peaks.append(positive_integer(peak, "observed compiler peak") * 1536)
                except (OSError, StopIteration):
                    peaks.append(fence)
            try:
                pending.extend(map(int, (proc / str(pid) / "task" / str(pid) / "children").read_text().split()))
            except FileNotFoundError:
                pass
        increased = max(fence, claim, sum(peaks))
        if proc == Path('/proc'):
            scopes[str(len(claims))] = reader.compiler(marker)
        claims.append(increased)
        if increased > claim:
            growth.append({"reservation": str(marker), "previous_bytes": claim, "claim_bytes": increased})
    claims.extend([max(64 * GIB, fallback_bytes)] * len(physical - covered))
    return {"claims": claims, "growth": growth, "unrepresented_compilers": sorted(physical - covered),
            "scope_observations": scopes}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("test-ledger-policy")
    claim = commands.add_parser("claim")
    claim.add_argument("--profile", type=Path, required=True)
    claim.add_argument("--cwd", type=Path, required=True)
    claim.add_argument("--compiler", type=Path, required=True)
    claim.add_argument("--fallback-bytes", type=int, required=True)
    claim.add_argument("arguments", nargs=argparse.REMAINDER)
    check = commands.add_parser("admission")
    check.add_argument("--request-bytes", type=int, required=True)
    check.add_argument("--fallback-bytes", type=int, default=64 * GIB)
    check.add_argument("--available-bytes", type=int, required=True)
    check.add_argument("--headroom-bytes", type=int, default=20 * GIB)
    check.add_argument("--maximum-compilers", type=int, default=48)
    check.add_argument("--proc", type=Path, default=Path("/proc"))
    check.add_argument("markers", nargs="*")
    confirm = commands.add_parser('ledger-confirm')
    confirm.add_argument('--marker', type=Path, required=True)
    confirm.add_argument('--replacement', type=Path, required=True)
    confirm.add_argument('--request-bytes', type=int, required=True)
    confirm.add_argument('--available-bytes', type=int, required=True)
    release = commands.add_parser('ledger-release')
    release.add_argument('--marker', type=Path, required=True)
    mark = commands.add_parser('ledger-mark')
    mark.add_argument('--marker', type=Path, required=True)
    aggregate = commands.add_parser('aggregate-limit')
    aggregate.add_argument('--guard-pid', type=int, required=True)
    aggregate.add_argument('--inner-fence-bytes', type=int, required=True)
    aggregate.add_argument('--booking-bytes', type=int, required=True)
    aggregate.add_argument('--explicit-limit-bytes', type=int)
    aggregate.add_argument('--gate-limit-bytes', type=int)
    args = parser.parse_args()
    if args.command == 'test-ledger-policy':
        try:
            check_test_ledger()
        except ValueError as error:
            parser.exit(2, str(error) + '\n')
        return 0
    if args.command == 'aggregate-limit':
        print(select_guard_aggregate_limit(args.guard_pid, args.inner_fence_bytes, args.booking_bytes,
              explicit_limit_bytes=args.explicit_limit_bytes, gate_limit_bytes=args.gate_limit_bytes))
        return 0
    if args.command == 'ledger-confirm':
        result = confirm_shell(args.marker, args.replacement, args.request_bytes, args.available_bytes)
        if not result['fits']:
            print('unified memory ledger refuses the reservation')
            return 3
        return 0
    if args.command == 'ledger-mark':
        return 0 if mark_shell(args.marker) else 4
    if args.command == 'ledger-release':
        return 0 if release_shell(args.marker) else 4
    if args.command == "claim":
        arguments = args.arguments[1:] if args.arguments[:1] == ["--"] else args.arguments
        result = module_claim(json.loads(args.profile.read_text()), arguments, args.cwd, args.compiler,
                              fallback_bytes=args.fallback_bytes)
        print(result["claim_bytes"])
    else:
        observed = reservation_claims(args.markers, proc=args.proc, fallback_bytes=args.fallback_bytes,
                                      refresh=False, retained_claims=read_shell_bookings())
        refresh_shell_growth(observed['growth'])
        result = current_projection(args.request_bytes, args.available_bytes)
        result['admitted'] = result['fits'] and len(observed['claims']) < args.maximum_compilers
        result['reason'] = 'compiler_limit' if len(observed['claims']) >= args.maximum_compilers else 'memory_budget'
        if not result["admitted"]:
            print(f"module memory: {result['reason']}; unrealized {result['requested_unrealized_bytes']} bytes, "
                  f"available budget {result['budget_bytes']} bytes; total {result['requested_total_bytes']} bytes, "
                  f"slice cap {result['slice_claim_cap_bytes']} bytes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
