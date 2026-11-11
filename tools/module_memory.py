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
import sys
import tempfile

try:
    from .det.coqc_slots import compiler_pids
except ImportError:
    from det.coqc_slots import compiler_pids


_directory = Path(__file__).resolve().parent
_admission = _directory / 'block/harness/code/admission_memory.py'
if not _admission.is_file():
    _admission = _directory / 'block/admission_memory.py'
if not _admission.is_file() or not _admission.resolve().is_relative_to(_directory):
    raise ImportError('The module memory helper lacks its owned admission dependency.')
# The admission reader imports owned siblings and block helpers after loading.
_block = (_directory / "block").resolve()
if not _block.is_dir() or not _block.is_relative_to(_directory):
    raise ImportError("The module memory helper lacks its owned block dependency.")
sys.path[:0] = list(dict.fromkeys((str(_admission.resolve().parent), str(_block))))
_spec = importlib.util.spec_from_file_location('_zesu_owned_admission_memory', _admission)
_module = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_module)
evaluate, ScopeReader = _module.evaluate, _module.ScopeReader
confirm_shell, release_shell = _module.confirm_shell, _module.release_shell
recover_dead_shell = _module.recover_dead_shell
recover_stale_shell = _module.recover_stale_shell
recover_stale_shells = _module.recover_stale_shells
current_projection = _module.current_projection
mark_shell = _module.mark_shell
refresh_shell_growth = _module.refresh_shell_growth
check_test_ledger = _module.check_test_ledger
read_shell_bookings = _module.read_shell_bookings
authorized_shell_booking = _module.authorized_shell_booking
select_guard_aggregate_limit = _module.select_guard_aggregate_limit


GIB = 1024 ** 3


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


# Every guarded Dune compile books from this shared profile and records its
# own scope peak in it. The key is the module path; a row binds the source
# bytes, the compiler bytes and the compiler arguments, so a changed module
# books the full fence until it is measured again.
SCHEMA = "zesu.module-memory.v3"
DEFAULT_PROFILE = Path(os.environ.get("XDG_CACHE_HOME") or Path.home() / ".cache") / "zesu-module-memory/profile.json"
# The floor and margin apply to the largest completed cgroup memory.peak of a
# matching row. Measured 2026-11-09 over 546 modules: min 104 MiB, p5 525,
# p50 530, p95 547, max 566 MiB. A 384 MiB floor keeps every single booking
# under 4x its peak (3.7x at 104 MiB); the 1.25 margin gives 1.25x in sum.
# The booking also covers 1.5 times the compiler's peak resident set: the
# guard raises any live booking below that (reservation_claims), and a raise
# on every healthy compile costs a ledger write under the guard mutex.
FLOOR_BYTES = 384 * 1024 ** 2
MARGIN_NUMERATOR, MARGIN_DENOMINATOR = 5, 4
RSS_NUMERATOR, RSS_DENOMINATOR = 3, 2
CGROUP_ROOT = Path(os.environ.get("ZESU_CGROUP_ROOT", "/sys/fs/cgroup"))
BINDING = ("source_sha256", "compiler_sha256", "arguments_sha256")


def arguments_digest(arguments):
    return hashlib.sha256(json.dumps(list(arguments)).encode()).hexdigest()


def booking(peak_bytes, fallback_bytes, rss_peak_bytes=None):
    """Book the margin over a measured peak, at least the floor, at most the fence."""
    claim = max(FLOOR_BYTES, -(-peak_bytes * MARGIN_NUMERATOR // MARGIN_DENOMINATOR))
    if type(rss_peak_bytes) is int and rss_peak_bytes > 0:
        claim = max(claim, -(-rss_peak_bytes * RSS_NUMERATOR // RSS_DENOMINATOR))
    return min(fallback_bytes, claim)


def binding(arguments, cwd, compiler):
    """Return the row key and binding of one compile, or raise ValueError."""
    source = module_source(arguments)
    return source, {"source_sha256": digest(Path(cwd) / source),
                    "compiler_sha256": digest(Path(compiler).resolve(strict=True)),
                    "arguments_sha256": arguments_digest(arguments)}


def load_profile(path):
    """Read the profile. A missing, damaged or older profile is empty."""
    try:
        profile = json.loads(Path(path).read_text())
    except (OSError, ValueError):
        profile = None
    if not isinstance(profile, dict) or profile.get("schema") != SCHEMA \
            or not isinstance(profile.get("modules"), dict):
        return {"schema": SCHEMA, "modules": {}}
    return profile


# A module with no row books a prior from its own directory: 1.5 times the
# largest measured peak there, at least 2 GiB, at most the fallback. On
# 2026-11-10 eleven new 1 s declaration modules each booked the 16 GiB fence
# and waited 25 min for admission; every measured directory but one has a
# largest peak under 1.3 GiB. A directory with no rows in or below it books
# from its nearest ancestor that has rows in or below it, never above ZesuSsz/
# for a ZesuSsz module (the repository root bounds the others): a new function
# directory such as ZesuSsz/Generated/NextUint64/FP301 books from the
# measured modules under ZesuSsz/Generated. Without such an ancestor the
# module keeps the fallback. A module whose source changed books the same
# prior until it is measured again: on 2026-11-11 a regenerated trace set
# changed 960 trace modules (old peaks at most 0.9 GiB), and each booked the
# 16 GiB fence. Changed compilers and arguments keep the fallback. The
# compiler fence does not change: a module above its booking hits the same
# limit.
PRIOR_NUMERATOR, PRIOR_DENOMINATOR = 3, 2
PRIOR_FLOOR_BYTES = 2 * GIB
PRIOR_ROOTS = ("ZesuSsz",)
PRIOR_REASONS = ("directory_prior", "ancestor_prior", "changed_source_prior")


def _ancestors(directory):
    """Yield a normalized relative directory and its ancestors up to '.'."""
    while directory not in ("", "."):
        yield directory
        directory = directory.rpartition("/")[0]
    yield "."


def prior_directory(profile, source):
    """Return (directory, largest measured peak under it) for the nearest measured directory, or None.

    A directory counts as measured when a module in it or below it has a row."""
    largest = {}
    for key, row in profile["modules"].items():
        if not isinstance(row, dict):
            continue
        peak = max((value for value in (row.get("peak_bytes"), row.get("rss_peak_bytes"))
                    if type(value) is int and value > 0), default=0)
        if peak:
            for directory in _ancestors(key.rpartition("/")[0]):
                if largest.get(directory, 0) >= peak:
                    break
                largest[directory] = peak
    start = PurePosixPath(source).parent.as_posix()
    root = next((top for top in PRIOR_ROOTS if start == top or start.startswith(top + "/")), ".")
    for directory in _ancestors(start):
        if directory in largest:
            return directory, largest[directory]
        if directory == root:
            return None
    return None


def directory_prior(profile, source, fallback_bytes, found=None):
    """Return the booking for an unmeasured module, or None without a measured directory."""
    found = prior_directory(profile, source) if found is None else found
    if not found:
        return None
    prior = max(PRIOR_FLOOR_BYTES, -(-found[1] * PRIOR_NUMERATOR // PRIOR_DENOMINATOR))
    return min(fallback_bytes, prior)


def module_claim(profile, arguments, cwd, compiler, *, fallback_bytes=16 * GIB):
    """Use the full fallback unless a row matches this exact compile.

    A module without any row books its directory prior when one exists."""
    positive_integer(fallback_bytes, "fallback reservation")
    if profile.get("schema") != SCHEMA:
        raise ValueError("The module memory profile schema is unsupported.")
    try:
        source, bound = binding(arguments, cwd, compiler)
    except (OSError, ValueError):
        return {"claim_bytes": fallback_bytes, "reason": "ambiguous_source"}
    row = profile["modules"].get(source)
    if row is None:
        found = prior_directory(profile, source)
        if found is None:
            return {"claim_bytes": fallback_bytes, "reason": "unknown_module", "source": source}
        prior = directory_prior(profile, source, fallback_bytes, found)
        reason = "directory_prior" if found[0] == PurePosixPath(source).parent.as_posix() else "ancestor_prior"
        return {"claim_bytes": prior, "reason": reason, "source": source, "prior_directory": found[0]}
    for name, reason in (("compiler_sha256", "changed_compiler"), ("arguments_sha256", "changed_arguments")):
        if row.get(name) != bound[name]:
            return {"claim_bytes": fallback_bytes, "reason": reason, "source": source}
    if row.get("source_sha256") != bound["source_sha256"]:
        prior = directory_prior(profile, source, fallback_bytes)
        if prior is None:
            return {"claim_bytes": fallback_bytes, "reason": "changed_source", "source": source}
        return {"claim_bytes": prior, "reason": "changed_source_prior", "source": source}
    peak = row.get("peak_bytes")
    if type(peak) is not int or peak <= 0:
        return {"claim_bytes": fallback_bytes, "reason": "missing_peak", "source": source}
    return {"claim_bytes": booking(peak, fallback_bytes, row.get("rss_peak_bytes")),
            "reason": "measured_module", "source": source}


def record_measurement(profile_path, source, bound, peak_bytes, *, rss_peak_bytes=None, ended_ns=None):
    """Merge one completed peak under the profile lock and replace atomically.

    A matching row keeps its largest peak; a changed binding starts a new row.
    """
    import fcntl
    positive_integer(peak_bytes, "measured peak")
    profile_path = Path(profile_path)
    profile_path.parent.mkdir(parents=True, exist_ok=True)
    with open(profile_path.with_name(profile_path.name + ".lock"), "a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        profile = load_profile(profile_path)
        row = profile["modules"].get(source)
        if row is not None and all(row.get(name) == bound[name] for name in BINDING):
            row.update(peak_bytes=max(row["peak_bytes"], peak_bytes),
                       minimum_peak_bytes=min(row.get("minimum_peak_bytes", peak_bytes), peak_bytes),
                       observations=row.get("observations", 1) + 1)
        else:
            row = dict(bound, peak_bytes=peak_bytes, minimum_peak_bytes=peak_bytes, observations=1)
        if type(rss_peak_bytes) is int and rss_peak_bytes > 0:
            row["rss_peak_bytes"] = max(row.get("rss_peak_bytes", 0), rss_peak_bytes)
        row["updated_ns"] = ended_ns
        profile["modules"][source] = row
        descriptor, temporary = tempfile.mkstemp(prefix=".profile-", dir=profile_path.parent)
        try:
            with os.fdopen(descriptor, "w") as stream:
                json.dump(profile, stream, sort_keys=True, separators=(",", ":"))
            os.replace(temporary, profile_path)
        except BaseException:
            Path(temporary).unlink(missing_ok=True)
            raise
        return row


def scope_peak(*, proc=Path("/proc"), cgroup_root=None, unit=None):
    """Read memory.peak of this process's own guard scope, or None.

    The cgroup leaf must be the scope unit that the guard named, so a run
    outside a guard scope never reports its parent's memory.
    """
    unit = os.environ.get("ZESU_SCOPE_UNIT") if unit is None else unit
    if not unit:
        return None
    try:
        membership = next(line.split(":", 2)[2] for line in
                          (proc / "self/cgroup").read_text().splitlines() if line.startswith("0::"))
        if PurePosixPath(membership).name != unit:
            return None
        peak = int((Path(cgroup_root or CGROUP_ROOT) / membership.lstrip("/") / "memory.peak").read_text())
    except (OSError, StopIteration, ValueError):
        return None
    return peak if peak > 0 else None


def peak_exec(output, payload):
    """Run the compiler inside its scope, then save the scope's memory.peak."""
    import resource
    import signal
    import subprocess
    import time
    admitted = time.time_ns()
    child = subprocess.Popen(payload)

    def forward(number, _frame):
        if child.poll() is None:
            child.send_signal(number)
    for number in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(number, forward)
    status = child.wait()
    if status == 0:
        try:
            usage = resource.getrusage(resource.RUSAGE_CHILDREN)
            Path(output).write_text(json.dumps({"peak_bytes": scope_peak(), "rss_peak_bytes": usage.ru_maxrss * 1024 or None,
                                                "compiler_cpu_seconds": usage.ru_utime + usage.ru_stime,
                                                "admitted_ns": admitted, "ended_ns": time.time_ns()}))
        except OSError as error:
            print(f"module memory: scope peak not saved: {error}", file=sys.stderr)
    return status if status >= 0 else 128 - status


def observe(profile_path, output, guard, compiler, cwd, arguments, *, fallback_bytes):
    """Book one guarded compile from the profile and record its measured peak.

    The guard receives the claim through ZESU_MODULE_CLAIM_BYTES. Only a clean
    compile inside a guard scope supplies a peak; signals reach the guard.
    """
    import signal
    import subprocess
    import time
    profile_path = Path(profile_path)
    try:
        source, bound = binding(arguments, cwd, compiler)
    except (OSError, ValueError):
        source = bound = None
    claim = module_claim(load_profile(profile_path), arguments, cwd, compiler, fallback_bytes=fallback_bytes)
    descriptor, peak_file = tempfile.mkstemp(prefix=".peak-", dir=tempfile.gettempdir())
    os.close(descriptor)
    try:
        started = time.time_ns()
        payload = [str(guard), "scope", "dune-coqc", "--", sys.executable, "-B",
                   str(Path(__file__).resolve()), "peak-exec", "--output", peak_file,
                   "--", str(compiler), *arguments]
        child = subprocess.Popen(payload, env=dict(os.environ, ZESU_MODULE_CLAIM_BYTES=str(claim["claim_bytes"]),
                                                   ZESU_MODULE_MEMORY_PROFILE=str(profile_path)))

        def forward(number, _frame):
            if child.poll() is None:
                child.send_signal(number)
        for number in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
            signal.signal(number, forward)
        status = child.wait()
        if status != 0:
            return status if status > 0 else 128 - status
        import resource
        usage = resource.getrusage(resource.RUSAGE_CHILDREN)
        guarded_cpu = usage.ru_utime + usage.ru_stime
        try:
            measured = json.loads(Path(peak_file).read_text() or "{}")
        except (OSError, ValueError):
            measured = {}
    finally:
        Path(peak_file).unlink(missing_ok=True)
    peak = measured.get("peak_bytes")
    try:
        if source is not None and type(peak) is int and peak > 0:
            record_measurement(profile_path, source, bound, peak, rss_peak_bytes=measured.get("rss_peak_bytes"),
                               ended_ns=measured.get("ended_ns"))
        if output:
            import fcntl
            row = {"source": source, "cwd": str(Path(cwd).absolute()), "peak_bytes": peak,
                   "rss_peak_bytes": measured.get("rss_peak_bytes"),
                   # The guard path (scope setup, admission, ledger) is the
                   # guarded CPU less the compiler's own CPU.
                   "compiler_cpu_seconds": measured.get("compiler_cpu_seconds"),
                   "guarded_cpu_seconds": guarded_cpu,
                   "claim_bytes": claim["claim_bytes"], "claim_reason": claim["reason"],
                   "fence_bytes": fallback_bytes, "started_ns": started,
                   "admitted_ns": measured.get("admitted_ns"), "ended_ns": measured.get("ended_ns", time.time_ns())}
            with open(output, "a") as stream:
                fcntl.flock(stream, fcntl.LOCK_EX)
                stream.write(json.dumps(row, separators=(",", ":")) + "\n")
    except (OSError, ValueError) as error:
        print(f"module memory: measurement not recorded: {error}", file=sys.stderr)
    return 0


def booked_versus_peak(observations):
    """Compare concurrent bookings with concurrent measured peaks.

    A booking lasts from admission inside the scope to compiler exit, as in
    the guard ledger. The concurrent peak sum bounds live compiler memory.
    """
    rows = [json.loads(line) for line in Path(observations).read_text().splitlines() if line.strip()]
    timed = [row for row in rows if row.get("admitted_ns") is not None and row.get("ended_ns") is not None]

    def concurrent(field):
        events = sorted([(row["admitted_ns"], row.get(field) or 0) for row in timed]
                        + [(row["ended_ns"], -(row.get(field) or 0)) for row in timed])
        total = maximum = 0
        for _time, change in events:
            total += change
            maximum = max(maximum, total)
        return maximum
    peaks = sorted(row["peak_bytes"] for row in rows if type(row.get("peak_bytes")) is int)

    def quantile(fraction):
        return peaks[min(len(peaks) - 1, int(fraction * len(peaks)))] if peaks else 0
    return {"compiles": len(rows), "measured": len(peaks),
            "unmeasured_fence_bookings": sum(1 for row in rows
                                             if row.get("claim_reason") not in
                                             PRIOR_REASONS + ("measured_module",)),
            "directory_prior_bookings": sum(1 for row in rows if row.get("claim_reason") == "directory_prior"),
            "ancestor_prior_bookings": sum(1 for row in rows if row.get("claim_reason") == "ancestor_prior"),
            "changed_prior_bookings": sum(1 for row in rows if row.get("claim_reason") in PRIOR_REASONS[2:]),
            "maximum_concurrent_booked_bytes": concurrent("claim_bytes"),
            "maximum_concurrent_peak_bytes": concurrent("peak_bytes"),
            "peak_bytes_p50": quantile(0.5), "peak_bytes_p95": quantile(0.95),
            "peak_bytes_max": peaks[-1] if peaks else 0,
            "booked_bytes_total": sum(row.get("claim_bytes") or 0 for row in rows),
            "peak_bytes_total": sum(peaks),
            "compiler_cpu_seconds": round(sum(row.get("compiler_cpu_seconds") or 0 for row in rows), 1),
            "guarded_cpu_seconds": round(sum(row.get("guarded_cpu_seconds") or 0 for row in rows), 1)}


def publish_admission_totals(result=None, released_bytes=0, *, path=None):
    """Publish totals that held launches compare before a full admission check.

    A confirmation publishes its projection; a release subtracts its claim.
    The file is replaced atomically, which wakes waiting guards. It is only a
    hint: a waiting guard runs the full check at least every WAKE_TIMEOUT.
    """
    path = path or os.environ.get("ZESU_ADMISSION_SUMMARY")
    if not path:
        return None
    path = Path(path)
    if result is not None:
        fits = result.get("fits") is True
        live = result.get("live_memory_sample", {}).get("live_bytes", -1)
        values = [result["requested_total_bytes"] if fits else result["accounted_active_bytes"],
                  result["requested_unrealized_bytes"] if fits else result["unrealized_claim_bytes"],
                  result["budget_bytes"], result["slice_claim_cap_bytes"],
                  live if type(live) is int else -1, result.get("slice_max_bytes", 0)]
    else:
        try:
            values = [int(value) for value in path.read_text().split()[:6]]
            if len(values) != 6:
                raise ValueError
        except (OSError, ValueError):
            return None
        values[0] = max(0, values[0] - released_bytes)
        values[1] = max(0, values[1] - released_bytes)
    try:
        descriptor, temporary = tempfile.mkstemp(prefix=".admission-", dir=path.parent)
        with os.fdopen(descriptor, "w") as stream:
            stream.write(" ".join(str(int(value)) for value in values) + "\n")
        os.replace(temporary, path)
    except (OSError, KeyError, TypeError, ValueError):
        return None
    return values


def marker_claim(marker):
    try:
        fields = dict(line.split("=", 1) for line in Path(marker).read_text().splitlines()[1:] if "=" in line)
        return int(fields.get("memory_claim_bytes", 0))
    except (OSError, ValueError):
        return 0


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

    Unmeasured probes retain the full physical-fence claim. Measured families
    retain their validated claims below that fence. Growth never reduces a claim.
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
            recorded = max(values.get("memory_claim_bytes", 0),
                           values.get("memory_probe_claim_bytes", 0), retained_claims.get(str(marker), 0))
            authorized = (authorized_shell_booking(marker, recorded)
                          if recorded and "memory_fence_bytes" in values else None)
            measured = probe_measurement(marker, metadata, physical, proc)
            if measured is None and authorized is None:
                claims.append(fence)
                continue
            if measured is not None:
                covered.update(measured["covered"])
            previous = max(values.get("memory_probe_claim_bytes", 0), retained_claims.get(str(marker), 0))
            increased = max(authorized if authorized is not None else fence, previous,
                            measured["claim_bytes"] if measured is not None else 0)
            if proc == Path('/proc'):
                scopes[str(len(claims))] = reader.compiler(marker)
            claims.append(increased)
            if increased > max(authorized or 0, previous):
                growth.append({"reservation": str(marker), "previous_bytes": max(authorized or 0, previous),
                               "claim_bytes": increased, "probe": True})
            continue
        claim = max(values.get("memory_claim_bytes", fence), retained_claims.get(str(marker), 0)) if "memory_fence_bytes" in values else fence
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
                except (FileNotFoundError, ProcessLookupError):
                    # A compiler that exited after the snapshot holds no memory.
                    # Counting its fence made a finished compile "grow" past its
                    # measured booking, and its token could no longer be verified.
                    if (proc / str(pid)).exists():
                        peaks.append(fence)
                except StopIteration:
                    if not any(line.split()[1:2] in (["Z"], ["X"]) for line in status
                               if line.startswith("State:")):
                        peaks.append(fence)
                except OSError:
                    peaks.append(fence)
            try:
                pending.extend(map(int, (proc / str(pid) / "task" / str(pid) / "children").read_text().split()))
            except FileNotFoundError:
                pass
        increased = max(claim, sum(peaks))
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
    role_exit = commands.add_parser('role-exit-exec')
    role_exit.add_argument('--marker', type=Path, required=True)
    role_exit.add_argument('payload', nargs=argparse.REMAINDER)
    claim = commands.add_parser("claim")
    claim.add_argument("--profile", type=Path, default=DEFAULT_PROFILE)
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
    recover = commands.add_parser('ledger-recover-dead')
    recover.add_argument('--marker', type=Path, required=True)
    stale = commands.add_parser('ledger-recover-stale')
    stale_choice = stale.add_mutually_exclusive_group(required=True)
    stale_choice.add_argument('--marker', type=Path)
    stale_choice.add_argument('--all', action='store_true')
    mark = commands.add_parser('ledger-mark')
    mark.add_argument('--marker', type=Path, required=True)
    aggregate = commands.add_parser('aggregate-limit')
    aggregate.add_argument('--guard-pid', type=int, required=True)
    aggregate.add_argument('--inner-fence-bytes', type=int, required=True)
    aggregate.add_argument('--booking-bytes', type=int, required=True)
    aggregate.add_argument('--explicit-limit-bytes', type=int)
    aggregate.add_argument('--gate-limit-bytes', type=int)
    observe_parser = commands.add_parser("observe")
    observe_parser.add_argument("--profile", type=Path, default=DEFAULT_PROFILE)
    observe_parser.add_argument("--output", type=Path)
    observe_parser.add_argument("--guard", type=Path, required=True)
    observe_parser.add_argument("--compiler", type=Path, required=True)
    observe_parser.add_argument("--cwd", type=Path, required=True)
    observe_parser.add_argument("--fallback-bytes", type=int, required=True)
    observe_parser.add_argument("arguments", nargs=argparse.REMAINDER)
    peak = commands.add_parser("peak-exec")
    peak.add_argument("--output", type=Path, required=True)
    peak.add_argument("payload", nargs=argparse.REMAINDER)
    summary = commands.add_parser("observation-summary")
    summary.add_argument("--observations", type=Path, required=True)
    staging_exit = commands.add_parser('staging-exit-exec')
    staging_exit.add_argument('--marker', type=Path, required=True)
    staging_exit.add_argument('payload', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.command == "observe":
        arguments = args.arguments[1:] if args.arguments[:1] == ["--"] else args.arguments
        return observe(args.profile, args.output, args.guard, args.compiler, args.cwd, arguments,
                       fallback_bytes=positive_integer(args.fallback_bytes, "fallback reservation"))
    if args.command == "peak-exec":
        payload = args.payload[1:] if args.payload[:1] == ["--"] else args.payload
        if not payload:
            parser.error("The peak recorder requires its exact payload.")
        return peak_exec(args.output, payload)
    if args.command == "observation-summary":
        print(json.dumps(booked_versus_peak(args.observations)) if args.observations.exists() else "{}")
        return 0
    if args.command == 'staging-exit-exec':
        from staging_peaks import supervise
        payload = args.payload[1:] if args.payload[:1] == ['--'] else args.payload
        if not payload:
            parser.error('The staging supervisor requires its exact payload.')
        return supervise(args.marker, payload)
    if args.command == 'role-exit-exec':
        from role_peaks import supervise
        payload = args.payload[1:] if args.payload[:1] == ['--'] else args.payload
        if not payload:
            parser.error('The controller exit supervisor requires its exact payload.')
        return supervise(args.marker, payload)
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
        publish_admission_totals(result)
        if not result['fits']:
            print('unified memory ledger refuses the reservation')
            return 3
        return 0
    if args.command == 'ledger-mark':
        return 0 if mark_shell(args.marker) else 4
    if args.command == 'ledger-release':
        claim = marker_claim(args.marker)
        released = release_shell(args.marker)
        if released:
            publish_admission_totals(released_bytes=claim)
        return 0 if released else 4
    if args.command == 'ledger-recover-dead':
        return 0 if recover_dead_shell(args.marker) else 4
    if args.command == 'ledger-recover-stale':
        if args.all:
            print(json.dumps(recover_stale_shells()))
            return 0
        return 0 if recover_stale_shell(args.marker) else 4
    if args.command == "claim":
        arguments = args.arguments[1:] if args.arguments[:1] == ["--"] else args.arguments
        result = module_claim(load_profile(args.profile), arguments, args.cwd, args.compiler,
                              fallback_bytes=args.fallback_bytes)
        print(result["claim_bytes"])
    else:
        ledger = Path(os.environ.get('ZESU_CANONICAL_LEDGER', _module.DEFAULT_LEDGER))
        with _module.ledger_transaction(ledger):
            observed = reservation_claims(args.markers, proc=args.proc, fallback_bytes=args.fallback_bytes,
                                          refresh=False, retained_claims=read_shell_bookings())
            try:
                refresh_shell_growth(observed['growth'])
                unverified = None
            except ValueError as error:
                # A ledger bookkeeping error never fails a compile: hold this
                # launch with the reason, and the guard retries admission.
                unverified = str(error)
        # The memory budget is checked once, by ledger-confirm under the same
        # mutex hold. A second projection here cost a ledger pass per launch.
        if unverified is not None:
            print(f"module memory: unverified_growth; {unverified} "
                  f"Growth rows: {json.dumps(observed['growth'])}")
        elif len(observed['claims']) >= args.maximum_compilers:
            print(f"module memory: compiler_limit; {len(observed['claims'])} reservations")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
