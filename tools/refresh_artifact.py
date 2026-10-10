"""Refresh one Dune target under a private build lock and normal admission."""

import argparse
import fcntl
import os
from pathlib import Path
import subprocess
import time

from native_admission import clean_environment, inventory


ROOT = Path(__file__).resolve().parents[1]
GUARD = ROOT / "tools/resource_guard.sh"


def build_path(root, value):
    build = (root / value).resolve()
    if not build.is_relative_to(root / "_build/agents") or build == root / "_build/agents":
        raise ValueError("The refresh requires a private build under _build/agents.")
    return build


def artifact_lock(build):
    return build.parent / (build.name + ".artifact.lock")


def environment():
    env = clean_environment(os.environ)
    env.pop("OCAMLPATH", None)
    env["ZESU_IO"] = "batch"
    return env


def query(guard, root, env, name):
    return subprocess.check_output([str(guard), name], cwd=root, env=env, text=True).strip()


def pet_uses_workspace(process, root, build, proc=Path("/proc")):
    if process["comm"] != "pet":
        return False
    try:
        directory = (proc / str(process["pid"]) / "cwd").resolve(strict=True)
    except (FileNotFoundError, ProcessLookupError):
        return False
    except PermissionError:
        # An unreadable live Pet cannot establish independent ownership.
        return True
    return directory.is_relative_to(root.resolve()) or directory.is_relative_to(build.resolve())


def admission(guard, root, build, env):
    processes = inventory()
    return (not any(pet_uses_workspace(p, root, build) for p in processes)
            and len(processes) < 48
            and query(guard, root, env, "hold") == "none"
            and query(guard, root, env, "lock-status") == "no gate lock")


def command(root, build, target, switch):
    parts = Path(target).parts
    if (not parts or parts == ("default",) or target.startswith(("-", "@"))
            or Path(target).is_absolute() or ".." in parts):
        raise ValueError("The refresh requires one relative Dune target.")
    if Path(target).parts[0] == "install":
        raise ValueError("The refresh requires a source target, not an installed artifact path.")
    if Path(target).parts[0] == "default":
        target = str(Path(target).relative_to("default"))
    return [str(root / "tools/resource_guard.sh"), "batch", "artifact-refresh", "--",
            "opam", "exec", "--switch=" + switch, "--", "dune", "build",
            "--root", str(root), "--build-dir", str(build), "--cache=enabled", "-j1", target]


def attempt(root, build, argv, env):
    # A Pet or gate can appear between the first check and lock acquisition.
    if not admission(GUARD, root, build, env):
        return None
    build.parent.mkdir(parents=True, exist_ok=True)
    with artifact_lock(build).open("a+") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return None
        try:
            if not admission(GUARD, root, build, env):
                return None
            # batch performs its own normal launch reservation and memory checks.
            return subprocess.run(argv, cwd=root, env=env).returncode
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-dir", required=True)
    parser.add_argument("--switch", default=str(Path.home() / "islaris"))
    parser.add_argument("target")
    args = parser.parse_args()
    build = build_path(ROOT, args.build_dir)
    argv = command(ROOT, build, args.target, args.switch)
    env = environment()
    while True:
        waited = subprocess.run([str(GUARD), "wait"], cwd=ROOT, env=env)
        if waited.returncode:
            return waited.returncode
        result = attempt(ROOT, build, argv, env)
        if result is not None:
            return result
        time.sleep(5)


if __name__ == "__main__":
    raise SystemExit(main())
