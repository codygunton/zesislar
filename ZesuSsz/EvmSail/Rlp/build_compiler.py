#!/usr/bin/env python3
"""Build the selected Sail executable and its Coq plugin without changing opam."""

import argparse
import os
from pathlib import Path
import subprocess

from generate import SAIL_REVISION, check_source


def main() -> None:
    root = Path(__file__).resolve().parents[3]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--build-dir", type=Path,
                        default=root / "_build/agents/worker-build-1/sail-compiler")
    parser.add_argument("--switch", default="/home/cody/islaris")
    parser.add_argument("--jobs", type=int, default=20)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 48:
        parser.error("The worker count must be between 1 and 48.")
    source = args.source.resolve()
    build = args.build_dir.resolve()
    check_source(source, SAIL_REVISION)
    build.parent.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    # The external build directory lies outside Sail's Git checkout.
    # Select its Git directory so Sail embeds the compiler revision.
    env["GIT_DIR"] = subprocess.check_output(
        ["git", "-C", str(source), "rev-parse", "--absolute-git-dir"],
        text=True).strip()
    subprocess.run([
        "python3", str(root / "tools/build_record.py"),
        "--build-dir", str(build), "--target", "pinned-sail",
        "--", "opam", "exec", f"--switch={args.switch}", "--",
        "dune", "build", "--root", str(source), "--build-dir", str(build),
        "--cache=enabled", "--profile", "release", f"-j{args.jobs}",
        "src/bin/sail.exe", "src/sail_coq_backend/sail_plugin_coq.cmxs",
    ], env=env, check=True)
    subprocess.run([str(build / "default/src/bin/sail.exe"), "--version"],
                   env={**env, "SAIL_NO_PLUGINS": "1"}, check=True)


if __name__ == "__main__":
    main()
