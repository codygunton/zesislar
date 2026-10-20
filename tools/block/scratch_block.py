#!/usr/bin/env python3
"""Compile a native scratch copy of a decodeItem block.

Optional local additions precede the original statement. The scratch proof
ends with Abort, so its result does not certify the production theorem.
"""

import argparse
import os
from pathlib import Path
import re
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from residual.modules import parse_module

import coqc_primary


def find_block(workspace, pc):
    digits = pc.lower().removeprefix("0x")
    if not re.fullmatch(r"[0-9a-f]+(?:literal|shortstring)?", digits):
        raise ValueError("The block PC must be hexadecimal, with an optional Literal or ShortString suffix.")
    directory = workspace / "ZesuSsz/Proofs/DecodeItem"
    matches = [path for kind in ("Hand", "Auto")
               for path in (directory / kind).glob("Block*.v")
               if path.stem.removeprefix("Block").lower().endswith(digits)]
    exact = [path for path in matches
             if path.stem.removeprefix("Block").lower() == digits]
    selected = exact or matches
    if len(selected) != 1:
        raise ValueError("The block is missing or ambiguous.")
    return selected[0]


def scratch_source(module, additions=""):
    name = "DesignedBoundary_" + module.stem.removeprefix("Block")
    selected = [proof for proof in parse_module(module) if proof.name == name]
    if len(selected) != 1 or selected[0].inline:
        raise ValueError("The block requires one separate Proof line.")
    proof = selected[0]
    lines = module.read_text().splitlines(keepends=True)
    prefix = "".join(lines[:proof.declaration_line])
    statement = "".join(lines[proof.declaration_line:proof.proof_line])
    local = additions.rstrip() + "\n\n" if additions else ""
    return (prefix + local + statement + lines[proof.proof_line]
            + "  Set Printing Depth 30.\n"
              "  Time all: zesu_block.\n"
              "  Show.\n"
              "Abort.\n")


def main(argv=None):
    workspace = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pc", help="The block PC or unique suffix, optionally followed by Literal or ShortString.")
    parser.add_argument("extra", type=Path, nargs="?", help="Optional imports, lemmas, or local hints.")
    parser.add_argument("--source-workspace", type=Path,
                        help="Read the selected source from another workspace with this compiler helper.")
    parser.add_argument("--build-dir", type=Path,
                        default=Path(os.environ.get("AGENT_BUILD_DIR", workspace / "_build/agents/infra")))
    args = parser.parse_args(argv)
    try:
        source_workspace = args.source_workspace.resolve() if args.source_workspace else workspace
        module = find_block(source_workspace, args.pc)
        additions = args.extra.read_text() if args.extra else ""
        build = args.build_dir.resolve()
        if not build.is_dir():
            raise ValueError("The private build directory does not exist.")
        directory = build / "scratch-blocks"
        directory.mkdir(exist_ok=True)
        output = Path(tempfile.mkdtemp(prefix=module.stem + "-", dir=directory))
        source = output / module.name
        source.write_text(scratch_source(module, additions))
    except (OSError, ValueError) as error:
        parser.error(str(error))
    print("scratch_source=" + str(source), flush=True)
    policy = coqc_primary.budget_policy(memory_gib=64, diagnostic_probe=True)
    done, text, log, compiler, _ = coqc_primary.compile_source(
        source, output, build, policy=policy)
    print(text, end="" if text.endswith("\n") else "\n")
    print("compiler_log=" + str(log))
    if compiler and compiler.get("measurement_complete"):
        print(f"compiler_cpu_seconds={compiler['cpu_seconds']:.6f} "
              f"peak_rss_gib={compiler['peak_rss_kib'] / 1024**2:.6f}")
    else:
        print("Compiler CPU is unavailable.", file=sys.stderr)
    return done.returncode


if __name__ == "__main__":
    raise SystemExit(main())
