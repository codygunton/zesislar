#!/usr/bin/env python3
"""Generate the pinned dependency closure for the first two decoder rungs."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import tempfile
import time


EVM_REVISION = "d0e4aabdde52f9158d191dbc8add444abffd9a6a"
SAIL_REVISION = "25cc260d9940d65d2e5da427fe4b5d402809a50c"
ROOTS = (
    "rlp_decode_item", "rlp_ref_hdr", "rlp_node_cursor",
    "decode_parent_header_fields", "sail_model_init",
)
EXCLUDED = (
    "decode_legacy_tx", "decode_access_list_tx", "decode_fee_market_tx",
    "decode_blob_tx", "decode_set_code_tx", "decode_block_header_ssz",
)
BLOB_HANDOFF_RECORD = "BLOB_HANDOFF_EXPERIMENT.json"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_source(path: Path, revision: str) -> None:
    actual = subprocess.check_output(
        ["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
    if actual != revision:
        raise ValueError(f"Unexpected revision at {path}: {actual}")
    dirty = subprocess.check_output(
        ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"],
        text=True)
    if dirty:
        raise ValueError(f"Tracked source changes at {path}: {dirty}")


def main() -> None:
    here = Path(__file__).resolve().parent
    root = here.parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evm-source", type=Path, required=True)
    parser.add_argument("--sail-source", type=Path, required=True)
    parser.add_argument("--sail-build", type=Path, required=True,
                        help="The Dune build directory containing default/src.")
    parser.add_argument("--output", type=Path,
                        default=root / "generated/evm-sail-coq/rlp")
    args = parser.parse_args()
    args.evm_source = args.evm_source.resolve()
    args.sail_source = args.sail_source.resolve()
    args.sail_build = args.sail_build.resolve()
    check_source(args.evm_source, EVM_REVISION)
    check_source(args.sail_source, SAIL_REVISION)
    compiler = args.sail_build / "default/src/bin/sail.exe"
    plugin = args.sail_build / "default/src/sail_coq_backend/sail_plugin_coq.cmxs"
    env = os.environ.copy()
    env["SAIL_NO_PLUGINS"] = "1"
    env["PATH"] = str(root / "bin") + os.pathsep + env["PATH"]
    version = subprocess.check_output([str(compiler), "--version"], env=env, text=True).strip()
    if SAIL_REVISION not in version:
        raise ValueError(f"Compiler version does not identify the pin: {version}")
    commands = (here / "slice.commands").read_text()
    with tempfile.TemporaryDirectory(prefix="zesu-rlp-") as temp:
        stage = Path(temp)
        source = stage / "source"
        shutil.copytree(args.evm_source / "sail", source)
        shutil.copy(here / "decoder.sail_project", source)
        shutil.copytree(here / "shim", source / "shim")
        # Sail's native slice_keep_std recognizes a directory named sail/lib.
        library = stage / "sail"
        library.mkdir()
        (library / "lib").symlink_to(args.sail_source / "lib", target_is_directory=True)
        env["SAIL_DIR"] = str(library)
        output = stage / "output"
        output.mkdir()
        argv = [
            str(compiler), "--plugin", str(plugin),
            "--coq-semantic-range-types", "--coq-undef-axioms",
            "--coq-output-dir", "output",
            "--project", "source/decoder.sail_project",
            "--all-modules", "--interact-custom",
        ]
        started = time.monotonic()
        result = subprocess.run(argv, input=commands, text=True, env=env, cwd=stage,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                timeout=1800, check=False)
        elapsed = time.monotonic() - started
        diagnostics = re.sub(r"\x1b\[[0-9;]*m", "", result.stdout)
        # The Sail REPL can report errors while it returns exit code zero.
        if result.returncode or re.search(r"(?:Type error|Error):", diagnostics):
            raise RuntimeError(diagnostics)
        names = ("evm_rlp.v", "evm_rlp_types.v")
        generated = {name: (output / name).read_text() for name in names}
        declarations = set(re.findall(
            r"^(?:Definition|Fixpoint|Axiom)\s+(\w+)",
            generated["evm_rlp.v"], re.MULTILINE))
        if not set(ROOTS) <= declarations or set(EXCLUDED) & declarations:
            raise ValueError("The generated closure has unexpected roots or decoders.")
        generated["evm_rlp.v"] = generated["evm_rlp.v"].replace(
            "Require Import evm_rlp_types.", "Require Import EvmSailRlp.evm_rlp_types.")
        args.output.mkdir(parents=True, exist_ok=True)
        for name, text in generated.items():
            (args.output / name).write_text(text)
        manifest = {
            "evmSailRevision": EVM_REVISION,
            "sailCompilerRevision": SAIL_REVISION,
            "sailCompilerVersion": version,
            "sailCompilerSha256": digest(compiler),
            "sailCoqPluginSha256": digest(plugin),
            "sailProjectSha256": digest(here / "decoder.sail_project"),
            "sliceCommandsSha256": digest(here / "slice.commands"),
            "inputShimSha256": digest(here / "shim/input.sail"),
            "roots": ROOTS,
            "excludedDecoders": EXCLUDED,
            "blobDecoderGenerationMethod": {
                "method": "staged typed prefix handoff",
                "evidencePath": "ZesuSsz/EvmSail/Rlp/" + BLOB_HANDOFF_RECORD,
                "evidenceSha256": digest(here / BLOB_HANDOFF_RECORD),
                "sourceInliningCheck": "exact pinned decode_blob_tx reconstruction",
                "compiledWithinModuleLimits": True,
                "includedInThisSnapshot": False,
            },
            "generationSeconds": elapsed,
            "generationPeakRssKiB": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
            "snapshotSha256": {name: digest(args.output / name) for name in names},
            "axiomCounts": {name: len(re.findall(r"^Axiom\s", text, re.MULTILINE))
                            for name, text in generated.items()},
        }
        (args.output / "SOURCE.json").write_text(json.dumps(manifest, indent=2) + "\n")
        print(json.dumps(manifest, indent=2))


if __name__ == "__main__":
    main()
