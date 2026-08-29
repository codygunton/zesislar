# Level 1 evidence parity

The reference is `binary-fv-experiment@38a3a14a`.

The Rocq repository keeps 12 shared evidence and test files byte-identical.
`contracts/level1-evidence-parity.json` records their SHA-256 hashes.
The parity checker runs in the local suite and the Nix evidence build.

The Rocq generator replaces `generate_level1_lean.py` and its tests.
Both generators consume the same CFG and Level 1 manifest.
The Rocq output contains the same entries, PC regions, exits, counts, glue words, and fixed addresses.
Nix compares each generated Rocq file with the committed snapshot.

The following Nix outputs match the Lean repository byte for byte:

- `zesu-cfg.json`
- `flame.json`
- The Level 1 manifest
- The Level 1 boundary bindings

The old Lean report and the Rocq report differ only by the QEMU user-stack base.
`compare_level1_evidence.py` rejects every other difference.

The Rocq evidence itself is byte-reproducible.
The QEMU guest receives an empty environment, so builder variables cannot move its initial stack.
Each Nix build produces two trace sets and two reports, then requires byte equality.
`nix build --rebuild` also confirms equality with the stored output.

The Rocq repository also builds a checked viewer payload.
It contains all six boundaries, both dynamic vectors, bindings, flame data, and a speedscope profile.
The checker requires every proof status to remain `not_started`.

This parity does not validate universal paths, bounds, frames, or the semantic result relation.
The dynamic report lists these items in `unmeasuredClauses`.
