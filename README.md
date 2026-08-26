# Zesislar

Zesislar prepares a Rocq and Islaris proof of the pinned Zesu SSZ decoder.
This repository does not contain the compliance proof yet.

## Fixed proof target

The target compares the pinned RV64IM endpoint with the EVM-Sail SSZ decoder.
It states compliance modulo seven fixed bugs.
It also states exact compliance for an input that avoids those bugs.

Six coarse contracts form the conditional proof boundary:

- `readInput`
- `allocatorGet`
- `sszDecode`
- `writeSuccess`
- `writeFailure`
- `zkvmExit`

The setup keeps these contracts coarse.
It does not copy Lean proofs or the former hLevel3 hierarchy.

## Source pins

The flake pins `binary-fv-experiment@38a3a14a`.
That source pins Zesu `d67f28c` and EVM-Sail `d0e4aabd`.
The committed decoder snapshot uses Sail `25cc260d` and SailStdpp `0.20.2`.

Nix builds the ELF.
Git does not store the ELF.
`SOURCE.json` records all generated Rocq file hashes.

## Start checks

Run these checks before proof work:

```sh
make doctor
make check-evidence-tools
make check-viewer
make check-evm-sail-snapshot
make traces
make proof
```

The Nix daemon must run for the Nix checks.

## Trust boundary

Rocq checks all theorem terms and generated Isla trace terms.
EVM-Sail defines the reference decoder action.
SailStdpp defines its prompt monad.

The proof also trusts these external components:

- The pinned Sail compiler generates the Rocq snapshot.
- Isla symbolically executes the Sail RISC-V model.
- Z3 removes infeasible trace paths.
- Islaris converts Isla traces to Rocq terms.
- Nix and the pinned Zig build produce the endpoint ELF.

The CFG, dynamic traces, contract manifest, and viewer provide review evidence.
No compliance proposition accepts this evidence as a premise.

## Layout

- `ZesuSsz/Compliance` contains the target definitions.
- `ZesuSsz/Contracts` contains the six coarse contract statements.
- `generated/evm-sail-coq` contains the pinned decoder snapshot.
- `generated/isla-traces/entrypoints` contains entry trace smoke tests.
- `ZesuSsz/Evidence` contains the evidence pipeline.
- `ZesuSsz/Viewer` contains the advanced speedscope viewer.
