# ZesuSsz

This repository contains Rocq and Islaris proofs for the RLP decoders of stock zesu.
The target is the zesu ELF for the ZisK platform.
The reference semantics is the EVM-Sail RLP decoder.
No decoder theorem is proved yet.
The rung-1 (`decodeItem`) and rung-2 (parent header) statements are exact.
These statements bind to the selected machine code and to the generated Sail actions.

## Selected target

| Input             | Identity                                                           |
| ----------------- | ------------------------------------------------------------------ |
| zesu              | `b5483dd` (`b5483dda21d72405c50a22cb6406a1231e51a579`)             |
| Build recipe      | zesu-zkvm `be591e90`                                               |
| Compiler          | Zig `0.16.0`, ReleaseFast, `rv64im-object`                         |
| Platform          | ZisK `v1.2.0-alpha`, `fbbc69bc`                                    |
| ELF SHA-256       | `e44c18d54ae3d77832df92aceb6eb7119de8eb2e8f1f1b4e585a6e33ea04ff95` |
| EVM-Sail          | `d0e4aabd`                                                         |
| Sail compiler     | `25cc260d`                                                         |
| Proof environment | Coq 8.19 pin, Lithium `dev.2024-09-11`, Iris `dev.2024-09-10`      |

The authors' CI pins a different zesu revision (`329c0128`).
No hash comparison establishes equality with a released ELF.
`build/stock-zisk/PROVENANCE.md` records the full build inputs.

## Layout

- `ZesuSsz/Contracts/`: Level 1 resources, runtime contracts, and shared semantic interfaces.
- `ZesuSsz/Automation/`: Lithium rules, invariant support, and shared tactics.
- `ZesuSsz/Proofs/`: small block, loop, composition, and contract modules per function.
- `ZesuSsz/Compliance/`: relations to the concrete Sail decoders, and the evaluator `SailRun.v`.
- `ZesuSsz/Export/`: snapshots, the verified executor, termination support, and adequacy.
- `ZesuSsz/Evidence/`: checkers, generated obligations, signature checks, and evidence interfaces.
- `ZesuSsz/Generated/`: generated states, blocks, indexes, and tables.
- `ZesuSsz/EvmSail/`: the decoder-only Sail project, input shim, and snapshot generators.
- `generated/isla-traces/`: generated instruction semantics.
- `generated/evm-sail-coq/`: the committed Sail decoder snapshot.
- `build/stock-zisk/`: the selected ELF, build recipe, manifest, and platform records.
- `tools/stock_zisk/`: the build and platform command interfaces.
- `tools/block/`: the block runner and chain driver.
- `Scaffolding/`: theorem statements outside the production imports.

## Reproduce

Prerequisites:

- The opam switch at `~/islaris`. The Makefile uses it through `OPAM_SWITCH`.
- Zig `0.16.0` on `PATH`.
- The pinned Sail compiler. `ZesuSsz/EvmSail/Rlp/build_compiler.py` builds it.

The Nix flake stays in the repository, but it is not the reproduction path.

Run these commands from the repository root:

```sh
python3 tools/stock_zisk/build.py --check
make traces-closure-indexes
make check-fast
make check-iris
make check-signatures
```

1. `build.py --check` verifies the recipe and every declared artifact hash.
2. `make traces-closure-indexes` regenerates the stock trace indexes from the pinned ELF.
   A cold run takes about 20 minutes.
   A restore from the cache takes about 5 seconds.
3. `make check-fast` restores the indexes and builds the retained production targets.
4. `make check-iris` builds all Dune targets.
5. `make check-signatures` checks the closed theorem types and the global axioms.
   `make check-fast` also runs this gate.

The default trace cache is `_build/stock-zisk/native-trace-cache` in each worktree.
Set `STOCK_NATIVE_TRACE_CACHE_DIR` to share one cache between worktrees:

```sh
make check-fast STOCK_NATIVE_TRACE_CACHE_DIR=/path/to/shared/native-trace-cache
```

`build/stock-zisk/BUILD.md` describes the cache checks.

## What the gates prove

The gates prove that the retained modules compile.
The signature gate checks the closed types of the current Sail relations.
It also checks their global axioms against an empty library-axiom allow-list.
The gates do not prove a decoder theorem, because no decoder theorem exists yet.

Every machine proof will establish partial correctness only.
Phase 5 of the plan must prove termination with `ZesuSsz/Export/Executor.v`.

These named premises remain outside the proofs:

- Rung 2 assumes the ZisK `memcpy` service at the CSR `0x813` instruction.
  Isla has no trace for that instruction.
- Rung 3 assumes seven Sail host externs, stated in `ZesuSsz/Compliance/SailHostPremises.v`.
  No public theorem uses them yet.
- `ZesuSsz/Compliance/KnownBugs.v` lists one known bug, `RlpLongLengthWrap`.
  The binary adds long payload and header lengths modulo 2^64.
  The compliance statements permit this divergence from Sail and no other.

QEMU traces and vector audits are review evidence.
No theorem uses them as a premise.

## More information

- `docs/TRUST.md` is the authoritative trust statement.
- `docs/STARTING_POINT.md` tells a new prover where to begin.
- `docs/ai/plan/PLAN_STOCK_LADDER.md` is the active plan.
