# Trust boundary

Rocq checks each completed theorem term. The current restart work has no completed
rung-1 compliance theorem. Its decoder result types are candidates until the user
selects decision C1. Machine proofs establish partial correctness only. Phase 5 of the
active plan must prove termination with the verified executor in `ZesuSsz/Export/Executor.v`.

## Selected artifact and machine semantics

The selected stock ELF has raw SHA-256
`e44c18d54ae3d77832df92aceb6eb7119de8eb2e8f1f1b4e585a6e33ea04ff95`. The authors' recipe
(zesu-zkvm `be591e90`, Zig 0.16.0, ReleaseFast, `rv64im-object`) builds it from unmodified
zesu `b5483dd`; `tools/stock_zisk/build.py --check` verifies the recipe and every declared
hash. The machine contracts use its instruction bytes, entry points, return sites, and
memory map. Isla symbolically executes the pinned Sail RISC-V model with a ZisK platform
layer. Z3 removes infeasible paths. Islaris translates the traces into Rocq. The final
claim depends on the correctness of these tools and of the selected platform model.
An empty axiom list does not verify the Isla-to-Sail connection.

## Reference semantics

The pinned EVM-Sail revision is `d0e4aabdde52f9158d191dbc8add444abffd9a6a`. The pinned
custom Sail compiler is `25cc260d9940d65d2e5da427fe4b5d402809a50c`. The committed
decoder-only snapshot under `generated/evm-sail-coq/rlp/` covers the first two decoder
rungs. Its input shim (`ZesuSsz/EvmSail/Rlp/shim/input.sail`) defines byte access,
big-endian word loads, zero padding past the slice end, and assertion failures for
invalid direct access. The evaluator `ZesuSsz/Compliance/SailRun.v` runs `sail_model_init`
before it installs input bytes. It marks `Fail "exit"` as RLP rejection only under six
audited entry actions and 16 pinned fatal-error sites. It marks other failures, choices,
and unsupported host effects as `UnsupportedOrInternalFailure`. A Rocq lemma connects
supported evaluator outcomes to `liftState`. The generated rung-1 and rung-2 snapshot
contains no input-extern axioms.

## Gates

The signature gate (`make check-signatures`, inside `make check-fast`) checks the closed
types of the four current Sail relations. A Rocq plugin checks their global axioms against
an empty library-axiom allow-list; runtime premises are listed separately from global
axioms. The gate does not yet check a compliance theorem because none exists. Every later
public theorem needs its own reviewed closed type and axiom check.

The rung-3 transaction snapshot declares seven approved C4 host extern axioms.
`SailHostPremises` states their required completion, return values, scratch changes,
input preservation, and unrelated-state preservation. It treats the digest function
as an explicit assumption; this work does not verify Keccak-256. The uncached
`check_sail_host_axioms.py` gate checks the exact names in each of the six generated
roots, separately from the empty library-axiom allow-list. The generated roots have
no Dune theory mapping, and their monadic externs are not yet connected to the
standalone host-state relations. No closed rung-3 compliance type exists yet, so no
public theorem consumes these premises. A reviewed type, generator binding, and
separate axiom gate for that theorem remain required.

## Known limits

The bounded record-extraction experiment crossed the 2 GiB module limit. A second,
typed seven-field prefix handoff compiled the complete blob decoder below that limit.
The staged source inlines exactly to pinned `decode_blob_tx`; the pinned source did not
change. `BLOB_HANDOFF_EXPERIMENT.json` records the generation method and measurements.
The committed rung-1/2 snapshot still excludes the blob decoder. The full transaction
decoder, keccak operations, scratch operations, and their host assumptions remain outside
the current executable reference boundary. The C1 wrap decision and the later
transaction-domain decisions remain open.
No present result claims unconditional binary equality with Sail.

QEMU traces and vector audits are evidence for review. They are not premises in a machine
or compliance theorem. The vector audit executes Sail RLP actions only. It does not execute
the selected ELF or establish complete transaction behavior.
