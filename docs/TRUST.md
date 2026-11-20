# Trust boundary

Rocq checks each completed theorem term. The rung-1 compliance theorem for decodeItem,
`decodeItemSelectedCompliance` in `ZesuSsz/Compliance/DecodeItemCompliance.v`, is complete.
It rests on these proofs, and on no axioms (`Print Assumptions`: "Closed under the global
context"):

- the 24 generated block proofs, one per basic block, each `zesu_block2. Qed.` against its
  generated entry (`tools/block/generated/fp301_callers`, compiled as
  `ZesuSsz.Proofs.DecodeItem.FP301.Caller*`), composed over the Automation2 block table in
  `ZesuSsz/Compliance/DecodeItemGeneratedComposition.v` and stated in
  `ZesuSsz/Compliance/DecodeItemComplianceGenerated.v`;
- the ported meaning lemmas in `ZesuSsz/Compliance/DecodeItemMeaningPorted.v`, which give
  the output meaning at the six return blocks;
- the residual lemmas in `ZesuSsz/Residuals`, pure lemmas that close the goals the
  automation leaves open; a model wrote their proofs, and Rocq checks them like any proof.

The registers and compositional variants in `DecodeItemCompositionalCompliance.v` rest on
the same chain. The October block, slot and composition proofs are retired. Some October
fact modules remain because the block design binds them as sources, the generated support
files import them, or nextUint64's frozen-core exit meanings use them; no production theorem
uses them. The user selected C1-B: the public result records exact
machine bytes. For decodeItem it permits only the named `RlpLongLengthWrap`
divergence from Sail; a wrap case requires the exact binary result and Sail
rejection. `KnownBugs` lists ten classes. Each names an input class, what the binary
does on it, and what Sail does:

- `RlpLongLengthWrap`: an item whose long header and payload lengths add to 2^64 or
  more; the binary adds them modulo 2^64 and goes on; Sail rejects the item.
- `ParentHeaderMissingRequiredField`: a header list with fewer than twelve fields; the
  binary rejects it; Sail accepts any field count.
- `ParentHeaderTrailingBytes`: bytes after the outer header list; the binary ignores
  them; Sail rejects the input.
- `ParentHeaderSkippedFieldShape`: a parent hash or state root (fields 0 and 3) that is
  a list or a string longer than 32 bytes; the binary skips it; Sail rejects it.
- `ParentHeaderBlobGasUnaligned`: a blob gas used (field 17) that is not a multiple of
  2^17 or counts more than 21 blobs; the binary returns it; Sail rejects it.
- `RlpUintNonCanonical`: a base fee, blob gas used or excess blob gas (fields 15, 17,
  18) of at most 8 bytes with a leading zero or a non-canonical header; the binary
  reads its value; Sail rejects it.
- `ParentHeaderUintOver8`: a canonical base fee of 9 to 32 bytes; the binary rejects
  it; Sail accepts it as a 256-bit value.
- `ParentHeaderUndecodedFieldRejected`: a gas limit, gas used or timestamp (fields 9 to
  11) that is a list or longer than 8 bytes; the binary rejects it; Sail skips it.
- `ParentHeaderExcessBlobGasAboveLimit`: an excess blob gas (field 18) above
  2,992,193,280; the binary returns it; Sail rejects it.
- `ParentHeaderTrailingItemMalformed`: an item after field 18 inside the header list
  that does not decode; the binary never reads it; Sail rejects the input.

The decodeParentHeader meaning
(`ParentHeaderRung2.v`) requires the exact result of the candidate function
`candidateParentHeader` (`Contracts/Candidates/ParentHeaderCandidate.v`), which
follows the machine code, and then either Sail's agreement with that candidate or
a boolean trigger of a listed class on the input bytes
(`Contracts/ParentHeaderBugTriggers.v`). The candidate is pinned to the ELF by
emulation vectors (`Evidence/ParentHeaderCandidateVectors.v`), which are test
evidence. The decodeParentHeader domain (`parentHeaderArgsWellFormed`)
requires the outer header to fit (`headerFits` of the whole input). The code checks the
first item only for an error, the list flag and a nonzero payload length; it never checks
that payload against the input. An outer long-list length that wraps 2^64 therefore passes,
and the later decodeItem calls read outside the input (`0xff` followed by eight `0xff`
bytes is one such input). That input class is outside the decodeParentHeader theorem.
A nested wrap uses the same known bug on the
reached slice. The candidate reached-slice walk needs machine-call correspondence
before a proof can use it. Machine proofs establish partial correctness only. Phase 5 of the
active plan must prove termination with the verified executor in `ZesuSsz/Export/Executor.v`.

`parentHeaderGeneratedCompliance` in `ZesuSsz/Compliance/ParentHeaderGeneratedComposition.v`
derives `ParentHeaderContractCorrect` from two premises: `NextUint64ContractCorrect` and
`ParentHeaderOpenBlocks`, a record with one field per decodeParentHeader block whose proof is
not closed (generated in `ParentHeaderBlockObligations.v` by
`tools/block/render_open_blocks.py`). It is not an unconditional result: `ParentHeaderOpenBlocks`
is the remaining work. `NextUint64ContractCorrect` is proved without premises by
`nextUint64Compliance` in `ZesuSsz/Compliance/NextUint64GeneratedComposition.v`; its contract
code is nextUint64's own map and decodeItem's map. The memcpy runtime premise enters through the
contract code (`memcpyCallPremise`), as `ParentHeaderContractCorrect` states it.

A block leaves that record only with a closure certificate,
`tools/block/closures/<callers directory>/<block>/CLOSURE.json`, written by
`tools/closure_cert.py`. The certificate binds the unmodified generated caller at a head that
precedes the record, coqc's own exit status 0, the `-time` records of the theorem's `Qed` and of
its `Print Assumptions` ("Closed under the global context"), and a bank whose load path holds
only that head's sources (no tactic redefinition from elsewhere). The renderer refuses a closed
block without one. Check-iris still compiles every closed caller on the merged head.

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

## Initial platform registers

The selected platform uses the following proof-entry assumptions.
The reset configuration emits `AssumeReg` events.
It does not create register ownership or prove loader initialization.
`machine_ram_sys_regs_init` consumes the corresponding owned values and the MPRV condition.

| Register | Entry value and reason | Exact proof-entry locations |
| --- | --- | --- |
| `cur_privilege` | `Machine` selects the platform's only privilege mode. | `ZesuSsz/Contracts/Machine.v:defaultMap.mapPrivilege`; `InstrSpecs/Machine.v:machine_static_sys_regs`; `ZesuSsz/Export/Adequacy.v:machine_static_sys_regs_map` |
| `misa.bits` | `0x8000000000001100` selects RV64IM and excludes compressed instructions and lower privilege modes. | `ZesuSsz/Contracts/Machine.v:defaultMap.mapMisa`; `InstrSpecs/Machine.v:machine_static_sys_regs`; `ZesuSsz/Export/Adequacy.v:machine_static_sys_regs_map` |
| `mtvec.bits` | `0` retains the existing platform trap-vector assumption. | `ZesuSsz/Contracts/Machine.v:defaultMap.mapMtvec`; `InstrSpecs/Machine.v:machine_static_sys_regs`; `ZesuSsz/Export/Adequacy.v:machine_static_sys_regs_map` |
| `mstatus.bits` | `(bits & 0x20000) = 0` clears MPRV and retains physical data addressing. Other bits remain symbolic. | `ZesuSsz/Contracts/Machine.v:defaultMap.mapMstatusMask/mapMstatusValue`; `InstrSpecs/Machine.v:machine_static_sys_regs`; `ZesuSsz/Export/Adequacy.v:machine_ram_sys_regs_init.Hstatus` |
| `medeleg.bits` | `0` explicitly excludes exception delegation and removes redundant forks before the pinned privilege clamp. | `InstrSpecs/Machine.v:machine_static_sys_regs`; `ZesuSsz/Export/Adequacy.v:machine_static_sys_regs_map` |
| `mideleg.bits` | `0` explicitly excludes interrupt delegation to an unused lower privilege mode. | `InstrSpecs/Machine.v:machine_static_sys_regs`; `ZesuSsz/Export/Adequacy.v:machine_static_sys_regs_map` |

`ZesuSsz/riscv64_zesu.toml` supplies these reset values and the MPRV constraint.
`tools/machine_config.py` checks them against the machine map and the fixed delegation resources.
The delegation values are explicit platform assumptions, not inferred loader guarantees.

The RISC-V manual's `src/priv/machine.adoc` states that traps never move from a more privileged mode to a less privileged mode.
See [Machine Trap Delegation Registers](https://github.com/riscv/riscv-isa-manual/blob/main/src/priv/machine.adoc#machine-trap-delegation-medeleg-and-mideleg-registers).
The pinned `exception_delegatee` reads `medeleg` before it clamps the result to the originating privilege.
The platform snapshot has SHA256 `2b1b3c9eeae6fc53ea430376c9759a9abd0d1f8e123362078800642d4b5eec8e`.
Its `zexception_delegatee` body matches the pinned base snapshot exactly.
The configuration does not fix the complete `mstatus` value.

## Per-access trace constraints

Source-bound region annotations become `Assume` events in the generated traces.
Each instruction proof must discharge the condition through Islaris `wp_assume`
(`theories/lifting.v`) and its automation rule `li_wp_assume`
(`theories/automation.v`).
The annotations create proof obligations, not additional contract premises or established memory bounds.
The unsigned eql group constrains all 46 memory accesses, including four stack loads.
The group has no region-constraint exemptions.
The unsigned `decodeItemRegions` group constrains all 50 memory accesses: 15 loads and 35 stores.
All 50 constraints remain open Islaris `wp_assume` obligations.
The group has no region-constraint exemptions.

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
axioms. The decodeItem compliance theorem has a reviewed closed type: the Scaffolding
signature files built by `make check-signatures` compare `ReviewedDecodeItemComplianceType`
with `DecodeItemComplianceStatement` by `eq_refl`. The PUBLIC soundness gate
(`tools/soundness_gate.py`, `docs/SOUNDNESS_GATE.md`) checks the four PUBLIC theorems with an
empty axiom allow-list and recursive `coqchk`. Every later public theorem needs its own
reviewed closed type and axiom check.

The PUBLIC soundness gate (`tools/soundness_gate.py`, `docs/SOUNDNESS_GATE.md`) compiles
the PUBLIC theorem files fresh and checks that each fresh object equals the object in
`_build`. It takes their dependency objects from the Dune cache, runs
the five negative controls and the statement and wrapper checks, and re-checks every object
with recursive `coqchk`. `coqchk` re-checks cached objects against the kernel, but it does
not compare an object with its source, so the meaning of a cached dependency definition
rests on the integrity of the local Dune cache.

The user approved seven named C4 host premises for the rung-3 transaction snapshot.
Its generated roots declare those seven host extern axioms.
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
the current executable reference boundary. The later transaction-domain decisions
remain open. Rung-2 rejection agreement also needs a decision for truncated headers:
Sail can accept a truncated header that the selected binary rejects.
No present result claims unconditional binary equality with Sail.

QEMU traces and vector audits are evidence for review. They are not premises in a machine
or compliance theorem. The vector audit executes Sail RLP actions only. It does not execute
the selected ELF or establish complete transaction behavior.

## Rung 2 runtime premise and call records

Rung 2 models the reachable parent-header memcpy call as an 80-byte copy from
`0x80114fb8` to the result buffer. The service also writes the count to eight scratch
bytes at `0xa0400f00`. The selected index commits the CSR 0x813 bytes at `0x800e06c0`,
but Isla has no trace for that instruction. The closed code resource therefore assumes
the named persistent `instr_pre` service premise at that PC. This premise uses
`ZiskRuntime.ziskMemcpyAllows` and returns control to the recorded caller address. The
runtime premise is separate from the empty library-axiom allow-list. Separate source,
destination, and scratch ownership excludes overlap; the generic overlapping-copy
behavior is outside this rung-2 premise. No Rocq proof establishes this ZisK runtime
behavior.

The selected call records carry `s0`-`s4` for `nextUint64` and `s0`-`s8` for
`decodeParentHeader`. The parent-header record also carries its 400-byte frame and exact
source and scratch snapshots. These values make ABI preservation and memory framing
explicit within the existing Level 1 resource interface. They are not public outputs.
The rung-2 compliance propositions are statements only; no machine proof or termination
proof discharges them. A later proof must establish the memcpy return alignment and
instantiate its runtime permissions.
