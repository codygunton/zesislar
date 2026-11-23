# Proof scope of the pinned ZisK binary

This note states what the binary proofs cover and what blocks the rest.
It is part of the agent-assisted RLP plan (issue #347, task A8).

## Source

All counts come from the held-out census of the pinned ELF `build/stock-zisk/zesu-zisk.elf`:
`_build/agents/rebuild/heldout2/census-all.json` (kept by that run dir's `KEEP.json`;
SHA-256 `7de7177836abc98d800bf17f032112bbc2c8ab17704cb04d7e323d81b62cf092`).
The census script `census.py` in that directory decodes every function symbol with the repository's
own decoder and block splitter (`tools/stock_zisk/closure.py`, `analyze`), so its block counts agree
with `build/stock-zisk/cfg.json` for the closure roots.
The counts below were recomputed from the JSON file. None were copied from an earlier report.

## Functions

The census lists 527 functions, with 278,419 instructions and 35,011 basic blocks in total.

|Decoder status|Functions|
|---|---|
|every instruction decoded, every indirect jump resolved (`ok`)|300|
|every instruction decoded, at least one unresolved indirect jump|113|
|at least one instruction outside the decoder (`unsupported`)|114|

For the 114 `unsupported` functions the census records no control-flow figures (blocks, loops, calls,
indirect jumps). The counts in the next table therefore cover the other 413 functions, and each count
is a lower bound for the whole binary.

|Feature (over the 413 decoded functions)|Functions|Plan figure|
|---|---|---|
|at least one indirect jump (`jalr` other than a return)|125|125|
|at least one loop (natural-loop back edge)|98|98|
|calls at least one function without a contract|203|203|
|calls at least one function|259||
|irreducible control flow (at least one irreducible edge)|191||
|tail call|16||
|never returns (panic and assertion handlers)|13||

The plan's three figures hold. Of the 125 functions with an indirect jump, 12 have all their indirect
jumps resolved and 113 do not. The 98 functions with loops hold 1,168 loops, nested at most 5 deep.

"Without a contract" means outside the four callees that the census treats as contracted:
`rlp.decodeItem`, `rlp_decode.nextUint64` (both proved), `memcpy` (a service premise) and
`alt_fl_alloc.free` (a contract with entries only). The census sees 225 distinct callees.
The most-called are `memcpy` (148 callers), `memset` (62), a hash-map `getIndex` instance (41),
`alt_fl_alloc.alloc` (30) and `builtin.panic` (28).

Only 155 of the 300 `ok` functions have no loop and call only contracted functions (or nothing);
123 of those are leaves.

## `memset` and other platform instructions

The `unsupported` status counts, per function, instructions that the pinned Isla/Sail RISC-V model
used by the proofs does not decode:

|Instruction class|Instructions|Functions|
|---|---|---|
|CSR and system instructions|6,873|103|
|Zb or other extensions|807|25|
|compressed (RVC)|36|4|
|`ecall`|3|3|

ZisK implements its platform services as CSR accesses. The census does not split the CSR count by
service; the cases that matter for the RLP decoders are these.

- `memcpy` and `memmove` are three-instruction wrappers around one service CSR access. The trace run
  for the closure group (`TRACES-READY` of the census run) refuses the `memcpy` service instruction:
  "The pinned instruction model does not implement this ZisK service". Proofs therefore take `memcpy`
  as a premise, `memcpyCallPremise` in `ZesuSsz/Contracts/ParentHeaderMemcpyService.v`.
- `memset` has 1,036 instructions, 257 of them CSR or system instructions, and 62 callers. It is
  `unsupported` and has no premise yet. Every caller of `memset` needs one in the form of
  `memcpyCallPremise`.
- `memcmp` (one CSR instruction) and `zkvm_keccak256` (one CSR instruction, 15 callers) are in the same
  position.
- Four decoded functions read a CSR at run time (`memcpy`, `memmove`, `zkvm_bn254_pairing` and one Rust
  `alloc::vec` instance).

A service premise is trusted: it states what the ZisK service does, and no proof in this repository
checks that statement against the ZisK implementation.

## Termination

A compliance theorem is stated with `IslarisContractCorrect` (`ZesuSsz/Contracts/Level1.v`): from the
entry state, every run that reaches the exit address does so with an outcome the contract allows,
and no run faults on the way. This is partial correctness. A proved function may loop forever and
still satisfy its theorem.

Termination is a separate obligation. `ZesuSsz/Export/DecodeItemTermination.v` states the bounded-run
obligations of `rlp.decodeItem` with the executor of `ZesuSsz/Export/Executor.v`; its own header says
that it states them and does not prove them. No other function has a termination statement. Every
function with a loop (at least 98) needs a measure per loop for a termination proof; the loop
assertions of the block proofs do not supply one.

## Recompilation

All proofs are pinned to one ELF. The Isla traces are generated per instruction at its absolute
address, and contracts, selected code and generated block statements name entry, exit and call
addresses. A recompilation that moves code invalidates the traces and every statement that names a
moved address, even when the function's instructions did not change. A change of the Zig source,
the Zig compiler or the link order changes the layout.

Today the repair is regeneration followed by a rerun of the proofs. Issue #348 ("Relocatable proofs")
records the work that would make that repair mechanical: symbol-relative names in hand-written files,
symbolic address notations (`tools/oblig/render_symbols.py`), the existing absolute-address matches in
the files of the three proved functions, and a relink drill.

## The largest functions

By instruction count (blocks, loops, calls and indirect jumps as the census reports them; frame in
bytes):

|Function|Instructions|Blocks|Loops|Calls|Indirect jumps|Uncontracted callees|Frame|
|---|---|---|---|---|---|---|---|
|`transition.transitionWithContext__anon_2321`|18,413|2,690|0|372|63|37|2,032|
|`sort.block.block__anon_11541`|13,500|2,183|61|81|2|3|2,032|
|`sort.block.block__anon_10892`|13,365|1,665|57|82|2|3|2,032|
|`sort.block.block__anon_7840`|12,545|1,445|57|82|2|3|2,032|
|`main.executeBlockStateless`|12,192|1,706|31|179|70|35|2,032|
|`transition.BaTracker.computeHash__anon_5051`|12,134|2,601|124|81|52|11|2,032|
|`sort.block.block__anon_8211`|10,750|1,594|96|20|1|2|2,032|
|`sort.block.block__anon_8316`|10,298|1,605|93|21|1|2|2,032|
|`sort.block.block__anon_12614`|9,978|1,300|148|20|1|2|2,032|
|`sort.block.block__anon_9057`|8,773|895|74|235|2|4|2,032|
|`interpreter.runDispatch__anon_13271`|7,710|1,328|0|34|178|1|1,008|
|`mainnet_builder.ExecuteEvm.execute__anon_3724`|6,484|1,198|6|91|3|29|2,032|

For comparison, the three proved functions have 116 (`rlp.decodeItem`), 53 (`rlp_decode.nextUint64`)
and 367 (`rlp_decode.decodeParentHeader`) instructions.
