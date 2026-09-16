# Push 3 main progress

## Remaining work

Phase 4b.1: The 24 glue instruction proofs and their trace evidence are complete.
Phase 4b.2: The whole Main Iris theorem and contract correctness theorem are complete with the approved concrete decoder and fixed-tail writer hypotheses. Both outcomes reach exact physical terminal resources at 0x101d0. CP3 blocks writer instantiation and adequacy.
Phase 4b.3: Apply adequacy after CP3. The orchestrator owns the compliance files.

## Plan deviations

- Git forbids `islaris-native/main` because `islaris-native` already exists. The orchestrator assigned `islaris-native-main`.
- The worktree omitted ignored build links and traces. I linked unchanged traces from the integration worktree.
- The existing Shell.v uses placeholder main/decode resources. The orchestrator approved exact resource corrections.
- The orchestrator corrected `zesuSuccessArgs.successDecodedAddress` to `decodeStackPointer + 32`. The input address names the input buffer.
- Rocq MCP reports `No node at point`. I use the authorized scratch compiler.
- The shared Dune update awaits the initial gate. Scratch files copy exact raw traces to avoid changing the shared Dune file.

## Measurements

- New main trace generation uses the unchanged allocator config. The new dump selects 24 instructions and one branch.
- Main generated traces: exit 0, 2.717 seconds, 583116 KiB, 16 workers.
- Main initial resources: exit 0, 1.884 seconds, 609924 KiB, 16 workers.

## Checked glue proofs

All 24 glue instructions now have native block proofs.
Every block has an unframed theorem and a theorem that preserves an arbitrary Iris frame.
Every checked theorem prints `Closed under the global context`.
The shared gate must pass before the track commits these modules.

- `main_prologue_correct_with_frame`: scratch exit 0, 15.551 seconds, 1321124 KiB.
- `main_decode_call_correct_with_frame`: scratch exit 0, 3.656 seconds, 712860 KiB.
- Four framed outcome/exit calls: scratch exit 0, 3.404 to 3.745 seconds, at most 736396 KiB.
- `main_dispatch_success_correct_with_frame`: scratch exit 0, 7.969 seconds, 813012 KiB.
- `main_dispatch_failure_correct_with_frame`: scratch exit 0, 8.043 seconds, 819792 KiB.

## Integration dependencies

The orchestrator approved an arbitrary Iris frame in the generic block statements.
The frame occurs in each entry and exit resource.
The public contracts and their allows remain unchanged.

The existing exit store trace requires a different RAM configuration.
The orchestrator requested approval for one new trace at `0x101cc`.
The failure adapter can reuse the existing prefix and the compatible output traces from `write_success_01`.
The user excluded the decoder region from every theorem.
The decoder-table request is withdrawn.
Compliance retains the named `decodeOk` hypothesis.

## Binding boundary conflict

The plan maps decode exit resources directly to the next endpoint entry.
The consumed decode exit PC is `0x14cfc`.
A successful decoder return leaves `x1 = 0x14cfc`.
The writeSuccess entry requires `x1 = 0x14d10`.
The glue establishes that value at `0x14d0c`.
The failure entry instead requires `x1 = 0x14d24`.
The glue establishes that value at `0x14d20`.
The direct equality is false at the consumed decode exit boundary.
The orchestrator requested approval for dispatch resources at that boundary.
The frozen decode allows remains unchanged.

## Paused handoff

The orchestrator paused composition under section 5.5.
Nine files remain staged and uncommitted.
Seven files live under `ZesuSsz/Proofs/Main/`.
The other files are `experiments/islaris-main/profile.json` and `main.dump`.
The generated main traces remain ignored and reproducible.

The complete compatible failure theorem is `main_failure_trace_correct`.
Its scratch compile passed in 1.744 seconds at 722612 KiB.
Its focused Dune build passed in 2.489 seconds at 721812 KiB.
The prefix build passed in 4.801 seconds at 759016 KiB.
Rocq final compilation passed both failure modules.
Rocq verification returned no assumptions for both failure theorems.
Rocq compiled directly with coqc because its Dune fallback rejected the external build layout.
The `_build/default` symlink points to `agents/main/default` for the Rocq load paths.
All compilation artifacts remain inside the main build directory.

Resume after the shared Dune/hash-split commit and the user rulings.
The pending decisions cover the direct decode boundary and the new `0x101cc` trace.
The track must run `make check-fast CHECK_AGENT=main AGENT_JOBS=16` before each commit.
The track will commit the glue unit before the compatible failure adapter.

The user requires the named `decodeTerminates` hypothesis for termination.
The main track will use the decoder contract only.
The decoder region remains outside this track.

### Canonical config endpoint work

The user approved canonical `riscv64_zesu.toml`. New writeFailure and zkvmExit traces use RAM base `0x20000000` and size `0x20000000`. The binary, Islaris, and generator remain unchanged. Existing traces were not edited. The new trace directories replace local symlinks with local directories. Root owns integration copies and old config removal.

Canonical trace gate: 1.405 s, 583068 KiB, j16. `zkvm_exit_state_correct` scratch: 3.379 s, 743172 KiB. `write_failure_state_correct` scratch: 6.490 s, 872456 KiB. Both use `zesu_block`. ZkvmExit selects the final existential witness with the approved `liInst`, then `zesu_run`. Both print `Closed under the global context`.

The approved failure postcondition retains `failureMemory`. Its snapshot output lemma scratch passed: 4.681 s, 779240 KiB. Its arbitrary-frame prefix passed: 3.378 s, 743236 KiB. The canonical ZkvmExit tail contract preserves arbitrary frame `P` and `spec_trace tail`; scratch passed: 3.352 s, 744360 KiB, closed. The WriteFailure tail factory composition remains under check.

Rocq MCP compiled both complete canonical endpoint modules successfully. It used direct coqc fallback because its Dune layout lacks this worktree's external theory wiring. It wrote artifacts through `_build/default` into `_build/agents/main/default`. Focused Dune endpoint gates also passed. Final assumption audits and the mandatory fast gate remain before commits.

The user approved decoder dispatch resources. Root approved fixed saved registers and padding in `DecodeBoundaryArgs`. The same args must index both entry and exit resources. Decoder caller-clobbered a0/a1/a2 and its allocator pair are existential. Main's `lhu` loads branch status from object tag memory at `sp+880`; the contract does not assume a decoder status return in a0. The complete factory remains under shared review. Decoder traces and proofs remain out of scope.

The Main profile now uses the canonical config. The generated dump moved from `experiments/islaris-main/main.dump` to ignored `build/islaris-dumps/main.dump`. Only the Main profile will enter its commit.

The final WriteFailure tail factory scratch passed: 7.158 s, 865484 KiB, closed. Explicit tail/frame arguments avoid slow unification in the obsolete attempt. Root and main stopped its remaining scratch process before the 300-second limit. Rocq verification returned `assumptions: []` for both endpoint tail contracts. The combined Main glue and endpoint tail gate passed: 67.511 s, 1532132 KiB, j16. Main now uses aliases to the canonical failure factory and its five output instructions. Root approved this statement correction.

Commit `a77ec8e`: Phase 2 canonical writeFailure and zkvmExit contracts. Mandatory `make check-fast CHECK_AGENT=main AGENT_JOBS=16` passed: 314.083 s, 2619332 KiB. Both state theorem assumption audits print closed. Both tail theorem Rocq audits return no assumptions. Root must copy the two new canonical trace directories before its merge preview.

Rebase onto `a5637e48` changed endpoint commit `a77ec8e` to `77019c6f`; its proof code is unchanged. Root will preview the new branch tip. The corrected shared factory `/tmp/DecodeMachine.v` passed its type check. Entry fixes input a2/a3 and allocator words from args. Exit preserves indexed saved registers and padding and returns existential allocator words. Root approved the fixed union tail and `spec_trace_mono` selection after the decoder outcome. Root will copy the factory into `Contracts/DecodeMachine.v`.

The generic frame wrapper and `IslarisContractSpec_frame` are closed. Scratch: 1.252 s, 682416 KiB. Rocq verification returned no assumptions. Root approved `Contracts/Frame.v`. Main will reuse the exact readInput contract through this wrapper. The framed allocator adapter uses the existing eight traces. Scratch: 11.752 s, 1020584 KiB, closed. Its focused Dune build passed. No allocator traces were generated again.

Commit `dc414045`: Phase 4b.1 framed Main glue and canonical endpoint adapters. The block proves 24 Main instructions and eight allocator instructions from existing traces. It preserves arbitrary frames. Its canonical failure aliases use ten instructions. It removes the unused WriteSuccessOutput import. It tracks only the canonical Main profile. The dump stays ignored. The final focused gate passed: 3.296 s, 718268 KiB. Mandatory fast gate passed: 1.793 s, 1148952 KiB. Prologue and Dispatch Rocq audits returned no assumptions. The first Dispatch audit used an incorrect theorem name; the corrected name passed. All proof statements remain unchanged.

The fixed union and both outcome-selection subset lemmas are closed. Both `spec_trace_mono` selection lemmas are closed. Scratch: 2.003 s, 1113196 KiB. Rocq verification returned no assumptions. Root approved the actual exit-tail index. The updated shared factory requires the native witness tail to equal `successExitTail args`. Its type check passed: 1.002 s, 1056176 KiB. Root will apply its exact text.

Commit `f0ad73fe`: Phase 4b.2 fixed decode union tail and writer selection. The two subset proofs and two selection proofs print closed assumptions. The union includes exact success and failure exit tails. It does not select an outcome at entry. Rocq verification returned no assumptions. Focused Dune gate: 3.244 s, 1110744 KiB. Mandatory fast gate: 0.518 s, 133800 KiB, j16. Root accepted the commit for the same preview as Main glue. Main composition awaits the shared factory commit and its concrete heap/frame instantiations.

Rebase onto `1d91f274` changed Main commits to `60deb829` and `7e2de2d8`. Root received both identifiers. The pinned allocator word remains zero. The pinned heap base is `0x1a000`. Root escalated its conflict with the successful high-RAM heap bounds. Main does not change these bounds or the configuration.

The physical input projection reads the eight-byte size word at `0x2401a0b8` and the buffer at `0x2001a000`. Its range lemma proves that recovered bytes lie in `[0,256)`. Its roundtrip lemma reconstructs the physical bytes through `readInputMemory`. Both scratch proofs passed. Rocq compiled the module and verified both lemmas without assumptions. No byte-range premise or change to `InputWithinBound` was added.

The failure finish contract composes three checked Main instructions and the three checked canonical exit instructions. It preserves the failure payload, caller frame, output MMIO range, exit MMIO range, and trace tail. The exit code is zero. Scratch: 5.006 s, 823184 KiB. The focused two-module build passed: 5.798 s, 823748 KiB, j16. Rocq compiled and verified the finish theorem without assumptions. The initial scratch check found stale dependency assumptions after rebase. The refreshed dependency build passed: 30.567 s, 1310008 KiB.

The trace input projection finds the first trap snapshot with a recoverable input image. Its range lemma is closed. Scratch: 0.751 s, 632220 KiB. Rocq verified this lemma without assumptions. Final snapshot focused gate: 2.026 s, 631672 KiB. The full fast gate passed: 205.397 s, 2704880 KiB, j16. The final cached fast gate passed: 0.634 s, 132508 KiB, j16. An attempted focused build during the first gate hit the Dune lock. The sequential focused retry passed.

Commit `40a42efb`: Phase 4b.2 physical input projection and failure finish. All four lemmas print closed assumptions. Root received the commit and the exact Shell projection alias request. The failure finish covers six instructions through the canonical exit store. Main now prepares the complete failure call and output composition. The successful Main path still waits for the pinned heap ruling.

The complete failure outcome contract covers `0x14d1c` through `0x101d0`. It composes two Main call instructions, ten canonical failure instructions, and six finish instructions. Its entry owns the actual register and memory resources. Its exit retains the payload, frame, and trace tail. It changes no existing public allows. Scratch: 6.758 s, 906248 KiB. Focused gate: 7.411 s, 908032 KiB. Rocq compiled and verified the theorem without assumptions. Mandatory fast gate passed: 0.480 s, 133584 KiB, j16. Root received the factory review request.

Commit `09682fa3`: Phase 4b.2 complete failure writer and terminal exit composition. Root received its closed statement and gate measurements. Root must review the new region-local factory before integration. Main requested the next status-dispatch composition. That composition preserves status memory through the terminal exit. Main awaits the factory ruling before this next proof.

Root merged Main commits through `09682fa3` after its green preview. Root approved the failure outcome factory and the status-dispatch composition. Main read the complete ruling dispatch and the central `MachineMap` schema. Main stops proof work until the map commit, matching traces, and a gate slot arrive.

Initial-resource proposal: load the pinned PT_LOAD file bytes and zero NOBITS bytes. Overlay only the approved host input and its size word. Add a disjoint external stack window `[sp-2896,sp)`. The decoder frame pointer is `sp-896`. The stack pointer remains a contract parameter. Shell selects a valid disjoint parameter. This proposal adds no premise to `InputWithinBound`.

Pinned data evidence: the two .sdata words at `0x19000` are `0x2001a000` and `0x1a000`. The allocator-state word at `0x2401a0b0` is zero. The 32 vtable bytes at `0x177a8` encode `0x15ffc`, `0x15d40`, `0x15d38`, and `0x15a14` in little-endian order. Main read only these ELF data bytes. Main inspected no decoder trace or instruction.

The proposed decoder heap entry owns `[mapHeapBase,mapHeapEnd)`, the zero state word, and the two pinned .sdata words. The initial heap image is zero. The contract can forget these zeros to uninitialized heap ownership. The failure heap exit owns the same extent with arbitrary bytes and existential returned global words. The preserved frame owns active input bytes, the size word, pinned vtable bytes, failureMemory, and the exit MMIO range. The shared factory already owns the output MMIO range, object/frame/scratch memory, registers, and trace tail. The proposal does not duplicate object memory. Main keeps the 512 MiB heap list symbolic and does not compute it.

Root approved the corrected initial stack window of 2976 bytes. Let `D=decodeStackPointer`. The lower scratch regions are `[D-2080,D-2048)` and `[D-2048,D-2000)`. The private region is `[D-2000,D-104)`. Writer scratch is `[D-104,D)`. Main frame is `[D,D+896)`. The previous 2896-byte proposal omitted the lower 80 bytes returned through `NativeDataResources`.

The exact uncompiled factory request is `/tmp/main_decode_image_resources_request.v`. Decoder heap entry owns the pinned globals, heap extent, lower 80 bytes, and `NativeStaticResources`. Failure heap exit returns arbitrary global values, the same heap extent, lower 80 bytes, and `NativeStaticResources`. The preserved frame contains input bytes, size word, vtable, failureMemory, and exit MMIO. It excludes the output range and `NativeStaticResources`. Success obtains the lower 80 bytes and static header through `NativeDataResources`. Main sent all fixed disjoint intervals and the five stack intervals to root. Main edited no shared file and ran no build or commit.

The approved failure-after-decode composition is closed in `Main/FailureAfterDecode.v`. Its statement is `IslarisContractSpec 0x14cfc 0x101d0 (fun _ _ => True) (mainFailureAfterDecodeResources tail sp ra status P)`. The entry requires nonzero status, dispatch memory, and failure entry resources. The exit retains dispatch memory through the complete failure outcome. It uses the two real dispatch instructions and the closed failure outcome. No instruction proof is duplicated.

The initial scratch check found a stale `Dispatch.vo` dependency. Root approved its artifact refresh. That focused dependency refresh passed: 22.902 s, 1233120 KiB, j16. The new lemma then passed scratch: 5.004 s, 822300 KiB. Rocq compiled and verified it without assumptions. `Print Assumptions` reports closed. Root approved the closed block. The MachineMap migration, final gate, and commit remain pending publication. Main generated no trace.

Native worker exec performed this bounded Main handoff because the thread limit prevents resuming main.
The worker preserved the exec worktree without edits.
The worker stashed Main's untracked proof, rebased onto `97e2729d`, and restored the proof unchanged.
The assigned fast gate passed: 629.144 s, 2591680 KiB, j16, cache enabled.
The focused failure and dependency build passed: 35.823 s, 1379488 KiB.
The final cached fast gate passed: 0.633 s, 134548 KiB.
Commit `8a7572da` closes the approved failure-after-decode block.
Its statement and proof remain unchanged from the approved draft.
`Print Assumptions main_failure_after_decode_state_correct` prints closed.
MCP final compilation found the missing shared MachineMap mapping.
Root accepted the focused kernel audit and will add that mapping.

The exact concrete decoder-call adapter is in `Proofs/Main/DecodeEntry.v`.
Root approved its complete frame and its exact concrete exit at `0x12168`.
The existing helper requires an unguarded target body.
The contract exit supplies a guarded target continuation.
The adapter therefore proves its four Main instructions directly with `zesu_block`.
The scratch passed: 6.007 s, 1164056 KiB.
`Print Assumptions main_before_decode_call_state_correct` prints closed.
The adapter preserves both supplied trace tails.
It consumes no decoder trace or instruction.
The external initial stack window remains the approved 2976 bytes.

Commit `3dbcc3df`: Phase 4b.2 exact concrete decoder entry.
The theorem is `IslarisContractSpec 0x14cec 0x12168 True` for `mainBeforeDecodeCallResources`.
Its exit is exactly `islarisEntry (mainDecodeConcreteResources decodeTail successExitTail) args`.
Its four Main instructions preserve every other concrete entry resource.
The focused Dune check passed: 7.621 s, 1166376 KiB, j16, cache enabled.
The final fast gate passed: 0.547 s, 132760 KiB, j16.
`Print Assumptions main_before_decode_call_state_correct` prints closed.
MCP final verification waits for Root's shared MachineMap load-path commit.
The native kernel checks passed against the published map and refreshed traces.
The bounded Main assignment ends here, as Root instructed.
All Main scratch drafts remain in the Main build directory.
The exec worktree remains unchanged.
Next Main step: compose prologue, framed readInput, and allocator setup into this exact boundary.
The successful post-decoder composition still waits for CP3.

### Main prefix composition

The native exec worker resumes Main on 07046724.
The exec and port worktrees stay unchanged during this assignment.
Root approved a local mainPrefixResources boundary from 0x14cb0 to 0x14cec.
Its exit equals the committed DecodeEntry entry.
The entry preserves the complete concrete heap, frame, and approved tails.
The stack window stays 2976 bytes.
The existing input bound stays unchanged.
No decoder instruction or trace enters this proof.

The framed readInput factory reuses read_input_state_correct.
Its entry and exit add the same arbitrary Iris frame P.
Scratch: 2,753 ms, 726,168 KiB peak RSS, exit 0.
Print Assumptions main_read_input_framed_state_correct prints Closed under the global context.

The original allocator helper requires an unguarded terminal body.
Root approved a local guarded contract with the same entry and exit resources.
The proof uses the same eight allocator instructions and zesu_block.
Scratch: 20,022 ms, 1,274,660 KiB peak RSS, exit 0.
Print Assumptions main_allocator_guarded_state_correct prints Closed under the global context.

Two arithmetic helpers recover bounded stack addresses and the input size word.
Each proof uses no more than four arithmetic lines.
Scratch: 1,502 ms, 635,548 KiB peak RSS, exit 0.
Both helpers print Closed under the global context.

The foundation fast gate passes in 214,599 ms at 2,689,496 KiB peak RSS.
The dependency refresh passes in 31,770 ms at 1,464,744 KiB peak RSS.
The build uses the assigned Main directory, the shared cache, and 16 workers.

The guarded adapter block committed as fcca89a3dd63a2ac60e8ffe4bd83c30f1bbbbc8b.
Its focused build passes in 23,395 ms at 1,225,944 KiB peak RSS.
Its final fast gate passes in 504 ms at 138,476 KiB peak RSS.
MCP compiles all three modules and verifies both contract statements with assumptions [].
Root accepts the block for merge preview.
The branch rebases onto 9401061c.
The same adapter commit now is e4ff44ad.

The local resource draft factors the preserved frame into globals, active input, and its size word.
This factorization preserves the exact physical ownership.
The register collection helper closes in 4,255 ms at 1,144,780 KiB peak RSS.
Its assumption report is Closed under the global context.
The allocator handoff still needs its final resource match.
The readInput handoff needs an alignment bridge.
Five arithmetic lines leave a modular alignment goal.
Root receives the exact residual and the scratch module.
The worker continues the independent allocator handoff.

2026-09-14 Main prefix refresh: Main rebased onto 693c4bde. Both local drafts remained intact. The exact allocator handoff and guarded contract close. The combined scratch reports exit 0, 34838 ms, and 1461396 KiB. The register helper, resource handoff, and contract each print `Closed under the global context`. The contract entry retains `mainAllocatorEntry` and `mainPrefixAllocatorFrame`. Its exit equals the committed `mainBeforeDecodeCallResources` entry at 0x14cec. The proof names `successExitTail` explicitly because its entry projection does not determine that parameter. The reader and prologue composition remain in progress.

2026-09-14 Exact Main prefix: the complete composition from 0x14cb0 to 0x14cec closes in scratch. The scratch reports exit 0, 12282 ms, and 1140352 KiB. `main_prefix_state_correct` prints `Closed under the global context`. The proof composes the existing seven-instruction prologue, the framed eight-instruction readInput contract, and the guarded eight-instruction allocator contract. Its exit is the unchanged committed DecodeEntry entry. It consumes no decoder instruction or trace. It adds no `InputWithinBound` premise. The allocator and reader statement audits report `assumptions: []`. Root requested map normalization for every RAM range fact. Both offset and alignment helpers retain their statements and use `zesu_normalize_machine_map`. Their focused scratch reports exit 0, 4769 ms, 635084 KiB, and two Closed lines. The final handoff checks and fast gate remain pending.

2026-09-14 Reviewed map handoffs: both resource handoffs now use `zesu_normalize_machine_map` for their RAM facts. Their combined focused scratch reports exit 0, 35363 ms, 1424248 KiB, and two Closed lines. The proof statements remain unchanged. Root approved the subsequent local composition into `mainDecodeConcreteResources` at 0x12168. That composition retains the prefix entry and reuses the committed four caller instructions. It excludes all decoder instructions and traces. The prefix commit precedes that composition.

2026-09-14 Main commit ad358b16: Phase 4b.2 composes the Main prefix into the exact DecodeEntry boundary. `main_prefix_state_correct` proves `IslarisContractSpec 0x14cb0 0x14cec (fun _ _ => True%type) (mainPrefixResources decodeTail successExitTail a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13)` under the Iris validity operator. Every new lemma prints `Closed under the global context`. The final MCP compilation passes. Its exact statement audit reports `assumptions: []`. The focused final build passes at j16 in 62393 ms with peak 1463264 KiB. `make check-fast CHECK_AGENT=main AGENT_JOBS=16` passes in 26534 ms with peak 984768 KiB. The proof reuses 23 real instructions across three regions. It adds no instruction semantics, conditional branch, loop, decoder instruction, decoder trace, or stronger input bound. Performance sample: CPU use 56 percent, load 38.10, available memory 93059 MiB, swap use 6515 MiB. Root owns the integrated Iris gate. The next approved block composes the committed four caller instructions into the exact concrete decoder entry at 0x12168.


2026-09-14 Main commit 31612b6ad8507473629582f3d6d9ed02f4f72ad4: Phase 4b.2 composes the committed prefix and the four caller instructions into the exact concrete decoder entry at 0x12168. `main_to_decode_entry_state_correct` proves `IslarisContractSpec 0x14cb0 0x12168 (fun _ _ => True%type) (mainToDecodeEntryResources decodeTail successExitTail a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13)` under the Iris validity operator. The local factory retains the approved prefix entry. Its exit equals `islarisEntry (mainDecodeConcreteResources decodeTail successExitTail) args`. The scratch reports exit 0, 5758 ms, and 1135588 KiB. The focused final build reports exit 0, 7149 ms, and 1135316 KiB at j16. The final MCP compilation passes and prints `Closed under the global context`. Its exact statement audit reports `assumptions: []`. `make check-fast CHECK_AGENT=main AGENT_JOBS=16` reports exit 0, 591 ms, and 144552 KiB. The composition reuses 27 real instructions across the prefix and caller regions. It consumes no decoder instruction or decoder trace. It preserves both approved tails and every entry resource. The worktree is clean. The successful post-decoder composition and adequacy still wait for CP3. All ignored Main drafts remain intact.

2026-09-14 Main 4b.2 continuation resumes. Root clarified that CP3 blocks hypothesis removal and adequacy. The conditional whole Main theorem must proceed before CP3. Root approved `mainSuccessAfterDecodeResources`. Its entry equals the concrete decoder success exit. Its five caller instructions reach `writeSuccessNativeEntry`, while preserving the physical caller frame and zero status slot. The five-instruction guarded block closes: scratch exit 0, 8258 ms, 881020 KiB, and Closed. Two writer postconditions prevent the later Main composition: the terminal machine predicate omits x10 ownership, and its existential witness does not preserve the entry trace tail. Main reported exact resource corrections to Root. ZkvmExit itself needs x5 and x10. Its generic caller wrapper also carries x11. Retaining x10 is the minimum mandatory correction. The writer allows and output relation must stay unchanged.

2026-09-14 Root approved the writer corrections. Root will publish `writeSuccessFixedTailResources outputRelation fixedTail` and `writeSuccessFixedTailModel allows outputRelation fixedTail nextPc`. The family retains arbitrary returned x10, x11, and x12 values. It pins the witness tail at both boundaries. It preserves the legacy terminal predicates, the allows, and the output relation. Root also approved the matching success-glue exit: `writeSuccessFixedTailEntry (successExitTail args) (mainWriterArgs args observation)` plus the caller frame. The physical decoder success exit and the five caller instruction addresses stay unchanged.

### Main success status and terminal block — draft checkpoint

- Root approved the fixed-tail writer family in shared commit 926802fa.
- Main rebased onto that commit and preserved its five new proof modules.
- The exact concrete success glue proves only 0x14cfc, 0x14d00, 0x14d04, 0x14d08, and 0x14d0c.
- Its entry equals the concrete decoder success exit. Its exit establishes `writeSuccessFixedTailEntry (successExitTail args) (mainWriterArgs args observation)` and preserves the caller frame.
- The closed scratch reports exit 0, 11.512 seconds, and 1361272 KiB.
- The terminal contract composes three Main instructions at 0x14d10..0x14d18 and three proved zkvmExit instructions at 0x101c4..0x101cc.
- Its closed scratch reports exit 0, 4.005 seconds, and 786384 KiB.
- The focused source build refreshes shared writer dependencies. Final MCP audits, fast gate, and commit remain pending.
- The partial whole Main theorem retains the concrete decoder and fixed-tail writer contract hypotheses. CP3 blocks their later writer instantiation and adequacy.

### Commit 022f0941 — Phase 4b.2 success boundaries

- Five Main modules implement the exact success dispatch, witness handoff, and six-instruction terminal contract.
- Both final theorems print `Closed under the global context`.
- MCP compiled both final modules and verified both exact statements. Both audits report `assumptions: []`.
- Focused Dune: `-j16 --cache=enabled`, exit 0, 19.120 seconds, 1212952 KiB.
- `make check-fast CHECK_AGENT=main AGENT_JOBS=16`: exit 0, 27.652 seconds, 1148356 KiB. The outer wrapper reports 30.590 seconds.
- The success dispatch uses five real instructions. The terminal contract uses six real instructions. Neither contract uses decoder instructions or loops.
- Next: bridge the concrete failure exit and the fixed-tail writer exit to their physical terminal contracts. Then prove the whole Main theorem with the approved two contract hypotheses.
- Both terminal bridges need the same preserved memory frame without exit MMIO. I sent its exact shared extraction request to Root.

### Commit 0b5e7020 — Phase 4b.2 concrete terminal continuations

- Root published the exact memory separation helpers in 914b6377. Main rebased onto that commit.
- Rebased prior SHAs: f8b8ad50 (prefix), eba07a64 (decoder entry), and 72a39b08 (success boundaries).
- The guarded failure theorem starts from the exact concrete decoder failure exit. It reaches 0x101d0 through the proved failure continuation. Its physical terminal resources retain failureMemory.
- The guarded success theorem starts from the exact concrete decoder success exit. It composes the five success instructions, fixed-tail writer contract hypothesis, and six terminal instructions.
- Both final theorems print `Closed under the global context`.
- MCP compiled both final modules and verified both exact statements. Both audits report `assumptions: []`.
- Focused Dune: `-j16 --cache=enabled`, exit 0, 25.998 seconds, 1369788 KiB.
- Fast gate: exit 0, 0.538 seconds, 136452 KiB. The outer wrapper reports 2.005 seconds.
- One first fast-gate attempt encountered the healthy prefix build lock. Main waited for that build, then reran the gate successfully.
- Root approved the exact whole-resource factory. Root approved failureObservation for the ByteString result; failureMemory remains the physical byte array.
- Next: close and audit the whole Main theorem with the concrete decoder and fixed-tail writer correctness hypotheses.

### Phase 4b.2 whole Main contract — final checkpoint

- The Main entry retains the approved physical prefix resources at 0x14cb0.
- The concrete decoder contract and fixed-tail writer contract remain explicit correctness hypotheses.
- Both outcomes reach physical terminal resources at 0x101d0.
- The success outcome retains the writer witness, output relation, caller memory, saved registers, saved slots, and native exit memory.
- The failure outcome uses failureObservation as ByteString and retains failureMemory as the physical array.
- mainWholeAllows composes the unchanged decoder and writer allows. No frozen allows or output relation changed.
- The closed code equivalence proves that the extracted failure code does not depend on the sample failure status.
- The first transparent code rewrite exceeded the memory limit. The scratch tool stopped it at 89.871 seconds and 6376052 KiB.
- The proof now keeps the writer code locally opaque and transfers only the outer conjunctions. This changes no statement, resource, or instruction.
- The revised whole scratch prints Closed: exit 0, 8.009 seconds, 1239660 KiB.
- Focused Dune: `-j16 --cache=enabled`, exit 0, 13.626 seconds, 1260392 KiB.
- MCP compiled Main.v. main_whole_state_correct and main_whole_correct both print Closed.
- MCP verified both exact statements. Both audits report `assumptions: []`.
- Fast gate: exit 0, 1.039 seconds, 136472 KiB. The outer wrapper reports 3.794 seconds.
- This theorem consumes no decoder instruction or decoder trace.
- Phase 4b.3 awaits CP3. Root owns writer instantiation, adequacy integration, and compliance files.

2026-09-15 Phase 4b.2 verification against Root `445e0eb3`: Main rebased safely. The branch had no unpublished commit and remained clean. The exact prefix, success status glue, concrete failure branch, and whole Iris theorem all passed a focused private Dune build with `--cache=enabled -j16`: 327104 ms, 2691940 KiB peak RSS. Every printed Main assumption line was `Closed under the global context`. MCP compiled `Prefix.v`, `SuccessStatusGlue.v`, `FailureAfterConcreteDecode.v`, and `Main.v`. MCP verified `main_prefix_state_correct`, `main_success_status_glue_state_correct`, `main_failure_after_concrete_decode_state_correct`, `main_whole_state_correct`, and `main_whole_correct`. Each exact statement audit reported `assumptions: []`. `make check-fast CHECK_AGENT=main AGENT_JOBS=16` passed: 64954 ms, 2566048 KiB peak RSS. No proof residual, source change, trace generation, or new commit occurred. Phase 4b.2 is complete. Phase 4b.3 and zesuCompliance wait for CP3 and Root's writer instantiation and shared Compliance integration.

## B4 Encoder.byteLists closed-provider deviation (2026-09-16)

**Before.** `encoderByteListsExactCallSpec` was the only exact byte-list call predicate. It already reduced through `zesu_c_call` to `ret : bv 64`, fixed caller resources, `spec_trace ... tail`, and `instr_pre (bv_unsigned ret) (zesu_call_ret ...)`.

**After.** Add the name `zesuEncoderByteListsExactCallSpec := encoderByteListsExactCallSpec`, its body and persistent providers, and `encoder_byte_lists_exact_closed_equiv`. The existing public predicate and theorem statements remain unchanged.

**Reason.** Tail segment proofs need the standard B2 closed-provider interface. Reuse avoids a duplicate resource predicate.

**Equivalence note.** `encoder_byte_lists_exact_closed_equiv` proves the new predicate equivalent to the existing predicate by definitional reduction. It is closed under the global context.

Commit `d86dde6b` implements this deviation. MCP health and interactive start/check/step passed. Four `Print Assumptions` lines are `Closed under the global context`. The focused j16 target and mandatory Main `check-fast` passed. MCP final compile and verify encountered an `_CoqProject` load-path defect at the first import; the production Dune compile passed. Root will repeat the MCP final audit after integration.
