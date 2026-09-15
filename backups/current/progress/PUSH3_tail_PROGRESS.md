# Push 3: tail

## Plan deviations

- Git cannot create `islaris-native/tail` beside the existing `islaris-native` ref. The orchestrator approved `islaris-native-tail`.
- Ignored trace files do not enter new worktrees. The orchestrator approved copies of unchanged generated files and build links.
- This track uses an absolute build directory under `_build/agents/tail`.
- The orchestrator approved an ignored `_build/default` link to the owned build directory for Rocq MCP.

### Hash-loop split

The integration compile exceeded 300 seconds in `WriteSuccessHashesLoop.v`.
The orchestrator stopped it at 304.61 seconds with sampled RSS of 3858212 KiB.
The orchestrator approved a split at its existing instruction handoffs.
`WriteSuccessHashesLoopSpec.v` contains the unchanged definitions.
Five independent modules contain the unchanged word and tail proofs.
The umbrella retains the unchanged composition and Löb closure.
All seven statements and proof bodies remain byte-identical.
The split awaits compilation and `check-fast`.

### Rocq MCP assumptions

Rocq MCP starts with the owned build link.
Its source-load proof reaches `Qed`.
MCP reports 33 generated `instance_subproof` axioms for register-collection lookups.
The identical source-load scratch compile reports `Closed under the global context`.
The compile exits 0 after 15.926 seconds with peak RSS of 898524 KiB.
The exact MCP output remains in the owned build directory.

## Remaining work

The exact tail needs live source loads, canonical payload calls, and complete memory preservation.
The checked legacy load proofs treat caller slots as uninitialized scratch.
The new handoffs retain the caller values.

### Split measurements

The five independent helpers compile with closed assumptions.
Four measured word modules take 68.610–70.620 seconds.
Their peaks range from 2486564 to 2558284 KiB.
The first umbrella build failed because it lacked a direct import.
The umbrella now retains its original imports and local hints.
The fast gate runs before the split commit.
The machine sample shows 25 percent CPU use and 157714684 KiB available memory.
The sample shows 7045476 KiB used swap.
Each active word proof uses one core.

## Checkpoint commit

35f8312 splits the checked hashes loop at existing native handoffs.
All seven statements and proofs remain identical.
The fast gate exits 0 after 141.132 seconds with peak RSS 2141352 KiB.
The final MCP compile reports closed assumptions for both umbrella lemmas.
The final source-load MCP compile also reports closed assumptions.

1ccf34e proves the source-array load at [0x15668,0x15674).
The proof retains all 69 words without array splitting.
Its final compiler reports closed assumptions.
The fast gate exits 0 after 0.524 seconds with peak RSS 137284 KiB.
I removed the unused cell-only draft.

- The exact value-to-live-entry scratch stopped at the memory limit. The last tactic was `intuition lia` after unfolding `transactionLoopSourceFacts`. This proposition includes the natural-number bound `2^64`. The scratch used 6331756 KiB at 20.555 s. The agent sent the lead a sound split proposal. The proposal separates a pure stack-bound projection from the resource handoff. The Level 1 statement stays unchanged. The failed tactic will not run again.

- The agent copied the canonical `write_failure` and `zkvm_exit` trace artifacts unchanged from the integration worktree. The trace digests are `8dd8b5e7dbd1314f` and `a584bb4babff80b8`. The track artifacts still used the old configuration. This caused the neighbouring writeFailure gate failure after `1d91f274`. The user authorized the canonical configuration. The lead authorized unchanged artifact copies.

- Commit `3710b0f`: Phase 4a pure stack-bound projection. The lemma projects the stack bound without expanding the natural-number count bound. It forms the independent pure part of the required sound split. The compiler reports `Closed under the global context`. MCP verification reports no assumptions. Scratch passed in 1.001 s with 1038852 KiB peak RSS. The fast gate passed in 109.897 s with 2156372 KiB peak RSS. The complete entry handoff still awaits the split ruling.

- The replacement tail agent completed the approved sound entry split. The entry handoff projects the closed Z stack bound before Lithium arithmetic. It keeps `transactionLoopSourceFacts` opaque. Scratch passed in 2.753 s with 1074404 KiB peak RSS. `Print Assumptions` reports `Closed under the global context`. MCP verification reports no assumptions. The region module awaits the matching map, traces, and assigned gate capacity before its commit.

- Commit `e7222a0`: Phase 3.3 exact value-to-live-transaction handoff. The statement preserves the complete caller resources. The final focused build passed in 11.269 s with 1120200 KiB peak RSS. `Print Assumptions` reports `Closed under the global context`. The commit fast gate passed in 0.480 s with 135888 KiB peak RSS. The cold map gate passed in 661.570 s with 2594196 KiB peak RSS. MCP cannot resolve the new `ZesuMachineMap` load path through the current project file. The lead accepted the commit for its merge preview.

- The lead stopped all four exact suffix-word proofs at 300 s after map regeneration. The lead approved a split after eight byte loads and the first two-byte combination. The new handoff preserves every byte and fixes all seven intermediate registers. The original entry and final post stay unchanged. The Word3 assembly scratch passed in 20.524 s with 1351768 KiB peak RSS. Its assumptions are closed. The first load scratch stopped with seven lookup equalities after 272.925 s. The lead accepted the required shared lookup-rule correction.

- The lead approved a draft-only root-output handoff correction. The old draft post required `"x1" ↦ᵣ RVal_Bits (BV 64 0x1573c)`. The generic output ABI exports only `BitsShape 64` for `x1`. The new draft includes `x1` in its 64-bit register collection. The following region already accepts this shape. The public writer exit and its saved return address stay unchanged. No checked proof changes.

## Suffix splits, 2026-09-14

I rebased the tail branch onto shared commit `3bfd25c1`. I kept the public suffix entry and post statements unchanged.

- Word3 load closes in 70.087 seconds at 2136164 KiB.
- Word2 load closes in 124.885 seconds at 2112840 KiB.
- Word1 load closes in 124.381 seconds at 2078804 KiB.
- Word3, Word2, and Word1 pack proofs close in 20.524, 20.780, and 19.776 seconds.
- Each scratch proof prints `Closed under the global context`.
- The focused Dune gate closes Word1–3 compositions and the withdrawal handoff in 75.820 seconds at 2161312 KiB. It uses 16 workers and the shared cache.
- The nonzero helper application closes in 0.751 seconds at 625344 KiB. Its statement stays unchanged.
- Rocq MCP verifies the Word3 pack proof with no assumptions. Word3 load verification times out at 120 seconds. Its scratch and focused Dune checks pass.

Word0 has a different load order. I corrected its internal midpoint from the real traces. The public entry and post stay unchanged. I stopped the old pack test because its midpoint was incorrect. The corrected load and pack tests now run.

Word0 load closes in 35.050 seconds at 1298612 KiB. Word0 pack closes in 51.054 seconds at 1843156 KiB. Both print `Closed under the global context`. The pack proof uses the existing binding and byte lookup helpers.

The fresh-trace fast gate passes in 183.795 seconds at 2667104 KiB. Rocq MCP verifies the withdrawal nonzero helper with no assumptions.

The binding residuals select an output resource through its 16-byte shape. The reviewed map reduces its address to the same value. Post15670Data closes in 5.759 seconds at 1074472 KiB. Header14e28 closes in 12.772 seconds at 1166748 KiB. Both print `Closed under the global context`. Their public statements stay unchanged.

Merged-unit offer: `bbd75d685ce7bce2f40d6b848aa899efcdd609e5`, Phase 3.3 suffix word splits. The final focused gate passes in 50.235 seconds at 1839328 KiB. The warm fast gate passes in 0.554 seconds at 136208 KiB. Rocq MCP verifies Word0 pack and the nonzero helper with no assumptions. Every public suffix word theorem prints `Closed under the global context`.

The four header call repairs each close in approximately 12.27 seconds. Header14e78 closes with the 16-byte shape selector in 16.268 seconds at 1437028 KiB. The repair keeps its existing resource handoff and does not change numbered bindings. All five scratch proofs print `Closed under the global context`. The other five repaired blocks use the existing binding helper. The six public statements stay unchanged.

Commit `f02375929ca7dd9bee4e4520c281ee325e2b7ce1` repairs six output resource bindings. The focused gate passes in 34.032 seconds at 1712236 KiB. The fast gate passes in 0.506 seconds at 134008 KiB. Every printed theorem is closed. Rocq MCP verifies Header14e28, Header14e38, Header14e78 core, and Post15670Data with no assumptions.

I rebased both offered commits onto `6cb46751`. The suffix split commit is now `c70f1f31`. The binding repair commit is now `e4fa2de2`. The proof statements and proof scripts stay unchanged during this rebase.

Commit `83b0d2c599cfb07704d058c830d1c6c92e523e5e` connects the existing exact header frame to live transactions. The adapter retains the static bytes in its caller resource. It keeps the source facts opaque. Both lemmas print `Closed under the global context`. The focused gate passes in 9.093 seconds at 1197952 KiB. The fast gate passes in 0.572 seconds at 141176 KiB. Rocq MCP verifies the handoff with no assumptions.

Commit `df9d4c566c95347cee701f15601d840708f07793` constructs the existing exact header transition through the live-loop continuation. Scratch passes in 1.752 seconds at 1149832 KiB. The focused gate passes in 7.453 seconds at 1230844 KiB. The fast gate passes in 0.860 seconds at 140224 KiB. The theorem prints `Closed under the global context`. Rocq MCP reports no assumptions.

I rebased onto shared restoration commit `9401061c`. The offered commits are now `e9f2d766`, `055156bf`, `07c72e32`, and `2a229384`. Their statements and scripts stay unchanged. The root-output dependencies pass in 44.780 seconds at 1029120 KiB. The native root-output scratch now uses the shared restoration rule and `zesu_finish`.

The lead approved the shared caller remainder. Its exact text and imports are in `_build/agents/tail/ExactCallerRemainderRequest.v` in the tail worktree. The lead will apply it in `Interfaces.v`. The existing tail caller stays unchanged. The header and tail compositions will use the same remainder.

- Commit `10b148d6`: Phase 3.3 exact source-root output at `0x1572c` restores the complete 720-byte source array with shared automation. The approved draft x1 shape remains 64-bit. The saved entry return address and public terminal resources stay unchanged. Print Assumptions reports Closed under the global context. Scratch: 31.785 s, 1,420,580 KiB. Focus: 35.939 s, 1,435,600 KiB. MCP verification returns no obligations. The fast gate passes in 279.065 s with 2,665,492 KiB before the rebase onto `693c4bde`.
- The proposed prefix and terminal export statements are in `_build/agents/tail/ExactRegionExportsRequest.v`. Root must review them before composition proofs. The terminal statement consumes a persistent accessor from P to the exact terminal guard. Both transaction boundaries retain `writeSuccessExactTailCaller args witness ∗ P`.
- Root approved both export statements. The prefix lemma must state `writeSuccessWitnessWellFormed args witness` as a Coq premise. `Contract.v` will choose its terminal continuation as P. The shared transaction boundaries and terminal resources stay unchanged.
- The caller dependency gate passes in 415.276 s with 4,032,936 KiB. No module exceeds its limit. The rebased fast gate passes in 46.519 s with 985,476 KiB.
- The exact terminal resource adapter closes in scratch: 34.837 s, 1,283,392 KiB. The header source-fact projection closes in 5.266 s with 1,094,564 KiB. Both print Closed under the global context. MCP verifies both with no obligations. Their focused gate passes in 38.280 s with 1,283,956 KiB.
- The caller equivalence closes in scratch: 11.280 s, 1,256,372 KiB. It preserves the full tail caller. The helper applies `lookup_take` to the payload pointer. Print Assumptions reports Closed under the global context.
- Commit `bba38e7`: Phase 3.3 exact source-fact projection. Commit `acb40e6`: Phase 3.3 exact terminal resource adapter. Root accepts both for merge preview. The terminal adapter fast gate passes in 1.125 s with 142,536 KiB.
- Commit `d11d31e`: Phase 3.3 caller equivalence and its framed form preserve arbitrary P. Both lemmas print Closed under the global context. The framed scratch passes in 6.017 s with 1,235,036 KiB. MCP verifies both lemmas with no obligations. The combined focused gate passes in 14.499 s with 1,273,556 KiB. The fast gate passes in 1.382 s with 141,252 KiB.
- Root approves fresh exact entry adapters at `0x14d7c` and `0x14d80`. The existing to-load adapter drops saved slots and the decoded-object prefix. The fresh adapters will preserve both resources. Existing statements and the approved prefix export stay unchanged. The first scratch test covers eight load-region instructions. The production boundary retains all 32 instructions. Production splits require measured module limits and sound handoffs.
- The eight-instruction native load scratch closes in 92.943 s with 2,032,292 KiB. It preserves the full 848-byte object and all resources in P. Root approves this sound handoff if the bounded full-block test exceeds its limits.
- The exact prefix trace split closes in 2.003 s with 1,243,448 KiB. It separates the main descriptors from the exact tail events. The prefix payload bound closes in 1.502 s with 1,059,260 KiB. Both lemmas print Closed under the global context. MCP verifies the split with no obligations. The focused gate passes in 3.247 s with 1,244,232 KiB.

- The stopped load test supplied Trace10 only. Trace10 contains 24 instructions. Trace11 contains the final eight instructions. The corrected composition uses both trace maps and preserves the 32-instruction public boundary. The stopped test reached 6,300,808 KiB after 254.563 seconds. Root approved four exact eight-instruction handoffs. I did not repeat the stopped tactic.
- The four load leaves pass their focused gate in 58.968 seconds with 2,638,104 KiB. Each leaf preserves the complete decoded object and the caller frame. The complete-code composition scratch passes in 12.763 seconds with 1,088,200 KiB. Both composition lemmas print Closed under the global context.
- The additional terminal adapter closes against the shared schema draft in 11.769 seconds with 1,294,524 KiB. It retains x10, x11, and x12 through the epilogue frame. Root accepts its statement. The production adapter waits for the canonical shared definitions.
- The copy probe stops before memory matching at the unit package and the address normalization for 0x101d4. Root approves the existing tuple packing helpers. The retry waits for the shared normalization hint. The integrated Iris gate remains failed. Root owns its shared normalization and encoder repairs.
- Root approves a new exact final byte-list adapter. The legacy adapter fixes the saved epilogue return address to 0x159d8. The exact variant will use the witness saved return address. The actual byte-list call still returns to 0x159d8. The writer still returns to 0x14d10. The exact variant will preserve returned x10, x11, and x12 through the epilogue frame. The legacy statement stays unchanged.
- Built-in normalization reaches the copy target after liShow; zesu_instantiate_tuple; liFromSyntaxGoal. Root removes the proposed global address hint because it causes a memory regression. No new address rule is needed for the copy.
- I rebased onto 926802fa. The accepted SHAs are now 6ac73eb8, d99e239f, 53b69d7a, edd5d0bf, and e538f6f3. The statements stay unchanged.
- Commit e362a9c9 completes the exact native load region from 0x14d80 to 0x14e00. Four eight-instruction handoffs retain the complete decoded object and the caller frame. The complete-code export collects Trace10 and Trace11. All four leaf MCP audits and the complete-code audit return assumptions []. Every theorem prints Closed under the global context. The final focused gate passes in 89.019 seconds with 2,547,792 KiB at j16. That gate also verifies the pending pure saved-slot and terminal adapters. The rebased fast gate passes in 250.732 seconds with 2,662,052 KiB at j16.
- Root approves a unit proof-state boundary inside the copy call. I stopped the premature full search. The bounded post-unit probe reaches the existing memcpy predicate in 3.504 seconds. The copy proof now exposes that predicate before it packs the full object list. Its machine goals close. I will inspect its remaining shelved goals before the next test.
- Commit 37fb9f68 completes the exact prologue copy at 0x14d7c–0x14d80. It preserves the full 848-byte object, saved slots, and caller frame. The closed scratch takes 13.264 seconds with 992,768 KiB. The focused gate passes in 14.322 seconds with 991,676 KiB. The fast gate passes in 0.478 seconds with 137,116 KiB. Print Assumptions reports Closed under the global context. MCP returns assumptions [].
- Commit 595318cc adds the saved-slot equivalence and the canonical exact terminal adapter. The terminal adapter preserves returned x10/x11/x12 and the fixed trace tail. Both lemmas print Closed under the global context. Both MCP audits return assumptions []. The fast gate passes in 0.476 seconds with 138,240 KiB. The saved-slot scratch takes 2.002 seconds with 1,019,440 KiB. Their focused gate belongs to tail-exact-load-final above.
- The exact final-call conversion request is in _build/agents/tail/ExactFinalCallFullResourcesRequest.v. Its probe takes 4.004 seconds with 1,089,336 KiB. The proposed returned frame keeps caller registers, free80 at sp-80, byte-list memory, MMIO, the trace tail, and Q. The legacy proof drops those returned memory and trace resources. I will not copy its long resource epilogue into the exact proof. Root will add the shared conversion rule. Root approves the post guard at bv_unsigned savedReturn. The call return and epilogue entry stay at 0x159d8.

- 2026-09-14: Commit 6cb082df proves `exact_main_payload_prefix`. Print Assumptions reports Closed under the global context. MCP reports assumptions []. Scratch: 1.252 s, 1,070,816 KiB. Focused build: 2.360 s, 1,060,820 KiB. Fast gate: 0.518 s, 136,960 KiB.
- 2026-09-14: Root approved the full final-call return family. The family retains x10, x11, x12, stack80, byte-list memory, MMIO16, the trace tail, and Q. The epilogue guard uses the saved writer return address. Root owns the shared conversion rule.
- 2026-09-14: The exact header dependencies pass their focused gate. The build used j16. Elapsed time: 164.861 s. Peak memory: 4,032,852 KiB.
- 2026-09-14: Commit 3017208d proves `native_load_header_entry`. The transition frame retains the full decoded object. Automation divides the workspace at the required resource boundaries. The proof adds no array split. Print Assumptions reports Closed under the global context. MCP reports assumptions []. Scratch: 15.533 s, 1,250,612 KiB. Focused build: 11.075 s, 1,251,284 KiB. Fast gate: 0.580 s, 137,920 KiB.
- 2026-09-14: The exact header model matches the first seven main fragments to the native header events. The proof uses the existing private/public byte inverse. Print Assumptions reports Closed under the global context. MCP reports assumptions []. Scratch: 2.753 s, 1,060,256 KiB. Focused build: 3.659 s, 1,060,376 KiB. Fast gate: 0.538 s, 136,036 KiB.
- 2026-09-14: Commit c954b943 proves `exact_value_model`. The next nine main fragments produce the exact native value events. Print Assumptions reports Closed under the global context. MCP reports assumptions []. Scratch: 3.505 s, 1,116,552 KiB. Focused build: 4.062 s, 1,115,440 KiB. Fast gate: 0.538 s, 137,980 KiB.
- 2026-09-14: Root approved use of the transaction-count bound from `transactionLoopSourceFacts`. Witness well-formedness alone gives the count modulo 2^64. The existing caller invariant gives the required bound. The prefix export and resources stay unchanged.
- 2026-09-14: The exact header model commit is 8de961bc. Root accepted it for the merge preview.
- 2026-09-14: Commit 4f95c77b derives all three value-model premises from witness well-formedness and `transactionLoopSourceFacts`. The proof converts the natural count bound with `Nat2Z.inj_pow`. It does not expand natural 2^64. Print Assumptions reports Closed under the global context. MCP reports assumptions []. Scratch: 2.253 s, 1,075,076 KiB. Focused build: 3.283 s, 1,074,676 KiB. Fast gate: 0.518 s, 138,532 KiB.
- 2026-09-14: Commit 4efa935b proves the exact prefix model and entry trace. Both Print Assumptions lines report Closed under the global context. Both MCP sandbox audits report assumptions []. Scratch: 3.254 s, 1,257,396 KiB. Focused build: 4.153 s, 1,258,240 KiB. Fast gate: 0.628 s, 137,076 KiB.
- 2026-09-14: Tail rebased onto cc1e6d87 without conflict. The remaining SHAs are d4ff0540, f719fb0b, 914a5d9b, 3b6f0b2b, e881ad8e, and c85f32b2. The rebased fast gate passes in 2.219 s with 1,115,436 KiB.
- 2026-09-14: A rewrite over the complete transaction resource predicate stalled. A timed scratch located the stall at the caller equivalence rewrite. The repair applies that closed equivalence to the caller resource only. The repaired guard closes in 6.759 s with 1,338,964 KiB. Tail stopped the three old rewrite probes after this closed result. The guard and resources stay unchanged.
- 2026-09-14: Rocq MCP automatically restarted pet after pet exceeded 16 GiB. The server reported lost proof states. The health check passed after the restart. Both frame adapter audits then passed. Compiler memory stayed below 1.4 GiB. Pet memory and compiler memory are separate measurements.
- 2026-09-14: Commit 3995c2da adds the exact transaction guard adapter and load-frame monotonicity lemma. Both preserve every resource. Both Print Assumptions lines report Closed under the global context. Both MCP sandbox audits report assumptions []. Load-frame scratch: 8.765 s, 849,220 KiB. Focused build: 7.729 s, 1,339,656 KiB. Fast gate: 0.511 s, 135,788 KiB.
- 2026-09-14: Commit 758fdb35 connects the exact copy frame to header resources. It derives the required stack facts from witness well-formedness. The adapter retains the decoded object, saved slots, invariant, and caller frame. All three lemmas print Closed under the global context. Both main MCP sandbox audits report assumptions []. Copy scratch: 4.756 s, 1,313,816 KiB. Stack scratch: 1.752 s, 1,091,680 KiB. Focused build: 5.344 s, 1,313,816 KiB. Fast gate: 0.524 s, 133,944 KiB.
- 2026-09-14: Tail rebased onto e85edfb2 without conflict. The remaining SHAs are 4f38c914, 524c3c29, dea2f000, 82b83549, 99da476e, 3a601c74, 8fde109d, and ea06ac9d. The fast gate passes in 2.302 s with 627,104 KiB.
- 2026-09-14: The exact prefix callee guards follow from the existing closed callee proofs and complete native code. A timed scratch located a stall in generic framing of the four guards. Direct conjunction proofs close the same statement. Tail stopped the two old framing probes after this closed result. Print Assumptions reports Closed under the global context. MCP reports assumptions []. Scratch: 9.261 s, 1,086,332 KiB. Focused build: 9.145 s, 1,087,264 KiB. Fast gate: 0.789 s, 135,212 KiB.
- 2026-09-14: The exact prefix calls commit is 85a690e1. Root accepted it for preview.
- 2026-09-14: Root approved whole-package `iExact` proofs at the final prologue-to-copy handoff. The handoff retains the complete saved-slot package and native data package. The handoff adds no array split or register rename.
- 2026-09-14: Commit 65464c17 exports `write_success_exact_prefix`. The theorem keeps the explicit witness well-formedness premise. It reaches the exact transaction entry at 0x14f04. It retains the decoded object, saved slots, and caller resources. Print Assumptions reports Closed under the global context. MCP sandbox verification reports assumptions []. Scratch: 19.522 s, 1,503,624 KiB. Final focused build: 20.797 s, 1,505,112 KiB. Fast gate: 0.562 s, 136,040 KiB.
- 2026-09-14: Tail rebased onto b8ec12ec. The exact prefix commit is now 4310b192. The callee guard commit is now 923631e1.
- 2026-09-14: The first prefix gate skipped the untracked file. The next gate found its 74-line proof. Root approved three closed handoff lemmas. The public statement and resources stay unchanged. Tail staged the repair before its gate. Scratch: 49.302 s, 1,579,256 KiB. Actual module: 54.972 s, 1,576,636 KiB. Fast gate: 12.699 s, 1,356,484 KiB, j16. All three Print Assumptions lines report Closed under the global context. All three MCP audits report assumptions []. The full-file public audit timed out and restarted pet. The public audit then passed with the compiled handoff lemmas. Compiler memory and pet memory remain separate measurements.
- 2026-09-14: The exact final byte-list call now uses native automation for the real call instruction. Its 31-line proof uses the shared return conversion. It retains all returned registers, stack80, item memory, MMIO16, trace tail, and Q. Its epilogue guard uses the saved writer return. The byte-list call still returns to 0x159d8. The public legacy adapter stays unchanged. Scratch: 7.008 s, 1,263,472 KiB. Actual module: 7.570 s, 1,254,952 KiB. Staged fast gate: 0.546 s, 136,128 KiB, j16. Print Assumptions reports Closed under the global context. MCP reports assumptions [].
- 2026-09-14: The exact final setup proves the three instructions at 0x159c8–0x159d4. It retains the count slot inside the final-call frame. It preserves the full decoded object and saved slots through Q. The proof normalizes the count address from the map bound. It adds no array split or selected resource name. Scratch: 34.795 s, 1,609,544 KiB. Actual module: 32.149 s, 1,623,404 KiB. Staged fast gate: 0.546 s, 135,012 KiB, j16. Print Assumptions reports Closed under the global context. MCP reports assumptions []. Existing setup statements stay unchanged.

## Phase 4a: exact final payload call and model

The additive payload call uses encoderByteListsExactCallSpec. The metadata adapter stays unchanged. Both adapters use one common resource frame.

The metadata trace was writeOutputEventsAny for the count, followed by byteListItemEvents. The payload trace is writeOutputEvents with writeSuccessEncodeU64 for the count, followed by byteListItemPayloadEvents. Code, registers, memory, return guards, and exit resources stay identical. No trace artifact changed. This approved variant matches the terminal snapshot events.

Both model lemmas and both call adapters passed Rocq verification with assumptions []. Each lemma prints Closed under the global context. The focused payload and neighbor build passed in 29.398 seconds, with 1631476 KiB peak memory. The staged check-fast gate passed in 0.490 seconds, with 135764 KiB peak memory. Both builds used j16 and the shared cache.

Next: rebase onto 8266ba22, then prove payload setup and the exact terminal chain.

## Exact terminal boundary repair

The pinned prologue copies decoded offsets 720 through 840 into stack cells. The suffix reads these cells at 0x15930 through 0x159cc. The legacy exactNativeLoadState and writeSuccessExactTailCaller retain only free memory at those stack addresses. Those predicates do not retain the copied values.

Root approved an additive typed predicate, writeSuccessExactCopiedTailWords. Root also approved writeSuccessExactTailCallerWithCopiedWords. The typed predicate retains all sixteen copied words. The additive prefix and tail exports must use the same caller predicate. The terminal resources stay unchanged. Existing closed adapters stay unchanged.

The payload setup scratch prints Closed under the global context. Its run took 51.815 seconds and used 1725848 KiB peak memory. The shared rebase requires a dependency rebuild before the final Rocq audit. The first audit reported stale Hooks assumptions during that rebuild. This result is a cache mismatch, not a completed assumption audit.

## Phase 4a: exact final payload setup

write_success_exact_final_payload_setup_correct proves the three instructions at 0x159c8 through 0x159d0. Its exit at 0x159d4 uses the exact payload call frame. The count slot and caller frame remain owned. The legacy metadata setup stays unchanged.

The lemma prints Closed under the global context. Rocq verification reports assumptions []. The scratch took 51.815 seconds and used 1725848 KiB peak memory. The focused build, including the shared dependency rebuild, passed in 420.713 seconds with 4032208 KiB peak memory. The staged check-fast gate passed in 45.702 seconds with 1320908 KiB peak memory. Both builds used j16 and the shared cache.

The typed-load diagnostic found an incomplete proof after 92.188 seconds and 2980796 KiB. The bounded boundary diagnostic took 16.020 seconds and used 1469448 KiB. The Rocq scratch session died and restarted pet automatically. Root received that restart report. No local automation changed.

Next: rebase onto 146fa8eb, extract the typed-word residual, and compose the final payload sequence.

## Phase 4a: complete final payload sequence

write_success_exact_final_payload_sequence composes the setup at 0x159c8, the call at 0x159d4, and the epilogue at 0x159d8. It consumes complete native code. Its entry retains the saved-return guard, count slot, and caller frame. It has no region correctness premise.

The lemma prints Closed under the global context. Rocq verification reports assumptions []. The scratch passed in 15.766 seconds with 1215936 KiB peak memory. The actual module passed in 17.355 seconds with 1214092 KiB peak memory. The staged check-fast gate passed. Both builds used j16 and the shared cache.

The bounded typed-load diagnostic selected the correct stack address. Its residual compares the loaded decoder word with writeSuccessPostWord. Root owns that shared normalization repair. The complete residual and resource context are in _build/agents/tail/copied-load-first-residual.txt.

Next: prove the additive typed load leaves after root publishes the normalization rule. Prepare exact payload variants for the preceding suffix calls.

### CP3 payload call at 0x1595c

- Commit: `4a1995be`.
- The additive call uses `encoderByteListsExactCallSpec` and payload events.
- The return family retains all twelve saved values and their shape facts.
- The return family retains the exact saved-register identities through `zesu_c_call_ret`.
- The proof keeps the legacy metadata adapter unchanged.
- The proof uses `liShow` at the native call continuation boundary.
- `Print Assumptions exact_suffix_1595c_payload`: `Closed under the global context`.
- Scratch: exit 0, 28.280 seconds, 1491844 KiB.
- Focused build with copied-live dependencies: exit 0, 23.391 seconds, 1489228 KiB, 16 workers.
- Rocq verification: `shared_defs`, assumptions `[]`.
- `make check-fast CHECK_AGENT=tail AGENT_JOBS=16`: exit 0, 44.977 seconds, 1354600 KiB.
- The typed load draft now retains x10–x13 at 0x14de0.
- The fourth typed leaf closes with that repair.
- The third typed leaf needs shared packed-word normalization for register subsumption.
- The complete residual is in `_build/agents/tail/copied-load-register-lithium-residual.txt`.

### CP3 payload call at 0x1594c

- The additive first call uses the exact encoder payload contract.
- The return family preserves the twelve saved identities and shapes.
- `Print Assumptions exact_suffix_1594c_payload`: `Closed under the global context`.
- Scratch: exit 0, 22.026 seconds, 1496168 KiB.
- Focused build: exit 0, 4.533 seconds, 1278152 KiB, 16 workers.
- Rocq verification: `shared_defs`, assumptions `[]`.
- Fast gate: exit 0, 0.638 seconds, 135792 KiB, 16 workers.
- The previous call commit rebased from `4a1995be` to `4612a49e` on `fb3f9a91`.
- The additive value, frame, caller equivalence, and value-live handoffs now close.

### CP3 copied-word caller handoffs

- Commit `e2a286f1` rebased to `bf5d2307` on shared commit `ca4a8013`.
- Five additive lemmas preserve all sixteen copied stack words.
- The caller equivalence establishes `writeSuccessExactTailCallerWithCopiedWords`.
- The adapter unfolds the typed package before the existing resource-group automation.
- The orchestrator approved this package operation.
- All five `Print Assumptions` lines say `Closed under the global context`.
- All five Rocq audits use `shared_defs` and report assumptions `[]`.
- The scratch checks use 2.252–6.758 seconds and at most 1362612 KiB.
- The actual focused targets pass with 16 workers.
- The fast gate passes in 1.273 seconds with 138020 KiB and 16 workers.
- The next copied header transition closes in scratch: 4.510 seconds, 1301444 KiB.
- Payload call `c65075e4` rebased to `701c805f`.
- Payload call `4612a49e` rebased to `9024df47`.
- The shared register rule now supports the exact stage-10 load identities.
- The additive prefix draft keeps the original machine entry and the strong transaction caller.

### Normalization dependency gate

- `TypedLoadNormalizationDependencies` passes against `ca4a8013`.
- Elapsed time: 494.524 seconds.
- Peak compiler memory: 2663940 KiB.
- The build uses 16 workers and the shared Dune cache.
- Both large legacy dependencies finish below the module limits.
- The following build sample includes the other active tracks.
- Total CPU use: 62.8 percent.
- Load averages: 37.70, 35.58, and 24.08.
- Available memory: 90.7 GiB.
- Used swap: 6662540 KiB.

### Copied header guard

- `exact_copied_header_transaction_guard` closes with the additive caller.
- `Print Assumptions` says `Closed under the global context`.
- Scratch check: 22.077 seconds, 1339468 KiB.
- The native header scratch found a stale optional `RegPacking.vo` dependency.
- The next dependency gate will rebuild that optional module before the next scratch test.

### Typed load build

- All four additive eight-instruction load leaves pass against `ca4a8013`.
- Each leaf prints `Closed under the global context`.
- The focused build uses 104.656 seconds and 2676504 KiB with 16 workers.
- The stage-10 boundary retains x10 through x13 as copied words 10 through 13.
- The original load entry remains unchanged.
- The four-leaf composition closes in scratch: 11.024 seconds, 1320036 KiB.
- The complete-code adapter closes in scratch: 8.509 seconds, 1313820 KiB.
- The native header handoff closes in scratch: 11.021 seconds, 1400536 KiB.
- The copied header transition closes in scratch: 3.257 seconds, 1302616 KiB.
- The optional `RegPacking` and `CodeLookup` dependencies now pass their focused rebuilds.
- The four Rocq assumption audits remain active.

### Audit transport and payload residual

- Three typed leaf audits pass with `shared_defs` and assumptions `[]`.
- The fourth request reaches the MCP transport timeout.
- The orchestrator approves one isolated retry with the complete proof file.
- Two helper audit requests trigger automatic pet restarts after query timeouts.
- The helper audit input omitted the complete proof file.
- The next helper audits must supply the complete proof file.
- No source proof changes or toolchain changes follow these failures.
- The copied copy-to-header frame closes in scratch: 6.508 seconds, 1363280 KiB.
- The copied prefix load stage closes in scratch: 20.276 seconds, 1413576 KiB.
- Its actual build passes: 21.026 seconds, 1413532 KiB, 16 workers.
- The exact payload tuple for `0x158e0` retains the caller frame and return `0x158f0`.
- The next shared residual converts 48 uninitialized stack bytes to six words.
- The complete goal is `_build/agents/tail/ExactSuffixBytes158e0PackedResidual.log`.
- The orchestrator owns the shared rule repair.

### CP3 typed load commit

- Commit `ba1907ad` adds the four typed load leaves and their region specification.
- Each leaf keeps the canonical entry and preserves its exact copied-word handoff.
- Stage10 retains x10 through x13 as words 10 through 13.
- All four `Print Assumptions` lines say `Closed under the global context`.
- All four Rocq audits pass with `shared_defs` and assumptions `[]`.
- The isolated fourth audit resolves the transport timeout without proof changes.
- Actual focused build: 104.656 seconds, 2676504 KiB, 16 workers.
- Fast gate: 54.854 seconds, 1354960 KiB, 16 workers.
- The orchestrator accepts the commit for its next preview.
- The three corrected header audits also pass with `shared_defs` and assumptions `[]`.
- The full copied prefix closes in scratch: 24.027 seconds, 1483152 KiB.
- Its final audit and actual build remain pending.
- The payload probe imports the existing `Automation.UninitWords` module explicitly.
- The existing finisher closes all shelved side conditions.
- The probe finishes with no goals: 17.268 seconds, 1603244 KiB.
- No local automation rule or memory split is added.

### CP3 complete copied prefix

- Commit `f28a95adacd142fde6a0e32259d056e42a1ba788` adds the complete copied prefix.
- Export: `write_success_exact_copied_prefix`.
- The export states `writeSuccessWitnessWellFormed args witness` as an explicit Coq premise.
- The export keeps the canonical `0x14d30` prologue entry.
- Its `0x14f04` guard uses `writeSuccessExactTailCallerWithCopiedWords args witness`.
- All sixteen copied words remain available to the exact tail.
- Ten `Print Assumptions` lines say `Closed under the global context`.
- Ten Rocq audits pass with `shared_defs` and assumptions `[]`.
- The final audit retries after its temporary missing dependency receives a fresh build.
- No proof or statement changes follow that audit failure.
- Final-source focused build: 42.973 seconds, 1420820 KiB, 16 workers.
- Fast gate: 0.489 seconds, 138460 KiB, 16 workers.
- Legacy prefix adapters remain unchanged.
- The next step rebases onto the integration branch and continues the exact terminal chain.
- The production `0x158e0` payload lemma also closes in scratch: 28.285 seconds, 1864800 KiB.

### Rebase and exact suffix payload

- The rebase onto `605b71da` succeeds.
- Typed load commit `ba1907ad` becomes `1dcb1384`.
- Complete prefix commit `f28a95ad` becomes `7079c141`.
- The cached fast gate passes: 0.495 seconds, 142888 KiB, 16 workers.
- Commit `84bc2c89` proves the exact payload call at `0x158e0`.
- Export: `exact_suffix_bytes_158e0_payload`.
- Before: the metadata trace uses `writeOutputEventsAny` for the count and data.
- After: the payload trace uses `writeOutputEvents` with the encoded count and the actual bytes.
- The entry, exit, code, memory, registers, and return guard keep the same resource shapes.
- The closed metadata adapter remains unchanged.
- The production module imports the existing `Automation.UninitWords` module explicitly.
- `Print Assumptions` says `Closed under the global context`.
- Rocq audit: `shared_defs`, assumptions `[]`.
- Scratch check: 28.285 seconds, 1864800 KiB.
- Actual target: 34.359 seconds, 1814884 KiB, 16 workers.
- Fast gate: 0.710 seconds, 142116 KiB, 16 workers.
- The remaining four payload calls need the same predicates with different descriptor offsets.
- The proposed generic region predicates await the orchestrator ruling.

- 2026-09-14: Commit `3c4528fb` adds `exact_tail_byte_list_sizes`. The lemma derives each byte-list size equality and preserves `byteListItemResources`. Print Assumptions reports Closed. The complete-file MCP audit passes with assumptions `[]`. The focused predicate and fact build passes in 180.896 seconds at 2295996 KiB. The j16 fast gate passes in 155.889 seconds at 2641368 KiB.
- Approved internal boundary change: payload `_at` families fix sp, payload values, saved register identities, and trace tail. Existing existential variants stay unchanged. These families retain the same resources. The public entry still accepts every permitted input. The five byte-output scratch proofs report Closed in 27.282–33.794 seconds. Entry and return factoring preserve the existing predicates by reflexivity.
- Commit `88b13ac7` identifies the exact payload suffix after the main fragments. Print Assumptions reports Closed. The complete-file MCP audit passes with assumptions `[]`. The scratch takes 1.502 seconds at 1060904 KiB. The focused target passes. The j16 fast gate passes in 0.524 seconds at 137164 KiB.
- All five byte-output `_at` leaves compile and pass complete-file MCP audits with assumptions `[]`. The separate untracked existential draft fails after predicate factoring. Root approves storage of that draft in ignored scratch files. Existing tracked variants stay unchanged.
- The byte-list `_at` scratch at 0x1594c reports Closed in 25.030 seconds at 1473988 KiB. The 0x1595c scratch reports Closed in 21.025 seconds at 1478408 KiB. Both entries retain twelve exact saved register values. Both returns retain sp, byte-list memory, MMIO16, fixed trace tail, and Q.
- Commit `51c5e430` adds five native byte-output `_at` leaves and their predicate module. Each leaf fixes sp, data, size, saved x8/x9, bytes, and trace tail. All five Print Assumptions lines report Closed. All five complete-file MCP audits pass with assumptions `[]`. The seven matching `_at` targets pass against shared commit `2151cd64` in 383.885 seconds at 4033196 KiB. The j16 fast gate passes in 217.496 seconds at 2663660 KiB.
- The 0x1595c byte-list final audit passes with assumptions `[]`. The first 0x1594c audit triggers automatic pet restart above 16384 MB RSS. The restart loses shared states. Root confirms its audit finished before the restart. No actor forces a restart. Compiler memory remains about 1.4 GiB. The retry uses stable file mode. Its start passes. Its check closes all goals in 9.143 seconds. Its final Module M verification passes with assumptions `[]`.
- The 0x15674 byte-list `_at` scratch reports Closed in 27.291 seconds at 1483912 KiB. It uses the same exact saved-register family as the two suffix calls.
- Commit `70404275` adds exact saved-register byte-list `_at` calls at 0x1594c and 0x1595c. Both statements fix sp, payload items, trace tail, and twelve saved register identities. Both Print Assumptions lines report Closed. Both complete-file Module M audits pass with assumptions `[]`. Stable file start/check and MCP compile_file also pass for 0x1594c. The j16 fast gate passes in 0.588 seconds at 136836 KiB.
- The public full-tail signature type-checks against `2151cd64` in 1.002 seconds at 1213476 KiB. Root approves that signature. Its only pure premises are `writeSuccessWitnessWellFormed args witness` and `writeSuccessTraceTail witness = fixedTail`. The public entry consumes the exact transaction exit and `writeSuccessExactTailCallerWithCopiedWords`. The terminal continuation receives `writeSuccessExactTerminalMachine`, native exit memory, fixed spec_trace, and P. No region correctness premise remains.
- The raw byte-list model passes stable file start/check/step_multi. Its check closes all goals. Final MCP compile_file reports Closed. Final MCP verify passes with assumptions `[]`.
- The exact native raw call at 0x15674 passes stable file start/check/step_multi. Its check closes all goals. Final MCP compile_file reports Closed. Final MCP verify passes with assumptions `[]`. The call preserves fixed sp, raw items, trace tail, twelve saved register identities, MMIO16, and Q.
- The rebase onto root integration `382f1aca` keeps pending byte-call commits at `d9d89a33` and `c34438b4`. Git skips the five blocks that Root merged. Source statements and proofs stay unchanged. The raw call and model fast gate passes at j16 in 0.538 seconds at 138100 KiB.

- Commit `2adcf600` (Phase 4b tail): `exact_tail_stack_call_bounds` derives the call's stack80 lower bound and RAM upper bound from witness well-formedness. The public tail signature stays unchanged. Stable MCP start103/check109/step_multi/check110 closes the proof. Final `rocq_compile_file` prints `Closed under the global context`. Final `rocq_verify` succeeds with `assumptions: []`. The fast gate passes: 0.488 seconds, 145632 KiB, j16, cache enabled. The exact 0x15668 LD still needs shared array selection for stack1032 plus index9. Root received the complete residual file. No local array rule was added.

- The exact 0x15668 probe confirmed the selector needs `length (take 69 Values) = 69`. This fact follows from the existing length74 witness fact. One `liAStep` selects the word array after this fact. No shared selector change is needed.
- Two automatic MCP restarts interrupted the probe. The first response was `Pet process died: No response from pet process`, `pet_restarted: true`, `partial_results: []`. The permitted fresh stable retry executed all three instructions. It exposed the environment alias and pure-package completion gaps. The second response had `commands_run: 2` and `last_valid_state_id: 161`. The second failure followed `Unshelve` during `all: zesu_finish`. Root received both failures. Tail did not force a restart or use a shell proof fallback.
- The isolated caller restoration test confirmed a bounded pure solver must test `assumption` before it splits pure conjunctions. This order closes the visible pure resources in 0.3 seconds. Tail sent the shared rule request to Root. The production draft does not contain a manual framing epilogue.

- Commit `2afc3d9f` (Phase 4b tail): the approved arbitrary-P split connects the exact transaction exit at `0x15668` through two loads and AUIPC to the exact raw byte-list call state at `0x15674`. The exported `exact_tail_raw_ready` statement is unchanged. The machine leaf retains exact value memory and the fixed trace. Two small adapters retain all other resources in `exactTailRawLoadMachineFrame`.
- The machine leaf used stable MCP start 200 and bounded instruction steps through state 254. Final `rocq_compile_file` passes in 13.2 seconds and prints `Closed under the global context`. Final `rocq_verify` succeeds with `assumptions: []`.
- Both adapters compile separately in 11.4 and 11.5 seconds. Both print `Closed under the global context`. Their separate final verifies succeed with `assumptions: []`. The composed export compiles in 3.0 seconds, prints `Closed under the global context`, and verifies with `assumptions: []`.
- Stable `rocq_start` repeatedly failed before proofs that mention `WriteSuccessArgs`: `Theorem_not_found ... The reference WriteSuccessArgs was not found`, although `available_in_file` listed each theorem. One-line imports and a fresh filename reproduced the failure. Root approved the bounded fallback for these files: MCP `compile_file` plus original-statement `verify`. No shell proof fallback was used.
- A third automatic MCP restart occurred on the unrestricted machine-leaf candidate. Tail replaced it with bounded instruction steps and did not rerun it. The prior two automatic restarts remain recorded above.
- Tail sent the `IPM_JANNO` alias and assumption-first pure completion residuals to the auto track. The saved report is `_build/agents/tail/IPM_JANNO_AliasResidual.txt`. No local Automation change or framing epilogue was added.
- `make check-fast CHECK_AGENT=tail AGENT_JOBS=16` passes with cache enabled: 0.525 seconds, 137428 KiB.

- Phase 4b tail raw-call block: `exact_tail_raw_ready_to_call` converts the exact `0x15674` ready state into the saved-register call entry. `exact_tail_raw_call` composes the real call through its existential saved-register return at `0x15678`. Both statements preserve the fixed payload trace, MMIO16, copied words, caller memory, and `P`.
- Both final MCP `compile_file` checks pass and print `Closed under the global context`. Both original-statement MCP verifies pass with `shared_defs` and assumptions `[]`.
- Stable `rocq_start` again reports `WriteSuccessArgs` missing while it lists `exact_tail_raw_call` in the file. Root's bounded MCP fallback applies to this file. No shell proof fallback is used.
- The j16 cached fast gate passes in 0.749 seconds at 137852 KiB.
- Commit `6d10360c` (Phase 4b tail) connects the exact raw byte-list return at `0x15678` through four real withdrawal-load instructions to `0x15688`. The entry adapter preserves the exact caller frame, stack, copied words, value memory, MMIO16, fixed trace, and `P`. Both composition theorems and the adapter print `Closed under the global context`. All three final MCP `compile_file` checks pass. All three original-statement MCP verifies pass with assumptions `[]`. Stable `rocq_start` reports the known missing `WriteSuccessArgs` reference for the adapter and final composition. It reports a missing `instr_lookup_resources` reference for the code collector. Root approved the bounded `compile_file` and `verify` fallback. No shell proof fallback was used. The three focused Dune targets pass at j16. The cached j16 fast gate passes in 0.664 seconds at 144084 KiB.

### Plan step 3.2: legacy ValueBlock sound split

The orchestrator approved a private native handoff at `0x14ed4` after two 300-second legacy gate stops.
The first draft assigned exact count words at `sp+104` and `sp+112` to the callback entry.
The corrected callback entry assigns `(bv_unsigned sp + 104) ↦ₘ? 16` to those two slots.
The instructions at `0x14ee8` and `0x14ef0` write the exact count words before `0x14f04`.
The callback retains stack32 at `sp-48`, returned registers, output events, object memory, and the exact public continuation.
The public `write_success_value_block` entry and `0x14f04` post stay unchanged.
The split moves the original definitions into `WriteSuccessValueSpec.v` and the callback into `WriteSuccessValueSuffix.v`.
Rocq MCP cannot start the legacy module because its stable source session misses `instr_lookup_resources`.
The orchestrator approved `rocq_compile_file` and original-statement `rocq_verify` for this module only.
The suffix's old selector pair is unnecessary after the split.
The pinned native suffix closes after `do 224 liAStep` in an unchanged-statement Rocq MCP probe.
The old `do 225 liAStep` requests one instruction after the exact return.
The corrected step count keeps the existing hygiene ratchet flat.

### Plan step 3.2: exact withdrawal count

`fb83a75c` splits ValueBlock at the exact 0x14ed4 callback; public 0x14f04 post stays unchanged.
All three machine lemmas print Closed and pass original-statement Module M verification with no assumptions.
Focused Dune exits 0 in 10.646 seconds at 1250476 KiB peak, j16.
The fast gate exits 0 in 134.840 seconds at 2663492 KiB peak, j16.
`3b1a5178` closes the withdrawal-count model and 0x1568c entry from the exact 0x15688 load post.
All four pure/entry lemmas print Closed and pass Module M verification with no assumptions.
The cached fast gate exits 0 in 0.608 seconds at 141568 KiB peak, j16.
The raw count call remains uncommitted until the shared folded-frame rule closes its first Lithium residual.
Rocq MCP refreshed stale private `.vo` files for ExactValueSpec, Interfaces, RawCallSpec, and WithdrawalLoadSpec.
The first Dune draft target failed on inconsistent compiled assumptions over ValueHandoff.
These cache repairs changed no proof source or shared module.
The orchestrator approved an internal exact count composition statement.
It consumes `writeSuccessCompleteNativeCode` and the persistent `instr_pre 0x1568c` CountReturn guard.
It yields `instr_body 0x15678 (exactTailRawCallReturn args witness P)`.
This statement retains P, the native frame, and the exact trace tail.
The final public full-tail export must discharge the internal CountReturn guard through native blocks.
The pinned status branch at `0x15690` has two syntactically exclusive cases.
Its Sail trace asserts `x9=0` on the `0x156e8` path and `x9≠0` on the `0x15694` path.
The typed branch-entry draft is `_build/agents/tail/WithdrawalBranchPredicatesDraft.v`.
MCP type-checks its unchanged machine return, exact x18 result, complete frame, and two pure count cases.
The orchestrator reviews the additive resource statements before this track edits a proof module.

### Exact private branch predicates before proof

The previous exact count caller frame at `4b6f4dbf` was:

```coq
Definition exactTailWithdrawalCountFrame `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  (reg_col exactTailWithdrawalCountOtherCallerShapes ∗
   reg_col exactTailWithdrawalLoadSavedShapes ∗
   reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessValueWord values 11) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessValueWord values 12) ∗
   (bv_unsigned sp - 80) ↦ₘ? 64 ∗
   byteListItemResources (bv_unsigned (writeSuccessValueWord values 9))
     (writeSuccessRawTransactions witness) ∗
   exactTailWithdrawalValueRemainder sp values ∗
   writeSuccessTransactionBase witness ↦ₘ∗
     WriteSuccessNativeContract.writeSuccessTransactionBytes witness ∗
   writeSuccessTransactionsOwn (writeSuccessTransactions witness) ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 (writeSuccessTransactionBase witness) ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (length (writeSuccessTransactions witness)) ∗
   (bv_unsigned sp + 120) ↦ₘ? 160 ∗ (bv_unsigned sp + 1640) ↦ₘ? 256 ∗
   bv_unsigned sp ↦ₘ? 8 ∗
   writeSuccessExactCopiedTailWords sp (writeSuccessDecodedBytes witness) ∗
   (bv_unsigned sp + 312) ↦ₘ∗ writeSuccessSourceBytes witness ∗
   (bv_unsigned sp + 1624) ↦ₘ? 16 ∗ writeSuccessTerminalSavedSlots witness ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗ writeSuccessDecodedBytes witness ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ writeSuccessPayload witness ∗
   bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗ writeSuccessWithdrawalsBytes witness ∗
   writeSuccessPostTransactionDataResources sp (writeSuccessSourceBytes witness)
     (writeSuccessDecodedBytes witness) (writeSuccessPostData witness) ∗
   writeSuccessNativeStaticResources ∗
   writeSuccessTransactionsInvariant sp (writeSuccessTransactionBase witness)
     (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) []
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) ∗
   ⌜writeSuccessWitnessWellFormed args witness⌝ ∗ P ∗ True)%I.
```

The approved common-frame factoring uses the same resource order:

```coq
Definition exactTailWithdrawalCommonFrame `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) (savedShapes : list (reg_kind * valu_shape))
    : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  (reg_col exactTailWithdrawalCountOtherCallerShapes ∗
   reg_col savedShapes ∗
   reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessValueWord values 11) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessValueWord values 12) ∗
   (bv_unsigned sp - 80) ↦ₘ? 64 ∗
   byteListItemResources (bv_unsigned (writeSuccessValueWord values 9))
     (writeSuccessRawTransactions witness) ∗
   exactTailWithdrawalValueRemainder sp values ∗
   writeSuccessTransactionBase witness ↦ₘ∗
     WriteSuccessNativeContract.writeSuccessTransactionBytes witness ∗
   writeSuccessTransactionsOwn (writeSuccessTransactions witness) ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 (writeSuccessTransactionBase witness) ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (length (writeSuccessTransactions witness)) ∗
   (bv_unsigned sp + 120) ↦ₘ? 160 ∗ (bv_unsigned sp + 1640) ↦ₘ? 256 ∗
   bv_unsigned sp ↦ₘ? 8 ∗
   writeSuccessExactCopiedTailWords sp (writeSuccessDecodedBytes witness) ∗
   (bv_unsigned sp + 312) ↦ₘ∗ writeSuccessSourceBytes witness ∗
   (bv_unsigned sp + 1624) ↦ₘ? 16 ∗ writeSuccessTerminalSavedSlots witness ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗ writeSuccessDecodedBytes witness ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ writeSuccessPayload witness ∗
   bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗ writeSuccessWithdrawalsBytes witness ∗
   writeSuccessPostTransactionDataResources sp (writeSuccessSourceBytes witness)
     (writeSuccessDecodedBytes witness) (writeSuccessPostData witness) ∗
   writeSuccessNativeStaticResources ∗
   writeSuccessTransactionsInvariant sp (writeSuccessTransactionBase witness)
     (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) []
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) ∗
   ⌜writeSuccessWitnessWellFormed args witness⌝ ∗ P ∗ True)%I.
Definition exactTailWithdrawalCountFrame `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  exactTailWithdrawalCommonFrame args witness P
    exactTailWithdrawalLoadSavedShapes.

Definition exactTailWithdrawalBranchFrame `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  exactTailWithdrawalCommonFrame args witness P
    (tl exactTailWithdrawalLoadSavedShapes).

Global Instance : LithiumUnfold (@exactTailWithdrawalCommonFrame) := I.
Global Instance : LithiumUnfold (@exactTailWithdrawalBranchFrame) := I.
```

The approved path resources and count conditions are:

```coq
Definition exactTailWithdrawalBranchResources `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  (encoderIntExactFramedPost (writeSuccessFrameSp witness) (BV 64 0x1568c)
     (exactTailAfterWithdrawalCountEvents witness)
     (exactTailWithdrawalBranchFrame args witness P) ∗
   "x18" ↦ᵣ RVal_Bits (writeSuccessFrameSp witness + BV 64 1768)%bv)%I.

Definition exactTailWithdrawalsBranchNonzeroEntry `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  (exactTailWithdrawalBranchResources args witness P ∗
   ⌜0 < writeSuccessWithdrawalsCount witness⌝)%I.

Definition exactTailWithdrawalsBranchZeroEntry `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  (exactTailWithdrawalBranchResources args witness P ∗
   ⌜writeSuccessWithdrawalsCount witness = 0%nat⌝)%I.
```

The CountReturn definition and the public terminal contract stay unchanged.

2026-09-15 ValueBlock selector gate: Root approved one local A2 selector opt-out
in `WriteSuccessValueBlock.v`. The exact new line follows the IslarisCode import:
`Local Remove Hints subsume_instr_some_pre_inst : typeclass_instances.` The
`write_success_value_block` statement and proof resources stay unchanged.
`rocq_health` selected the Islaris switch. Two fresh stable `rocq_start` calls
failed before theorem entry with `instr_lookup_resources was not found`.
Root approved MCP `rocq_compile_file` plus original-statement `rocq_verify`
for this theorem only. Compilation printed Closed. Original-statement
verification returned `assumptions: []`. The focused j16 target passed in
18.834 s with 1,514,052 KiB peak. The j16 check-fast gate passed in 101.267 s
with 2,189,572 KiB peak. No additional old-wand selector was introduced.

2026-09-15 supplemental proof-owner ruling: Root assigned the existing
`WriteSuccessExactEncoderIntCall.v` helper to Tail for Phase B2 after the Phase A
map gate. Auto owns its reusable automation and tests. Tail will add the
ret:bv64 closed-spec helper and derive the unchanged framed theorem from it.
Tail will not start that source change before Root reports the Phase A gate.

2026-09-15 suffix hash legacy fallback: Tail changed the first block call from
`zesu_block` to the named `zesu_block_simpl` in the six Word0, Word1, and Word2
Load/Pack modules. The A3 shared tactic removed general simplification. This
forward-only one-line fallback restores the measured old preamble without a
resource or theorem statement change. The focused j16 six-target gate passed
in 214.985 s with 2,156,848 KiB peak; each compiler stayed below 300 s.
Stable MCP file start twice failed `suffixWord0Mid was not found` before theorem
entry. Root approved MCP compile_file plus original-statement verify for exactly
these six unchanged theorems. All six compiled with Print Assumptions Closed.
All six original-statement verifications returned `assumptions: []`. The j16
check-fast gate passed in 129.517 s with 2,544,944 KiB peak.
2026-09-15 private Tail cache reset: Root approved one `dune clean` in `_build/agents/tail` after focused Dune builds kept stale `.vo` files. Tail verified all 339 ignored generated trace wrappers matched Root byte-for-byte, backed up and restored 259 private scratch files, and preserved both untracked CountCall drafts. The exact status dependencies rebuilt with j16 and cache enabled: exit 0, 174.990 seconds, 4,041,844 KiB peak. Fresh MCP status proof passed the folded mstatus and x9 selectors and reached both typed successors. Tracked proof source did not change.
2026-09-15 B2 proof inventory: `write_success_07.instr_map` has ten pinned PCs from `0x15d10` through `0x15d34`. Eight PCs end at `0x15d2c`; two more end at `0x15d34`. The proposed additive exact call uses `ret : bv 64` and retains the payload trace, RAM and MMIO map facts, x5/x10/x11 return values, stack16, and `instr_pre (bv_unsigned ret)`. The old payload-pre and framed theorem statements remain required by existing callers. An ignored full frame adapter prints Closed and verifies assumptions `[]`; the native exact call is still open at a `(spec *ₗ ())` existential. No tracked B2 source changed.

2026-09-15 B2 additive statement deviation: Before, `zesu_encoder_int_payload_call_correct` proved `instr_body 0x15d10 zesuEncoderIntPayloadCallSpec`, with `ret : Z` and x1 equal to `Z_to_bv 64 ret`. After, `zesu_encoder_int_exact_call_correct` proves `instr_body 0x15d10 zesuEncoderIntExactCallSpec`, with `ret : bv 64`, x1 equal to `ret`, and `instr_pre (bv_unsigned ret)` at return. The exact spec retains the same output payload trace, stack16, MMIO16, RAM bounds, and exact x5/x10/x11 return values. The old payload theorem and payload-pre theorem stay unchanged. An exact-entry adapter selects `retZ := bv_unsigned ret` and packs the old x5/x11 shape predicates. `instr_pre_wand` derives the exact body from the proved payload body. A second `instr_pre_wand` adapter derives the unchanged `encoder_int_exact_framed_correct` statement from the exact body and an exact return-frame lemma. The ignored combined fixture compiled with MCP and verified the unchanged framed statement with `assumptions: []`. This additive derivation avoids a new execution premise.

2026-09-15 private WithdrawalsRest split deviation: The unchanged legacy module reached the 300-second proof limit. Root approved a private typed first-return handoff at 0x156b4. The 0x156a8 prefix currently reaches `zesu_instr_pre_match` for the 0x156b4 load after the first encoder-int call. The private `withdrawalsFirstReturnResources` draft retains the loaded stack word, the two current48 fragments, exact x1/x2/x5/x10/x11 return values, x8/x9/x18, prefix/suffix arrays, the SecondInt phase trace, the loop-exit continuation, P, and the existing 0x156dc tail body. Its definition type-checks, but its machine proof is open at that match. The public `write_success_withdrawals_rest` statement and resources stay unchanged. The final split will compose a native 0x156a8 prefix and 0x156b4 remainder without a new region premise.

2026-09-15 B1 exact-return hook: Tail committed one `LithiumUnfold (@encoderIntExactReturn)` instance in the owned encoder-int Call module. Root merged it as 68efa2db. The unchanged exact-call and framed statements passed MCP original-statement verification with empty assumptions. Tail's focused j16 Call+Framed gate passed in 80.483 seconds/4,116,180 KiB, and check-fast passed in 0.635 seconds/139,288 KiB. The Tail branch was pushed after the authorized rebase.

2026-09-15 RawLoad qualifier correction: The existing `exact_tail_raw_load` proof stopped because `WriteSuccessValueBlock.writeSuccessValueWord` was no longer exported. Root approved two qualifier corrections to `WriteSuccessValueSpec.writeSuccessValueWord`, with the public statement unchanged. MCP compile_file closed and Module M verify returned empty assumptions. The focused j16 gate passed in 13.329 seconds/1,625,388 KiB, and check-fast passed in 41.547 seconds/1,358,320 KiB. Tail pushed rebased commit 75ae164d. No machine resource changed.

2026-09-15 persistent 0x15668 continuation: Root approved `exact_tail_raw_ready_pre` as an additive adapter from complete Code and persistent `exactTailRawReady` at 0x15674 to persistent `transactionLiveLoopExit` at 0x15668. The adapter uses the existing `exact_tail_raw_ready` native body through `instr_pre_to_body` and `iNext`. LoopExit scratch, exact output events, copied-word caller, and generic P stay exact. MCP compile_file closed and original-statement verify returned empty assumptions. The focused j16 gate passed in 5.089 seconds/1,315,308 KiB, and check-fast passed in 0.869 seconds/146,452 KiB. Tail pushed commit 8696dd36. Root must discharge the 0x15674 guard in final Contract composition.

2026-09-15 private status/CountCall owner checkpoint: The actual status goal after copied Word0 requests the complete bytes1571c array. A fixed-source `iSelect` exposes the direct folded `writeSuccessPostTransactionDataResources` owner and only its first descriptor. Six existing package openers promote the hash and five later descriptor size facts without splitting any byte array. The exact optional1596c whole owner matches its Some/None request. The next folded owner is `IAnon240 : byteListItemResources (bv_unsigned (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 14)) (writeSuccessPostByteLists159c8 (writeSuccessPostData witness))`. Its recursive arrays remain folded. The next exit frame contains PostDataFacts, static resources, the transaction invariant, Hwf, P, and branch registers. All tests are in ignored `_build/agents/tail/TailOptionalOwnerProbe.v`; production status and CountCall statements remain unchanged. Auto owns reusable native selectors.

2026-09-15 private Hwf residual: Existing whole-package selection consumes ByteLists159c8 while keeping its arrays folded. The first Coq goal after `zesu_run` is `writeSuccessTransactionBytes witness = writeSuccessTransactionsBytes (writeSuccessTransactions witness)`. WriteSuccessNativeContract.v:170 states this equality inside `writeSuccessWitnessWellFormed args witness`. A direct Iris selection of `⌜writeSuccessWitnessWellFormed args witness⌝` failed because the pure owner remains folded in `exactTailWithdrawalCommonFrame` after PostDataResources, static resources, and the invariant. Root sent the exact folded-frame residual to Auto for a guarded Hwf owner rule. No new premise or production status/CountCall edit was added.

2026-09-15 exact 0x15980 gate repair: The unchanged `write_success_suffix_bytes_15980_to_15990` theorem stopped at a continuation existential after `liARun`. MCP showed that the printed `bv_unsigned (sp+8) ↦ₘ size` word was an available Iris owner, not a goal. The only requested proposition related `writeSuccessSuffixBytes15990CallPost sp (data+0) ...` to the same post with `data`; the existing `Hdata0` equality resolves it. A four-line local step used `unLET`, rewrote `Hdata0`, selected `emp`, and proved the identity wand. Whole byte arrays and the public theorem stayed unchanged. Tail committed and pushed fd15a4df. MCP compile_file printed Closed, original-statement Module M verify returned empty assumptions, focused j16 passed in 5.922 seconds/1,084,868 KiB, and check-fast passed in 0.515 seconds/144,512 KiB. Root holds merge until the cohesive full-Iris recovery gate turns green.

2026-09-15 private 0x1568c status handoff: Root approved an ignored one-instruction `zesu_block` probe from unchanged CountReturn to unchanged BranchResources, with complete Code and persistent 0x15690 next state. Two local steps introduce the exact optional1596c antecedent and unfold BranchResources after `zesu_run` focuses it. The first spatial request is `encoderIntExactFramedPost ... BranchFrame`, followed by exact x18 ownership. An exact selection of the corresponding CountFrame post found no direct owner after machine progress. Tail stopped before opening the full frame or changing any array. The probe is `_build/agents/tail/TailStatusSetX18Probe.v`; Auto will classify its actual saved-slot owner after the frozen R/T repair matrix.
