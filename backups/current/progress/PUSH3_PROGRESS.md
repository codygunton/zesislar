# Push 3 progress — Islaris-native compliance

## Remaining-work inventory

Inventory origin: `272909a5`. Integration boundary: `382f1aca`. CP3, CP4, and CP5 remain open. The user approved the calling-convention correction and configuration unification.
Current Root integration HEAD: `33471636`. PR9 remains open and pushed; the latest full `check-iris` preview is red on 41 frozen proof modules and adds zero failures.
Repair phase: Auto's AllLegacy and exact R hygiene baseline are merged; TX owns 9 R and 28 active T files; Tail owns 2 R and 2 T files. Main and Exec wait for CP3. TX and Tail are rebasing once, then running their track gates before repair commits.
Ranges below include their start address and exclude their end address.
The legacy coverage matrix reports 950/950 addresses. That count does not establish the exact contract composition.
An existing block can require composition without another instruction proof.

### Loops that still need exact closure

| Loop | Head and range | Remaining work |
|---|---|---|
| Transactions | `0x14f04`, `[0x14f04,0x15668)` | The exact iteration cases, universal step, and persistent outer Löb closure are merged. Connect the 0x15668 Tail continuation and final exit resources. |

The exact withdrawal, suffix-hash, authorization, storage-key, access-list, blob-hash, byte-list, and memcpy loops contain checked Löb closures.
Their callers still need integration into the complete contract.
Legacy closures do not discharge any row above.

### Remaining exact blocks and integration

| Region | Address range | Remaining exact proof or integration |
|---|---|---|
| write_output | `[0x10190,0x101c4)` | No helper gap. Integrate the checked payload contract at all remaining sites. |
| memcpy | `[0x101d4,0x101f8)` | No helper gap. Integrate the checked whole-array contract into withdrawals. |
| Prologue | `[0x14d30,0x14e00)` | The additive full prefix preserves copied words. Its four typed leaves and full composition are merged and pass the preview gate. |
| Header and value | `[0x14e00,0x14f04)` | The additive copied-stack header connects to the generic transaction caller frame. The complete prefix is merged. |
| Transaction prefix | `[0x14f04,0x151d0)` | Compose checked index, tag, chain, nonce, gas, priority, recipient, value, and data blocks. Close exact call handoffs. |
| Transaction first loads | `[0x14f08,0x14f68)` | The frame-safe index and complete source composition pass through `0x150f0`. Connect the outer invariant. |
| Transaction remaining loads | `[0x14f68,0x150e8)` | The frame-safe source composition passes through `0x150f0`. Connect the field caller. |
| Transaction type | `[0x150e8,0x150f0)` | The frame-safe composition includes the exact payload output. Connect its exit to the field caller. |
| Transaction chain and nonce | `[0x150f0,0x15108)` | Both native optional paths compose through `0x153d0`. Their entries have no continuation premise. Connect the outer caller frame. |
| Transaction gas price | `[0x15108,0x15118)` | No exact region gap. The native nonce-to-gas region passes on both priority paths. Integrate the chain-ID caller. |
| Transaction priority | `[0x15118,0x15148)` | No exact region gap. Both paths, their payload traces, the fee jump, and the common gas frame pass. Integrate the caller. |
| Transaction gas limit | `[0x15148,0x15154)` | No exact region gap. Both predecessor paths compose through the access count. Integrate the chain-ID caller. |
| Transaction recipient | `[0x15154,0x1519c)` | No exact region gap. Both paths compose through the access count. Connect the access-list caller frame. |
| Transaction value | `[0x1519c,0x151b4)` | No exact region gap. The native U256 call composes with both data outputs and the access count. Integrate the caller. |
| Transaction data | `[0x151b4,0x151c4)` | No exact region gap. The complete `[0x150fc,0x151d0)` native region passes. Integrate the access-list caller. |
| Transaction access count | `[0x151c4,0x151d0)` | No exact region gap. Both native recipient paths reach this exit with source resources. Connect the exact access-list loop entry. |
| Access lists | `[0x151d0,0x153c0)` | Both chain-ID paths compose through the `0x153d0` terminal handoff. Connect the blob-hash caller and outer transaction frame. |
| Storage keys | `[0x15228,0x153b4)` | No nested-loop gap. Reuse the checked split byte-assembly blocks and exact closure. |
| Blob hashes | `[0x153d4,0x15564)` | No nested-loop gap. Connect its exit to the max-blob-fee call. |
| Authorization prefix | `[0x15564,0x15590)` | No instruction gap. The exact two-call prefix, both initial branches, and public count continuation pass. Integrate its caller. |
| Authorization copy | `[0x15590,0x155a4)` | No gap. The exact loop body composes the checked copy into the canonical row body. |
| Authorization body | `[0x155a4,0x15614)` | No gap. The exact loop body integrates all six checked outputs. Connect its caller. |
| Authorization tail | `[0x15614,0x15620)` | No gap. The exact Löb closure includes both branch handoffs and preserves the complete source array. |
| Transaction signature and tail | `[0x15620,0x15668)` | No instruction gap. The exact three-call composition and back-edge continuation pass. Establish the next outer invariant and exit resources. |
| Post-transactions | `[0x15668,0x15694)` | Replace remaining legacy-output handoffs with canonical payloads. Connect raw transactions and withdrawal count. |
| Withdrawals | `[0x15694,0x156e8)` | No body or closure gap. Connect the checked exact loop to its initial branch and post-withdrawal caller. |
| Post-withdrawals | `[0x156e8,0x15744)` | Connect extra-data bytes, optional fields, and the suffix count through exact output contracts. |
| Suffix entry | `[0x15744,0x15754)` | Connect the count and zero/nonzero branch with exact continuation resources. |
| Suffix hashes | `[0x15754,0x158e0)` | No native body or closure gap. Connect the exact closed loop to its initial branch and tail caller. |
| Tail | `[0x158e0,0x159d8)` | Connect remaining optional and fixed fields to canonical fragments. Establish the complete exit memory frame. |
| Epilogue | `[0x159d8,0x15a14)` | Integrate the checked strengthened epilogue with the exact terminal resources. |
| Encoder.boolean | `[0x15b9c,0x15bc8)` | No helper gap. Integrate exact calls at remaining sites. |
| Encoder.optional | `[0x15bc8,0x15c10)` | No helper gap. Integrate both checked payload branches at remaining sites. |
| Encoder.byte_lists | `[0x15c10,0x15c6c)` | No helper gap. Integrate the checked public contract for raw transactions. |
| Encoder.bytes | `[0x15c6c,0x15cb0)` | No helper gap. Integrate payload and whole-array handoffs at remaining sites. |
| Encoder.u256 | `[0x15cb0,0x15d10)` | No helper gap. Integrate U256 and U128 entries with canonical field fragments. |
| Encoder.int | `[0x15d10,0x15d38)` | No helper gap. Integrate exact field and count calls at remaining sites. |

### Exact transaction-source handoffs

These checked blocks still need caller composition into the complete transaction invariant.
No row requires a duplicate instruction proof.

| Exact range | Checked block to compose |
|---|---|
| `[0x14f08,0x14f1c)` | Index prefix. |
| `[0x14f1c,0x14f68)` | Complete nineteen-load region. |
| `[0x14f68,0x14f7c)` | Optional prefix bytes. |
| `[0x14f7c,0x14f90)` | Optional value bytes. |
| `[0x14f90,0x14fa8)` | Recipient source loads. |
| `[0x14fa8,0x14fb0)` | Recipient pair. |
| `[0x14fb0,0x14fb8)` | Recipient tag. |
| `[0x14fb8,0x14fc8)` | Recipient shifts. |
| `[0x14fc8,0x14fd0)` | Recipient high shifts. |
| `[0x14fd0,0x14fe0)` | Recipient pairs. |
| `[0x14fe0,0x14ff0)` | Recipient middle loads. |
| `[0x14ff0,0x15008)` | Recipient lower shifts. |
| `[0x15008,0x15018)` | Recipient lower pairs. |
| `[0x15018,0x15028)` | Value prefix. |
| `[0x15028,0x15038)` | Recipient middle pair. |
| `[0x15038,0x15044)` | Recipient words. |
| `[0x15044,0x15060)` | Signature values. |
| `[0x15060,0x15068)` | Recipient low words. |
| `[0x15068,0x15078)` | Recipient wide words. |
| `[0x15078,0x15088)` | Signature suffix. |
| `[0x15088,0x15098)` | Signature tail. |
| `[0x15098,0x150b0)` | Nested lists. |
| `[0x150b0,0x150cc)` | Nested suffix. |
| `[0x150cc,0x150e8)` | Type-output preparation. |
| `[0x150e8,0x150f0)` | Exact type output and chain-ID caller. |

### Exact blocks after transactions

These ranges come from the pinned instruction maps in the Push 2 build.
Each row still needs exact native composition and its caller frame.
The checked legacy block alone does not discharge that work.

| Region | Exact range | Handoff still to establish |
|---|---|---|
| Post-transactions | `[0x15668,0x15678)` | Raw-transaction byte lists. |
| Post-transactions | `[0x15678,0x1568c)` | Withdrawal count. |
| Post-transactions | `[0x1568c,0x15694)` | Both exact branches pass. Connect the witness caller and its post-withdrawal continuation. |
| Withdrawals | `[0x15694,0x156e8)` | The complete exact loop and Löb closure pass. Integrate the caller; no duplicate instruction proof is needed. |
| Post-withdrawals | `[0x156e8,0x156f4)` | First scalar output. |
| Post-withdrawals | `[0x156f4,0x15700)` | Second scalar output. |
| Post-withdrawals | `[0x15700,0x1571c)` | Optional-U64 setup and both payload branches. |
| Post-withdrawals | `[0x1571c,0x1572c)` | Bytes encoder. |
| Post-withdrawals | `[0x1572c,0x1573c)` | Fixed 32-byte root output. |
| Suffix entry | `[0x1573c,0x15750)` | Hash count. |
| Suffix entry | `[0x15750,0x15754)` | Both branches pass. The positive branch uses the checked exact Löb closure. Connect the count and tail caller. |
| Suffix hashes | `[0x15754,0x157b0)` | The first 23-instruction word block passes. Integrate its caller. |
| Suffix hashes | `[0x157b0,0x1580c)` | The second 23-instruction word block passes. Integrate its caller. |
| Suffix hashes | `[0x1580c,0x15868)` | The third 23-instruction word block passes. Integrate its caller. |
| Suffix hashes | `[0x15868,0x158c4)` | The fourth 23-instruction word block passes. Integrate its caller. |
| Suffix hashes | `[0x158c4,0x158d4)` | The exact 32-byte output passes. Integrate its caller. |
| Suffix hashes | `[0x158d4,0x158e0)` | Both invariant handoffs and the exact Löb closure pass. Integrate the tail caller. |
| Tail | `[0x158e0,0x158f0)` | First bytes encoder. |
| Tail | `[0x158f0,0x15900)` | Second bytes encoder. |
| Tail | `[0x15900,0x15910)` | Third bytes encoder. |
| Tail | `[0x15910,0x15920)` | Fourth bytes encoder. |
| Tail | `[0x15920,0x15930)` | Fifth bytes encoder. |
| Tail | `[0x15930,0x15940)` | First byte-list encoder. |
| Tail | `[0x15940,0x15950)` | Second byte-list encoder. |
| Tail | `[0x15950,0x15960)` | Third byte-list encoder. |
| Tail | `[0x15960,0x1596c)` | Scalar output. |
| Tail | `[0x1596c,0x15974)` | Optional-bytes branch. |
| Tail | `[0x15974,0x15980)` | Present boolean output. |
| Tail | `[0x15980,0x15990)` | Present bytes output. |
| Tail | `[0x15990,0x15994)` | Join at `0x159a0`. |
| Tail | `[0x15994,0x159a0)` | Absent boolean output. |
| Tail | `[0x159a0,0x159b0)` | Scalar output. |
| Tail | `[0x159b0,0x159bc)` | First optional-U64 output. |
| Tail | `[0x159bc,0x159c8)` | Second optional-U64 output. |
| Tail | `[0x159c8,0x159d8)` | Final byte-list output and complete memory frame. |
| Epilogue | `[0x159d8,0x15a14)` | Exact terminal resources at the caller return. |

### Steps to the remaining checkpoints

1. CP3: close the remaining exact transaction loop and region handoffs. Prove `Proofs/WriteSuccess/Contract.v` with unchanged exit resources.
2. CP3: check canonical output concatenation against the witness observation. Run both gates and record assumptions, coverage, timings, and deviations.
3. CP3: keep PR 9 open against `main`, push integrated commits, and do not merge it.
4. CP4: use the checked main dump and traces. Prove `Proofs/Main/Main.v` and compose all endpoints with `decodeOk`.
5. CP4: replace the shell placeholders with the pinned initial image and computable label outcome. Apply adequacy and remove `mainOk` only after importing the proved main theorem.
6. CP4: report the checked observation-bug adapter equality from `1e0d50a2`. State its exact definition. Check every reproducible evidence input with `zesuBugLayout`.
7. CP4: remove the shell admission and its allow-list entry. Remove remaining forbidden-name baseline occurrences. Run `check-fast`, `check-iris`, and `check`.
8. CP5: prove `Export/Executor.v` sound against unchanged `seq_step`. Prove `Export/Determinism.v` with its decidable trace condition.
9. CP5: test all 45 pilot addresses with `vm_compute` and `bv_solve`. Record each result below five seconds.
10. CP5: prove control invariants, ranks, and `zesuTerminates`. Run both gates and record the checkpoint.

I will update this inventory at CP3, CP4, and CP5.


## Track status

- tx: zero/nonempty iteration, three original H7 pilots, universal Hstep, and persistent 0x14f04 outer Löb export are merged. The 0x15668 continuation, older carrier pilots, and complete Contract.v handoff remain open. The B1 count-entry LithiumUnfold hook passed MCP and awaits focused/fast gates.
- tail: the full prefix, count-zero lemma, exact B2 encoder-int contract, and shared copied Word0 selector are merged. The guarded first-array opener is merged, but the rebased actual Tail goal still needs a narrow requested-term correction. The six descriptor sizes and optional1596c remain private. The capped WithdrawalsRest needs its 0x156b4 return split. The terminal 0x15668 continuation and exact exit remain open.
- main: Phase 4b.2 is merged. The whole-program factory takes decoder and writer hypotheses. Phase 4b.3 awaits CP3.
- exec: soundness, syntactic determinism, scoped trace audit, and 45 pilot proofs are merged. Phase 5.3 awaits CP3.
- port: preparation and tools are merged. Both loader checks pass. Binary PR 104 remains open. The default ELF remains frozen.
- auto: Phase 0, A1, A3, A2, A6, and A4 and the guarded first PostData whole-array opener are merged. The owner fixture closes under MCP, but the rebased Tail goal requires a narrow requested-term correction. A private A5 guard closes two original authorizations; WithdrawalsRest needs a sound capped-module split. B1 checker unit tests pass, but TX/Tail must add two LithiumUnfold hooks before its flat baseline can merge. Optional1596c and six-package pure openers remain private.
- orch: integration is at `68efa2db`; Root merged the guarded first-array opener and Tail's B1 hook. The 07:47 periodic Iris gate on e05 failed on 44 older files after 1,874.466 s/5,199,368 KiB. Three H7 pilots have since merged, but no complete new Iris gate has established a new error count. Tail exit composition, old tuple typing, Contract.v, and the mandatory green Iris gate still block CP3; no checkpoint passed.

## Plan deviations

### Git branch names

Git rejects `islaris-native/<track>` because the existing `islaris-native` reference occupies that path. Track branches use `islaris-native-<track>`. Worktree paths remain unchanged.

### Native agent capacity

The session permits three active child agents. Five logical tracks now have separate agents. The orchestrator rotates active work within that limit. Tx and tail now have separate owners. The orchestrator proves only integration steps.

### Historical inventory

The plan gate fields cite `362fdff8`. The user and inventory identify `272909a5` as the restart boundary. The integration branch confirms `272909a5`. This run uses that boundary.

### Scratch recipe selection

A generated-trace compiler recipe can omit the project load path. The exec agent reported this failure. The orchestrator changed recipe selection to retain a project recipe when later trace compilation occurs. A regression test passes.

### Gate worker count

The decoder evidence check hardcoded 32 workers. The orchestrator changed it to use exported AGENT_JOBS. Each track can now keep its assigned 16-worker limit.

### Red Iris gate and integration hold on 2026-09-15

The 07:47 complete Iris gate failed on 44 proof files. Root continued merging despite plan section 7.3(2), which requires every merged commit to keep every lemma closed. Root did run the full gate on the six-hour schedule and did not report a checkpoint while the gate was red. The earlier gate at `a93b28c6`, which already included A1, failed on 27 files; 16 failures overlap, 28 are new, and 11 earlier failures closed. Of the 28 new files, 27 are old TX Chunk14f/150 modules, and one is a Tail import. The old PostWithdrawalsBytes.v:202 `Hmmio` error already occurred at the earlier gate. A measured 14f1c legacy A1 opt-out leaves its H7 error unchanged; Root will not apply that insufficient fallback. At the user's 10:58 review, Root stopped ordinary integrations, including the otherwise healthy queued TX and Tail commits. Auto and proof owners will apply only causally measured Round2 A4/A6 normalization fallback, plus separate narrow interface repairs for earlier failures. Only a cohesive gate-repair preview may carry these changes while the hold applies. Root will rerun complete `make check-iris` on the preview and Root before ordinary merges resume. A green focused preview alone cannot release this hold; CP3–CP5 remain open.

TX's queued B1 count-entry hook `68438283` passed a j32 preview fast gate and complete CountHandoff/NonemptyBody focused build; Root did not merge it and reset the preview to `68efa2db`. A disposable A1 opt-out closed the original AccessLists15210 lemma under MCP, but the new `Local Remove Hints subsume_instr_pre_zesu_inst` line increased that file's forbidden-name count from zero to one. TX reverted the hygiene-red change without committing. Auto will test a Hooks guard on the measured owner shape that selects the existing legacy wand without adding a proof-local opt-out or increasing the baseline.

The repair-phase CP3 dependency query used Dune's recursive `describe rules --deps --format=json` graph at Root `68efa2db`. Contract.v reaches 268 proof sources, Interfaces.v reaches 267, and Main.v reaches 153. None of the 44 files from the 07:47 Iris failure log is in any of these three current transitive closures. The exact intersection list is empty; `_build/agents/orch/logs/CP3_FAILURE_DEP_CLOSURE_2026-09-15.json` records each target and the gate-log input. This result applies to the current draft Contract.v; its closure must be checked again when final composition imports arrive. The full Iris gate remains mandatory before any ordinary merge.

The user's one-hour Step 1 scratch attribution found mixed causes. The unchanged `WriteSuccessTransactionsChunk151c4.v:53` theorem closes with pre-A1 liAStep and both local hint removals in 40.792 s, but current rules fail at `iSplit`; this is a new-rule failure. `WriteSuccessTransactionsChunk14f2c.v:103` reproduces missing H7 with current rules and again with the old-hook overlay; by the dispatch test, this belongs to regenerated trace/RAM normalization. `Chunk14f1c` closes under both scratch recipes, so that sample alone does not reproduce its periodic H7 error. The repair will use AllLegacy only for the demonstrated new-rule class and name-independent selections at failing lines for the trace/RAM class. Bulk replacement of all 43 legacy imports would leave the old-hook H7 failures red, so Root logged this least-change hybrid as a deviation. Main temporarily owns H7 repairs in `14f20,14f24,14f28,14f2c,14f34,14f3c,14f44`; TX retains the remaining early TX repairs, and Exec will receive the late `150*Load` set when a slot opens. Auto will profile ExactByteListsPublicRawPrefix under the 300 s cap. The 44 first-error file/line entries are in `_build/agents/orch/logs/IRIS_44_FILE_LINES_2026-09-15.json`.

Proposed plan section 7.3 wording, effective in this session: no ordinary merge follows a red full Iris gate; only measured repair commits enter a recovery preview. A commit touching Automation, InstrSpecs, Contracts, or Export requires a full Iris preview before merge. Auto adds a generic rule only when a manual step exceeds five lines or two sites need it; generic rules name no addresses, offsets, or predicates. Two consecutive red full gates stop integration and require a user report. Root added this wording to AGENTS.md locally and backed it up; the lead-owned plan file remains unchanged.

The user amended the repair dispatch after Step 1: stop and wait for a go-ahead before Step 2. Root stopped Auto and Main, kept Tail and TX paused, terminated the remaining focused Dune build, and reset the isolated recovery preview to clean `68efa2db`. No repair commit merged into Root, and no new full Iris gate ran. Auto's incomplete AllLegacy draft and Main's seven uncommitted H7 file edits remain isolated; Root snapshots these as text copies on the backup branch. The attribution result and zero-file current CP3 dependency intersection are the Step 1 report. Step 2 and Step 4 await the user's go-ahead.

The user gave the Step 2 go-ahead with both branches partitioned per module. Auto classified all 44 original `e05d855d` failure files by the same pre-A1 scratch test. Root froze their R/T classes under a dedicated Repair phase heading; only resolved entries may leave that list. During this phase, check-fast and no added Iris failure permit a track merge. A change under Automation, InstrSpecs, Contracts, or Export also needs a full Iris preview whose failing set is a subset of the frozen list. The strict red-gate and two-red stop amendments remain in force after the repair phase ends. Tail's 0x15980 residual is already Closed in pushed fd15a4df. Auto's bounded RawPrefix profile Closed in 144.056 s/2,503,596 KiB. `zesu_finish` is the hot internal rule at 82.225 s across 12 calls, with a 20.750 s longest call; `zesu_liAStep` took 14.056 s across 1,743 calls.

## Repair phase

The lead added `DISPATCH_PUSH3_REPAIR_2026-09-15.md` and plan section 7.6 with the 7.3(5–8) rules. Auto developed `tools/pin_hypotheses.py` privately; Root applied the reviewed exact-byte patch at `f437dc89` because Root owns `tools/`. The tool's SHA256 is `594e58a971b6578e885599e56cee7a86ce5a555ba97d3617cafe4d0a6f902146`. It uses rocq-mcp to test each compatible candidate with the next tactic, validates a pure-Coq statement selector, and logs file, line, old name, and selected statement. Ambiguous or timed-out candidates remain unresolved. Auto's unique, ambiguous, actual 14f2c no-winner, log, mode, and Closed-compile trials passed; Root's Python syntax and j16 check-fast passed. Production numbered rewrites: 0 before track tool use. Tail's `Hmmio` name and RawLoad qualifier errors are class T without numbered references; their failing-line, name-independent corrections remain scoped locally.

Auto tested the 44 original failure modules at `e05d855d` with the pre-A1 hook and both old hint removals in scratch files. The verified partition is R=11 (rules) and T=33 (traces or RAM facts). The source matches Root for 41 files; three 14f20/14f24/14f28 files changed after the frozen gate. The active list below is frozen by file and class. Remove a line only after its module compiles and its repair merges without adding an Iris failure. The initial partition artifact is `.worktrees/islaris-native-auto/_build/agents/auto/partition44/partition44.json`.

All 11 frozen class-R original sources compiled after only the All-to-AllLegacy import substitution. No original proof residual or 300 s/6 GiB cap occurred. Auto's mandatory j16 check-fast passed before its shared repair commit; Root will run a full Iris preview before that merge.

Auto's three-file AllLegacy/hygiene repair commit `0e7675c4` is pushed and staged in the isolated Root preview. The j16 Auto check-fast is green; Root has not merged it. Backup branch `islaris-native-backup` is pushed at `5dacdb15` with the frozen matrix, current progress, and private TX/Tail repair candidates. PR9 stays open and pushed at `68efa2db`.
Root's `f437dc89` commit changes only `AGENTS.md` and `tools/pin_hypotheses.py`, so the staged Auto full Iris preview has the same proof source as a preview on the new Root head. Root will restage Auto on `f437dc89` and rerun check-fast before merging. The PR9 branch is pushed at `f437dc89` and remains open.

Root's complete baseline `make check-iris CHECK_AGENT=orch AGENT_JOBS=32` at `68efa2db` exited 1 in 1,874.082 s/5,199,756 KiB. Its 41 file failures are all inside the frozen 44; it added zero failures. The three closed files are Chunk14f20, Chunk14f24, and Chunk14f28, all previously repaired and merged by `3358e803`. Their active rows shrink below, so the initial R=11/T=33 partition is now active R=11/T=30. No checkpoint is reported while the full gate is red. The specific plan 7.6 repair criterion permits red previews only when failures stay within this shrinking active set. Root treats the general 7.3(8) two-red stop as applying outside that approved subset exception; a repair preview that adds a failure stops integration and gets a user report.

Auto's shared-file full `check-iris` preview at `68efa2db` plus `0e7675c4` exited 1 in 1,826.415 s/5,221,748 KiB. Its failure set equals the 41 active frozen files; outside=0 and newly closed=0. Root `f437dc89` differs from the preview base only in `AGENTS.md` and `tools/pin_hypotheses.py`; the `check-iris` target builds `@ZesuSsz/Proofs/all` and sees identical proof sources. Root restaged the exact Auto three-file diff on `f437dc89`; j32 preview check-fast passed in 0.504 s/154,416 KiB. Root merged Auto as `33471636`; Root j32 check-fast passed in 0.768 s/629,764 KiB, and PR9 is pushed. This is a repair merge under the 7.6 subset rule; the full gate remains red and no checkpoint is reported.

MCP fallback for TX's private CP3 boundary fixture: `rocq_compile_file` Closed, but scoped `rocq_verify` timed out after 90 s in shared-defs mode; a stable file-position session returned `proof_finished=true`, and theorem-mode start could not find `writeSuccessNativeWitness`. Root approved one bounded qualified Module M scratch audit of the original 0x15668-to-0x14f04 statement. That audit Closed under the global context in 82.085 s/2,100,448 KiB with Print Assumptions. The fixture remains private and uncommitted; production use still needs a green gate.

TX used the reviewed MCP pin tool in no-write mode on original H7 copies at Chunk14f2c:103, Chunk14f3c:105, and Chunk14f44:105. The current context offered H4 (`bv_unsigned sp mod 8 = 0`), H5 (`0 ≤ bv_unsigned sp - 48`), and H6 (`bv_unsigned sp + 1896 < 1073741824`), but no candidate passed the following `rewrite; lia` tactic. The tool changed no source. Chunk14f34:105 returned an MCP timeout in theorem-prefix mode; it remains unresolved. Root requested the exact residual and one fresh-session trial before any local correction or fallback.

TX and Auto found the existing generic `zesu_bv_unsigned_Z_to_bv_small` lemma for the missing current-pointer equality. Disposable current-source MCP trials at Chunk14f2c:103/105, Chunk14f34:105/107, Chunk14f3c:105/107, and Chunk14f44:105/107 passed the replacement and the following spatial tactic. The original block statements verified with assumptions `[]`; original wrappers verified with assumptions `[]` in a qualified Module M audit. Each uses two name-free proof lines and no new rule. The Chunk14f34 timeout did not recur after `rocq_health` and a fresh copied-file session. The four tracked edits remain private until the Auto merge and mandatory track check-fast.

Approved private class-T deviations, not yet merged:

- `WriteSuccessTransactionsChunk14f2c.v:103/105`: derive the current-pointer unsigned equality with the existing generic lemma; remove the old H7 reference.
- `WriteSuccessTransactionsChunk14f34.v:105/107`: make the same measured name-free replacement.
- `WriteSuccessTransactionsChunk14f3c.v:105/107`: make the same measured name-free replacement.
- `WriteSuccessTransactionsChunk14f44.v:105/107`: make the same measured name-free replacement.

Auto's no-write pin-tool trial at frozen `WriteSuccessTransactionsChunk150a0Load.v:93` timed out in the combined theorem prefix, so it changed no source. Auto then used a stable Rocq MCP session on the unchanged prefix. `rocq_step_multi` tested context H0–H6 with the next `rewrite; lia`; none passed. The existing `zesu_bv_unsigned_Z_to_bv_small` lemma closed the missing current-pointer equality at lines 93 and 95, and the following spatial tactic passed. TX owns production validation of the unchanged block and wrapper statements; this is a proposed two-line class-T deviation, not a pin-tool production rewrite.

Class-R scope decision: Tail's queued `fd15a4df` closes the 0x15980 residual but changes five proof lines in `WriteSuccessNativeSuffixBytes15980Segment.v:85`. Root will not merge that proof edit during the import-only class-R repair. Auto's original-source C04 fixture Closed under AllLegacy in 11.029 s/1,000,104 KiB with no proof-line change. Tail keeps the closed proof as a later CP3 option.

Tail repair integration deviation: the pushed Tail branch already contains the later CP3 proof edit `fd15a4df`, while the frozen class-R repair permits only import changes. AllLegacy makes the rebased `fd15a4df` epilogue redundant and its suffix module fails with zero focused goals. Tail keeps its one worktree and branch, makes one coherent commit that reverses the redundant private proof edit and applies the two R imports, then proves the original statements. Root integrates only the final net two import lines from that commit, plus focused class-T commits, and leaves the old `fd15a4df` commit out of Root history. This keeps class-R proof text unchanged on Root.

TX repair integration deviation: its rebased branch contains the queued ordinary B1 count-entry hook `c018c2fe` before the four approved class-T source edits. Root will cherry-pick only the four-file repair commit during the red gate; it leaves the ordinary hook unmerged until a green full gate. This keeps the 7.3(5) repair exception narrow.

- 01 | R | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessWithdrawalsRest.v:92`
- 02 | R | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessAuthorizationsSecondInt.v:89`
- 03 | R | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessAuthorizationsFirstInt.v:89`
- 04 | R | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessNativeSuffixBytes15980Segment.v:85`
- 05 | R | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessAccessListsChunk15210.v:87`
- 07 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk14f1c.v:139`
- 09 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk14f68.v:265`
- 11 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk1501c.v:277`
- 12 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk15078.v:477`
- 13 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk14f2c.v:103`
- 14 | R | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessExactValueBlock.v:104`
- 15 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk15044Load.v:92`
- 16 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk14f34.v:105`
- 17 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessPostWithdrawalsBytes.v:202`
- 18 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk14f3c.v:105`
- 19 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk1509cLoad.v:93`
- 20 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk14f44.v:105`
- 21 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk150a0Load.v:93`
- 22 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk14f48.v:103`
- 23 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk14f4c.v:105`
- 24 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk150a8Load.v:93`
- 25 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsPriorityFeeSomeIntCall15134.v:152`
- 26 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk14f54.v:107`
- 27 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk150b0Load.v:93`
- 28 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk14f58.v:109`
- 29 | R | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk151c4.v:53`
- 30 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk150b4Load.v:93`
- 31 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk14f5c.v:134`
- 32 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk150bcLoad.v:93`
- 33 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk150c4Load.v:93`
- 34 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk150ccLoad.v:93`
- 35 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk14f60.v:139`
- 36 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsOptionalAddressSome15190.v:56`
- 37 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk14f64.v:209`
- 38 | R | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk153c0.v:39`
- 39 | R | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk15570Call.v:39`
- 40 | R | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk15580Call.v:39`
- 41 | R | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk15628Call.v:38`
- 42 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk15658Call.v:75`
- 43 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessTransactionsChunk153d0.v:123`
- 44 | T | `ZesuSsz/Proofs/WriteSuccess/WriteSuccessExactTailRawLoad.v:46`

## Merged commits

- `0e7675c4`: Auto's frozen AllLegacy entry and exact R hygiene baseline merged at `33471636`. The full preview failed only on the 41 active frozen files; preview and Root check-fast passed. PR9 is pushed/open.
- `35f8312`: closed hash-loop split merged at `5ce975c4`. The merge preview passed check-fast with 32 workers.
- `1ccf34e`: exact post-transactions source load merged at `5ce975c4`. The theorem retains the 69-word array and closes under the global context.

PR #9 is open: https://github.com/codygunton/zesislar/pull/9.
The remote branch is pushed at `1d91f274`. PR #9 remains open and unmerged.

- `d6ef9b5a`: exact aliases, the public target draft, main wiring, and scratch recipe corrections. Focused check: 2.014 seconds, 1209332 KiB. Check-fast: 0.573 seconds, 137328 KiB.

- `42146d0`: closed executor soundness, Phase 5.2 primitives, and 45 pilots merged at `71069ed4`. The merge preview passed check-fast in 7.470 seconds at 697288 KiB.
- `fa95823d`: closed exact withdrawal loads merged at `71069ed4`. This rebased commit has the same region proof as `7e39ada`.
- `a5637e48`: shared exact caller frame, fixed decoder preservation fields, and bounded scratch compilation. Focused gate: 66.117 seconds, 2623264 KiB. Check-fast passed.
- `77019c6f`: canonical writeFailure and zkvmExit proofs merged at `2bdbf8b2`.
- `008f628b`: feasible-branch executor refinement and the closed counterexample merged at `c583c6dd`.
- `3e2b9038`: closed unused-variable reflection merged at `ec12177f`.
- `416c351a`: closed positional read pinning merged at `623fd52a`.
- `f60992f0`: exact transaction code adapters merged at `58507407`.
- `5de7df9a`: the closed outer-loop kernel merged at `49401520`. Its iteration handoff remains a premise. CP3 needs the complete iteration proof.

The combined canonical preview passed check-fast with 32 workers. Its first gate took 224.541 seconds at 2706288 KiB. Its final gate included the updated decoder factory and all six commits. That gate took 7.685 seconds at 1061196 KiB.

- `1d91f274`: canonical configuration, four endpoint profiles, fixed decoder resources, and the closed generic contract frame theorem. Check-fast: 202.103 seconds, 2706060 KiB, 32 workers. The seven obsolete files are removed.

## Checkpoint reports

CP3, CP4, and CP5 remain open. No completion gate is claimed.

## Initial integration review

- The restart branch is clean for tracked files. Four prior untracked proof files remain preserved.
- Rocq health reports Coq 8.19.2 and pet 0.2.4-dev in the pinned switch.
- Main generated 24 glue instruction traces in a new region directory. Its trace build took 2.717 seconds and 583116 KiB.
- The shell still contains empty initial code and memory, True resource predicates, and None trace projections. These placeholders require the authorized Phase 4b integration.
- The legacy transaction interface does not retain all caller slots. New exact aliases use transactionLiveLoopState and transactionLiveLoopExit. Existing aliases remain for checked dependents.
- The draft Contract.v fixes IslarisContractCorrect 0x14d30 0x14d10 against writeSuccessNativeModel. It contains no admission and no final theorem yet.

### Decoded object address

The old zesuSuccessArgs used the input buffer address as the decoded object address. Main passes its decoded object at decodeStackPointer + 32. The orchestrator corrected this field. The change preserves the frozen decode allows and matches the writeSuccess witness relation. Main proofs will check the machine handoff.

## Historical escalation — withdrawn by user ruling

The former Phase 5.3 interpretation requested 5,929 new decoder traces. Only 10 of 5,939 expected addresses have trace definitions. Missing ranges are [0x101f8,0x12168), [0x1216c,0x14cb0), [0x15d38,0x15d40), [0x15ffc,0x161c0), and [0x161d4,0x171f8). The orchestrator requested user approval under the trace-change rule. Existing traces and the pinned binary remain unchanged. Phase 5.1, 5.2, and the other tracks continue.

### Legacy hash-loop limit

The integration build exceeded the proof module limit in WriteSuccessHashesLoop.v. The orchestrator stopped its compiler after 304.61 seconds. Sampled RSS was 3858212 KiB. The tail track must split this module at a sound boundary before another complete compile.

## Gate attempts

Initial check-fast: `make check-fast CHECK_AGENT=orch AGENT_JOBS=32`; make exit 2, Dune exit 1, Dune wall 423.875 seconds, peak child RSS 3858212 KiB. The orchestrator stopped WriteSuccessHashesLoop.v at its module limit. This gate failure has no proof residual. Tail will split the five independent checked blocks and retain the original loop composition. No checkpoint passes this gate yet.

### Incompatible helper traces

Main reported incompatible RAM assumptions. read_input a10148 and allocator a14cd4 require rv_ram_base=0x20000000 and rv_ram_size=0x20000000. write_failure a1019c and zkvm_exit a101cc require rv_ram_base=0 and rv_ram_size=0x40000000. Main glue does not change these registers. Whole-program composition needs compatible helper traces. The orchestrator requested user approval for new traces. Existing traces remain unchanged. All 24 main glue instructions have closed scratch proofs. Final module gates remain pending.

### Minimal helper trace resolution

The new helper trace scope is one instruction: 0x101cc, opcode 00a2bc23, sd a0,24(t0). Existing compatible write_success_01 output traces and the unchanged write_failure prefix can compose through a Main adapter. Existing zkvm_exit 0x101c4 and 0x101c8 have no conflicting RAM assumptions. User approval remains required only for the new 0x101cc trace. The existing exit trace stays unchanged.

### False direct decode handoff

The binding direct handoff is false at 0x14cfc. Decode returns with x1=0x14cfc. Success glue sets x1=0x14d10 before writeSuccess. Failure glue sets x1=0x14d24 before writeFailure. The exact correction gives decode exit the main dispatch registers, status memory, and endpoint memory frame. Checked glue establishes each endpoint entry. The frozen decode allows stays unchanged. The orchestrator requested user approval because the direct equality is a false binding statement. The shared decode exit remains unchanged pending approval.

## User ruling — decoder scope

The user rejected decoder trace generation. The decoder region is out of scope for every theorem. zesuCompliance retains decodeOk. zesuTerminates must take matching named decodeTerminates. Phase 5.3 proves main and the five proved endpoints only. No decoder trace generation, proof, or trace reasoning is authorized. The decoder trace dependency is withdrawn. Main trace generation remains approved.

The user owns PROJECTS.md and the active plan. The orchestrator will not edit either file again. Proposed wording belongs in this progress file. The user kept the earlier index correction.

## Proposed plan wording

Phase 5.3 proves termination for main and the five proved endpoints. The decoder region remains out of scope. zesuTerminates takes decodeTerminates as a named hypothesis. This hypothesis states decoder termination from its exact entry resources to its exact exit resources. Print Assumptions lists decodeTerminates. zesuCompliance retains decodeOk.

## User ruling — one machine configuration

The user approved canonical writeFailure and zkvmExit traces and endpoint proofs. All six endpoints and main must use one configuration. The configuration uses RAM base `0x20000000` and `zesu_sys_regs`. The binary, Islaris, and trace generator remain unchanged. Compatible readInput or allocatorGet regeneration needs no further approval.

The canonical file is `ZesuSsz/riscv64_zesu.toml`. Its contents match the checked writeSuccess configuration. The endpoint proofs use `zesu_block`. Main generated all 13 helper instruction traces. Their focused trace build passed in 1.405 seconds at 583068 KiB.

Planned removals for this approved deviation:

- `experiments/islaris-zkvm-exit/riscv64_zesu_exit.toml`
- `experiments/islaris-allocator-get/riscv64_zesu_allocator.toml`
- `experiments/islaris-write-success/riscv64_zesu_write_success.toml`
- `experiments/islaris-zkvm-exit/zkvm_exit.dump`
- `experiments/islaris-allocator-get/allocator_get.dump`
- `experiments/islaris-read-input/read_input.dump`
- `experiments/islaris-write-failure/write_failure.dump`

## Scratch memory review

NativeEntry already supplies the lower 32 bytes through writeSuccessLoadHeaderHeapResources. The nested byteLists helper needs 80 bytes below frameSp. The tail composition must preserve all 80 bytes. No public resource correction is necessary.

## User ruling — actual decode return resources

The user approved replacement of the false direct equality. The decode exit must describe the actual calling convention. The frozen allows stays unchanged. Ordinary closed zesu_block glue lemmas establish endpoint entries. Print Assumptions zesuCompliance must list decodeOk only.

Before: the decode success exit equals writeSuccess entry at `0x14d30`, including `x1=0x14d10`. The failure exit equals writeFailure entry, including `x1=0x14d24`. Neither equals the decoder return at `0x14cfc`.

After: the decode exit owns the return resources at `0x14cfc`. Those resources include preserved registers and frame, object memory, and spec_trace tail. Main's checked glue establishes each endpoint entry. The factory is `mainDecodeMachineResources` in `ZesuSsz/Contracts/DecodeMachine.v`. Its entry fixes x10=sp+32, x11=sp+16, x12=input pointer, and x13=input length. Its exit fixes x1=0x14cfc and preserves the indexed callee-saved values, saved return address, input slots, and frame padding. Main reads the status at sp+880 into x10. The decoder exit leaves x10, x11, and x12 existential. Its tail admits both permitted outcomes before the closed subset glue selects an endpoint. The allows remains unchanged.

Call-site evidence: `0x14cec` sets `a0=sp+32`. `0x14cf0` sets `a1=sp+16`. `0x14cf8` calls the decoder. `0x14cfc` loads the 16-bit status from `sp+880` into `a0`. Thus status memory precedes the branch register value. The contract must not assume an unsupported decoder return-register tag.

## Executor refinement

The executor initially selected the first structurally successful branch before it checked register conditions. An infeasible branch could precede a feasible branch. The orchestrator approved rejection of decidably false register/read/write conditions during branch selection. The returned pure conditions and seq_step soundness stay unchanged. The determinism statement stays unchanged. Exec will add a regression and repeat affected verification.

## Merge preview gate

The preview for `35f8312` and `1ccf34e` passed check-fast. Dune wall time was 261.080 seconds. Peak child RSS was 2606172 KiB. The preview used 32 workers. The actual integration gate runs separately before the shared commit.

## Executor resource limit

The refined executor test compiler reached 17766572 KiB after 22 seconds. The orchestrator stopped PID 906517. This exceeded the 6 GiB proof limit. Exec must inspect the computation and use a sound split or compact projection before another complete compile. The prior committed pilot checks remain closed.


## Automatic scratch limits

The orchestrator added automatic limits to coqc_scratch.sh. The helper stops its compiler above 300 seconds or 6 GiB RSS. The normal-path tool check passed in 0.501 seconds at 304812 KiB. The helper still reports the compiler exit, elapsed time, and peak RSS.

## Resolved escalation — Phase 5.2 branch exclusivity

The stated pinning and no-MMIO condition does not imply determinism for every permitted trace. Exec proved two_feasible_cases_counterexample under the global context. The trace contains two feasible branches. One writes PC=4. The other writes PC=8. The trace has no declarations or ReadMem event. Thus both pinning and no-MMIO requirements hold, but the completed results differ.

The committed counterexample is `ZesuSsz/Proofs/Tests/Executor.v`, theorem `two_feasible_cases_counterexample`, from `008f628b`. Print Assumptions reports Closed under the global context. Rocq verify reports assumptions=[]. The final scratch check took 1.442 seconds at 652840 KiB.

Proposed correction: the decidable condition also requires at most one feasible tcases branch. Its Boolean definition checks this condition without execution-relation premises. The determinism conclusion stays unchanged. This correction needs user approval because section 7 routes false binding statements to the user. The user approved the correction on 2026-09-14. Exec must use syntactic exclusivity where possible. A per-instruction lemma requires a reported fallback.

## Current integration boundary

The endpoint trace directories contain the 10 canonical writeFailure instructions and 3 canonical zkvmExit instructions. The integration branch uses the shared RAM configuration. The binary, Islaris, and trace generator remain unchanged. No decoder traces were generated.

Main glue and union selection are merged through 05dc5358. All glue lemmas preserve an arbitrary frame and close under the global context.

The shared resource commit removes the seven obsolete files listed in the configuration deviation. It also removes the unused zero-based register shape and its adequacy initializer. It adds canonical profiles for readInput, allocatorGet, writeFailure, and zkvmExit. The fixed decoder factory and generic contract frame theorem accompany that commit.

CP3 remains open because the outer kernel still needs its iteration handoff and exact tail composition. CP4 remains open because Main composition and the named decodeOk export are incomplete. CP5 remains open because the approved determinism correction and the composed termination theorem remain incomplete. The PR stays open and unmerged.

## Input recovery resolution

ByteString is a list of Z values. Mapping Z_to_bv 8 loses the distinction between [256] and [0]. Main must recover input from physical snapshot bytes. It must derive the byte-range invariant from that projection and construct decoder arguments from the recovered input. endpointRuns already requires projection equality. This resolution adds no premise and changes no frozen definition. A binding statement that still requires arbitrary original-list recovery must be reported.

## Initial allocator image review

The pinned ELF places alt_fl_alloc.state at 0x2401a0b0 in .bss. Its initial value is zero. The ELF places heap_buffer at 0x1a000 and input_buffer at 0x2001a000. The orchestrator rejected an invented initial allocator word of 0x30000000. Main must use the pinned initial image and report any exact resource conflict with the canonical configuration. No decoder traces are part of this review.

## Resolved escalation — pinned heap and canonical RAM

Main confirmed that NativeDataResources requires transaction and withdrawal heap addresses in [0x20000000,0x40000000). The pinned heap starts at 0x1a000. The successful handoff cannot use an invented allocator initializer. Main keeps the pinned zero word. Main continues independent failure and projection work.

Proposed least-change resolution: keep one configuration and set its RAM range to [0,0x40000000). Keep the stack bounds. Correct only heap bounds to include the pinned heap [0x1a000,0x2001a000). Regenerate affected traces for main and the five proved endpoints with unchanged binary, Islaris, and generator. Do not generate or reason about decoder traces. This proposal changes resources and traces. Plan section 5.5 requires the user ruling before implementation.

The prefix-indexed pure decoder state predicates wait for that ruling. The user approved RAM [0,0x40000000) on 2026-09-14. The shared map migration now runs. Their entry receives args, local state, global state, and the label prefix. Their exit receives the same arguments, the outcome, the final states, and the extended prefix. decodeTerminates must name that exact physical handoff.

The Main and latest independent commits passed the combined check-fast preview in 25.737 seconds at 1308976 KiB. The focused proof preview remains active. Its first invocation used a relative build path and failed before compilation. The corrected invocation uses an absolute path. No checkpoint gate is claimed from that failed invocation.


## Dispatch execution — 2026-09-14

The orchestrator read the full dispatch and the updated plan. The lead owns the plan and PROJECTS.md. The orchestrator will record proposed wording here.

- `05dc5358`: merged Main glue, snapshot recovery, failure finish, and failure outcome through `09682fa3`.
- `c806d274`: merged executor concrete pins through `5de36aeb`.
- `0a3ee3ed`: merged transaction zero-blob, live back-edge, source frame, and monotonicity through `2e029d8`.
- `fa80ea15`: merged tail stack projection through `3710b0f`.

These commits passed the combined fast preview. The shared map migration remains uncommitted. No checkpoint is claimed.

### Map migration

`Contracts/Machine.v` defines one MachineMap record and defaultMap. The RAM range is [0,0x40000000). ROM starts at 0x40002000. CLINT starts at 0x40010000. HTIF remains at 0x40001000.

The register shapes, adequacy register map, generated Level1 constants, and canonical configuration derive from this record. Proof bounds use map fields. The changed-module inventory is `_build/agents/orch/logs/MACHINE_MAP_CHANGED_MODULES.txt`.

Before: heap resources required [0x20000000,0x40000000). After: RAM bounds derive from defaultMap and include the pinned heap at 0x1a000. Stack and MMIO bounds also derive from defaultMap. Endpoint PCs retain their pinned values through machinePc offsets.

The authored Machine module stays in Contracts/Machine.v. A Dune rule copies it into the pure ZesuMachineMap theory. InstrSpecs depends on that theory. Its distinct namespace prevents a Coq theory cycle and a duplicate load-path match. The final gate verifies this structure. The foundation and trace dependency checks passed. The first fast attempts found a list-length shadow, a missing import, a load-path error, and unreduced arithmetic fields. The orchestrator corrected these shared causes. The arithmetic scratch lemma remains closed.

All existing main, endpoint, and helper traces were regenerated with the unchanged binary, Islaris, and generator. The four unused monolithic trace directories were retired. The absent decoder traces remain out of scope. No decoder traces were generated.

### Port track

Port now owns its separate worktrees and the two approved zesislar tools. Its branch uses the existing hyphen naming convention because islaris-native blocks a slash-prefixed branch.

- Binary commit `b67884e8` adds the second ELF target, linker script, start file, and runtime constants.
- Zesislar commit `b87abaf4` adds the ELF map tool.
- Zesislar commit `2f246567` adds the dry-run relocation tool.
- Zesislar commit `69094bf5` adds the layout report.

The default ELF SHA remains `3e13afeae5719e10c65a89ea1b8a9afdb60b360e7e18faa81c31a71a44dcd8fb`. All 12 QEMU vectors match the default output.

ZisK v1.2.0-alpha and OpenVM commit 16c26a32 reached the exit spin without a fault. Port used one heavy loader build at a time. [Binary PR 104](https://github.com/codygunton/binary-fv-experiment/pull/104) remains open and unmerged. Port awaits the shared map publication before its final fast gate.

### Housekeeping

All PUSH3_ORCH_*.log files moved from docs/ai/plan to `_build/agents/orch/logs/`. All new logs use that directory.

Four untracked drafts moved outside Dune sources to `_build/agents/orch/preserved-drafts/`. Their contents remain available. They are ResourceUnits.v, its test, LiveBlobFrame.v, and SignatureTailModel.v. No tracked module imported those drafts.


Current track inventory after the dispatch:

| Track | Remaining work |
|---|---|
| tx | Connect nonempty blob, authorization, and signature handoffs. Discharge the complete outer iteration. |
| tail | Compose the exact header and terminal chain. Commit root-output and the caller equivalence. Shared restoration and live-entry adapters are merged. |
| main | Finish the exact prefix. Compose the real status branch and endpoints. Complete the initial image and compliance export. |
| exec | The checker, fresh trace audit, determinism, and pilot tests are merged. Complete composed termination after CP3 through decodeTerminates. |
| port | Preparation is accepted and tools are merged. Keep binary PR 104 open. Apply no relocation before Phase 7. |

Exec's syntactic reflection scratch passed in 1.502 seconds at 656584 KiB. MCP verification returned assumptions=[]. Its preliminary fallback count is zero. The final count must use regenerated traces.

### Map gate repairs on 2026-09-14

- The ReadInput compiler reached 8,177,752 KiB after 49 seconds. The orchestrator stopped it.
- The orchestrator split the existing ReadInput module into Resources, State, Model, and Termination modules. The umbrella exports the same endpoint.
- The shared arithmetic solver converts natural bounds to binary integer bounds before arithmetic. The isolated state proof closes in 8.009 seconds with 925,732 KiB.
- The shared address rule uses the resource address instead of numbered LET variables. Two byte-list handoffs use this rule.
- The output payload lemma reached the 300-second limit during proof checking. Nat2Z.is_nonneg replaces its unnecessary arithmetic proof. Its isolated proof closes in 1.252 seconds with 630,784 KiB.
- The first map fast gate failed at these two repaired sites. The next gate runs. No checkpoint is claimed.
- Root Rocq verification cannot load this agent build directory. The verifier ignores its _CoqProject and rejects Add LoadPath. Closed scratch proofs and Dune gates provide the permitted fallback.

The regenerated inventory contains 1,023 trace modules, 998 distinct PCs, and 133 directories. Its source SHA256 is daa340ee287c8e8d43e398d16ca21ec57cf3dfb628d66b064a729b16a38a6504. The configuration SHA256 is 76a2a8f4896670b9e7c7651731abf696b2429af7863a5f07f735f8b7a006c297.

The concrete decoder resources now include the preserved input, input slots, vtable, failure payload, and exit MMIO. The decoder entry owns the pinned heap and lower scratch. The external stack window requires 2,976 bytes. It includes the 80 lower bytes, 1,896 private bytes, 104 writer bytes, and 896 main-frame bytes. The decoder allows remains unchanged.

The new lookup rule unfolds only address bindings. It preserves hidden trace bindings. Its isolated byte-list return proof reaches the existing resource continuation. The range rule now unfolds the reviewed map before it selects regions. These two fixes close the isolated return proof in 6.007 seconds with 1,094,120 KiB. Scratch declarations for preceding lemmas served only as a development context. The complete gate checks their actual proofs.

The address selector now restricts normalization to offsets from a symbolic frame base. General normalization changed the readInput selector and caused a memory failure. The restricted selector preserves that proof. The final ReadInput scratch closes in 10.514 seconds with 924,216 KiB. All three proof phases pass. Print Assumptions reports Closed under the global context. The input-size definition remains unchanged. The temporary opacity change was removed.

The final shared candidates include the array restoration rule and Export/TerminationResources.v. Both array lemmas close under the global context. Their scratch takes 2.003 seconds with 672,932 KiB. The physical resource helpers match the caller frame and keep the status slot separate. They contain no decoder traces or execution evidence.

The word-address subsumption rule closes under the global context in 1.001 seconds with 663,552 KiB. The complete byte-list handoff closes with this rule and the shared binding tactic. Its isolated scratch has no remaining goals after 26.776 seconds with 1,804,712 KiB. The complete gate verifies the actual preceding lemmas. The changed-module inventory now lists 622 Coq sources.

- `97e2729d`: applied Push 3 ruling 2. One authored MachineMap supplies register shapes, adequacy registers, Level1 constants, and the configuration. The commit includes shared address rules, array restoration, physical resource helpers, concrete decoder resources, and the ReadInput split. The fast gate passes. Its final cached run takes 3.131 seconds with 1,058,940 KiB. The preceding full run compiled the repaired proof chain. check-iris now runs against the regenerated traces. CP3, CP4, and CP5 remain open.

The orchestrator copied the fresh trace mirrors into all five track worktrees. Workers must rebase onto 97e2729d before their next proof gate. PR 9 remains open.

The native thread limit blocked resumption of the previous main thread. The orchestrator assigned the completed exec thread one bounded main task. It uses the main worktree, main build directory, and main file scope. Tx and tail retain their separate threads. Exec proof artifacts remain intact. This scheduling change preserves the five logical tracks and the limit of three active workers. Port remains ready for its final gate.

The first unified-map Iris gate failed. Its log is `_build/agents/orch/logs/PUSH3_ORCH_MACHINE_MAP_IRIS.log`. The failures include numbered LET selections, cursor lookups, and slow arithmetic proofs. The orchestrator stopped the failed gate before applying shared fixes. No checkpoint passed.

The module monitor records limit stops in `_build/agents/orch/logs/MODULE_LIMITS.jsonl`. Four suffix word modules reached 300 seconds. Tail now splits their load and assembly blocks at sound handoff boundaries. Several short arithmetic proofs also exceeded 300 seconds. The shared solver now tries integer arithmetic without unused natural bounds first.

The blob scratch statement remains true with RAM base zero. Its old intermediate claim about unsigned stack subtraction fails at stack pointer zero. The orchestrator approved direct packing at the absolute address. The shared packing rule closes under the global context in 1.502 seconds with 678,156 KiB. No contract statement or stack bound changes.

Tail commit e7222a0 passed its track fast gate. It connects ExactValuePost to transactionLiveLoopState with unchanged caller resources. The merge preview remains pending. Main also passed its migrated fast gate. CP3, CP4, and CP5 remain open.

The cursor lookup regression closes under the global context in 1.002 seconds with 647,100 KiB. It checks two offset lookups and repeated default rewrites. The unchanged remaining-list arithmetic proof closes in 1.253 seconds with 651,512 KiB. Its previous module exceeded 300 seconds.

- `f0054a24`: repaired shared cursor matching, default lookups, direct packing, and binary arithmetic. Added the MachineMap tool path. make check-fast passes in 202.849 seconds with 2,696,652 KiB at j32. The commit is pushed. Workers must rebase before their next gates.

Main commit 3dbcc3df proves the four real call instructions from 0x14cec to the decoder entry at 0x12168. Its exit matches the concrete decoder entry exactly. Its proof consumes no decoder trace. The focused build passes in 7.621 seconds with 1,166,376 KiB. Its track fast gate passes. The merge preview includes this commit and failure commit 8a7572da.

The previous preview contained stale trace mirrors. The orchestrator stopped that invalid preview gate. It copied the regenerated mirror before restarting the gate. The replacement log is `_build/agents/orch/logs/PUSH3_ORCH_MAIN_TAIL_FRESH_PREVIEW_FAST.log`.

The root-output draft now accepts a 64-bit x1 shape after the generic ABI call. The next region already accepts that shape. The public writer exit remains unchanged. Its epilogue restores the saved return address.

- `3a192f4e`: merged tail commit 89424296. Exact value resources now establish the live transaction entry. The fresh-trace preview fast gate passes in 291.664 seconds with 2,598,492 KiB at j32.
- `3bfd25c1`: merged main commits 8a7572da and 3dbcc3df. The failure path reaches its exact endpoint exit. The four real call instructions establish the concrete decoder entry. The same preview fast gate passes. The focused preview also compiles all three new modules. Their printed assumptions are closed.

The encoder scratch tests pass in 83.096 and 80.097 seconds. They use development declarations for preceding suffix lemmas. They do not establish final closed assumptions. The focused final build now checks the actual suffix proofs and both corrected encoder proofs. The blob replacement preserves its public statement exactly.

- `07046724`: repaired the exact blob scratch and both encoder dependencies. The public statements stay unchanged. The blob proof uses direct absolute-address packing. The encoder proofs expand only bitvector bindings before selection. Final compilation prints Closed for the actual proofs. make check-fast passes in 0.663 seconds with 137,252 KiB.

Port commit 2e04603b passes ten tool tests. Root review adds a multiline tuple fixture. The fixture reveals an encoded-word rewrite across a line break. The port merge waits for its guard fix and blank-line test. Root ran dry-run only. The failure log is `_build/agents/orch/logs/PORT_MULTILINE_TUPLE_AUDIT.log`.

The new array prefix rule closes and wins its selection test in 1.001 seconds with 682,260 KiB. It removes the false restoration obligations. The remaining three side conditions close in 2.004 seconds with 655,552 KiB. The shared Finish tactic handles these list shapes and equal array addresses. Its guard excludes Iris environments. The focused dependency build passes. The native scratch now tests the complete shared path.

The orchestrator briefly launched five builds during focused verification. This exceeded the intended build count. The focused root build finished without a limit failure. The orchestrator will finish one gate before it starts another heavy preview. No checkpoint performance claim uses that overlap.

- `6cb46751`: merged the transaction signature event identity. The merge preview fast gate passes in 0.624 seconds with 139,420 KiB. The focused model prints Closed.
- `9401061c`: added shared prefix restoration and list side-condition rules. The native root-output proof prints Closed in 32.538 seconds with 1,317,260 KiB. The root fast gate passes. The commit is pushed.

Port guard commit c4574d64 passes ten tool tests and four additional multiline tuple fixtures. All tests use dry-run. The default ELF stays unchanged. The binary PR 104 remains open and unmerged.

The combined preview now includes the suffix splits, header adapters, executor reflection, port tools, positive-blob handoff, and main adapters. Its fast gate runs from the current shared boundary. CP3, CP4, and CP5 remain open.

- `97416198`: added the exact caller remainder requested by tail. The existing caller statement stays unchanged. The remainder scratch passes. The whole-output proof removes numbered trace bindings and prints Closed. Its scratch takes 7.260 seconds with 835,788 KiB. Its final module prints Closed. The root fast gate passes in 0.760 seconds with 135,744 KiB.

The combined five-track preview fast gate passes in 234.014 seconds with 2,668,912 KiB at j32. Focused final compilation checks all changed proof modules.

The main alignment residual closes with existing stdpp extraction lemmas. The scratch prints Closed in 1.001 seconds with 652,724 KiB. Main keeps this bridge local. No public contract changes.

- `c70f1f31`: split four exact suffix word proofs at native handoffs. All final proofs print Closed.
- `e4fa2de2`: repaired six header and tail bindings. Their statements stay unchanged. All final proofs print Closed.
- `83b0d2c5`: connected the exact header frame to live transactions. Both lemmas print Closed.
- `df9d4c56`: closed the existing exact header transition through the live continuation. The statement stays unchanged. The lemma prints Closed.
- `71ef370e`: connected source fields at 0x153d0 to the positive-blob header. The retained predicate keeps blob bounds and the source-memory wand. The lemma prints Closed.
- `fcca89a3`: added framed input and guarded allocator contracts for main. Their resources stay unchanged. All four lemmas print Closed.
- `d83157e8`: proved executor determinism with syntactic branch exclusivity. All 1,023 scoped trace instances pass. No instruction needs the fallback. All 45 pilot proofs print Closed.
- `399bf0bd`: added the dry-run ELF map tool with an explicit inherited Sail policy.
- `a39510ae`: added the dry-run PC relocation tool and instruction checks.
- `95c7ea8f`: documented the linked map and both loader checks.
- `2e04603b`: preserved encoded words and separated the extracted address map.
- `c4574d64`: preserved multiline encoded tuple values. Ten tool tests and four additional fixtures pass.
- `693c4bde`: merged these five tracks. The combined preview fast gate passes in 234.014 seconds with 2,668,912 KiB. Focused final compilation passes for all changed proof modules. Printed proof assumptions are closed.

The integrated Iris gate now runs. Its log is `_build/agents/orch/logs/PUSH3_ORCH_MERGED_MAP_IRIS.log`. No checkpoint passed yet. PR 9 and binary PR 104 remain open and unmerged. The default ELF hash remains 3e13afeae5719e10c65a89ea1b8a9afdb60b360e7e18faa81c31a71a44dcd8fb.

The native thread limit prevents delivery to the completed port thread. This report records the accepted port preparation. The active threads keep tx, tail, and main reachable.

Pending merge reports: tx d0fc4e1f splits the wide signature proof at two existing handoffs. Tail 31f66c7 adds exact output, caller, source-fact, and trace adapters. Main 31612b6a connects the main prefix to the concrete decoder entry. Each worker reports a green fast gate and closed proof assumptions. The orchestrator has not merged these commits.

The load scratch stops at the memory limit after 24 instructions. Tail will split four eight-instruction blocks. The complete code premise includes trace_10 and trace_11. The copy scratch stops at 300.145 seconds. Tail must inspect its first residual before another attempt.

The orchestrator approves the internal fee adapter premise `mapRamBase defaultMap <= bv_unsigned sp - 32`. The complete loop supplies the stronger `sp - 48` bound. Public contract boundaries stay unchanged. Tx reuses `transactions_source_suffix_model` for the event identity.

Main reports two writer resource gaps. The existing terminal predicate omits caller registers. Its existential witness also permits a different trace tail. Before: the public resource factory existentially chooses unrelated entry and exit tails. After: an additional exact resource family fixes one tail in both boundaries and retains arbitrary x10, x11, and x12 values. The existing predicates and closed adapter statements stay unchanged. The allows and output relation stay unchanged. Tail must prove the additional exact terminal adapter from the actual epilogue. Main will consume the fixed-tail family. CP3 remains open.

The integrated Iris gate at 693c4bde fails. Its current log lists 19 proof errors. The errors include stack-index normalization, stale numbered bindings, and resource selectors. No checkpoint passed. The orchestrator tests shared repairs before another gate. The exact writer schema scratch passes in 0.751 seconds with 1,057,496 KiB. The stack-index scratch prints Closed in 32.549 seconds with 1,629,640 KiB. The copy probe reaches the concrete memcpy PC after unit unpacking and closed-address normalization. The orchestrator approves the existing packing helper sequence. Focused compilation passes for the initial schema and word-rule changes. A focused final build now checks the additional normalization changes.

Tx reports 5a9eeafb after d0fc4e1f. It connects the positive source blob to the checked family and the exact guard. Three audited lemmas print Closed. Its fast gate passes in 0.488 seconds with 141,940 KiB. The commit waits for the next merge preview.

The proposed concrete-address hint causes a memory regression. The monitor stops EncoderInt, EncoderIntCall, ExactEncoderU256Suffix, and EncoderBooleanCall at more than 6 GiB. The orchestrator removes the candidate hint. No commit contains it. The existing packing helper sequence stays approved. The recovery build recompiles affected dependencies without that hint. The exact writer schema, word rule, stack-index repair, and checked loop-carrier repair remain pending verification.

Tail reports four exact load leaves and their complete-code composition. The leaves pass in 58.968 seconds with 2,638,104 KiB. The composition passes in 13.324 seconds. Its fast gate passes in 0.511 seconds. The MCP audit remains pending. The additional exact terminal adapter scratch prints Closed in 11.769 seconds with 1,294,524 KiB. Its terminal export now retains the actual returned caller registers. The legacy terminal adapter stays unchanged.

- `926802fa`: added the fixed-tail writer family and exact terminal machine. Added the shared word-restoration rule and syntax-independent stack-index normalization. Applied the checked loop-carrier and blob MMIO selector repairs. The recovery build passes. The production word scratch prints Closed in 1.502 seconds with 1,054,932 KiB. Built-in copy normalization passes after packing. The fast gate passes in 32.455 seconds with 1,344,256 KiB at j32. The commit is pushed.

The preceding integrated Iris gate fails in 1,778.795 seconds with 4,820,760 KiB. CP3, CP4, and CP5 remain open. No current checkpoint claims a green Iris gate. The next integration batch includes the reported tx, tail, and main commits. CarrierChunk14ff0 also has a checked selector candidate pending application.

- Merged `9ee9ffe6`: the legacy transaction carrier uses the generic MMIO selector. Its statement stays unchanged. The fast gate passes.
- Merged `914b6377`: decoder frame equivalences separate the exit MMIO and failure memory. The original frame definition stays unchanged. Both lemmas print Closed. The fast gate passes.
- Preview: `595318cc`, `eb5adc9a`, and `72a39b08` pass the updated fast gate. Changed-module verification runs before integration.
- Main reports `0b5e7020`: both concrete decoder continuations print Closed. The success continuation uses the approved writer hypothesis.
- Tail reports `6cb082df`: the payload extraction lemma prints Closed. Header composition continues.
- The exact final-call adapter preserves x10, x11, x12, stack memory, object memory, MMIO, and the trace tail. The byte-list return PC is 0x159d8. The saved writer return PC is 0x14d10.
- Main uses `failureObservation` for the ByteString outcome. `failureMemory` remains the physical byte memory. The decoder allows stays unchanged.

- Merged `a0da018e`: Phase 4a: split closed wide-signature handoffs at sound boundaries. Preview fast and changed-module gates pass.
- Merged `4f0a53e7`: Phase 4a: connect native blob region and live authorization frame. Preview fast and changed-module gates pass.
- Merged `28e97037`: Phase 4a: factor exact transaction source fee resources. Preview fast and changed-module gates pass.
- Merged `6ac73eb8`: Phase 3.3: restore the exact source array after root output. Preview fast and changed-module gates pass.
- Merged `d99e239f`: Phase 3.3: project exact loop source facts from the header invariant. Preview fast and changed-module gates pass.
- Merged `53b69d7a`: Phase 3.3: connect the epilogue to exact terminal resources. Preview fast and changed-module gates pass.
- Merged `edd5d0bf`: Phase 3.3: equate the exact caller with the live value frame. Preview fast and changed-module gates pass.
- Merged `e538f6f3`: Phase 3.3: split the exact native trace at the transactions exit. Preview fast and changed-module gates pass.
- Merged `e362a9c9`: Phase 3.3: preserve exact resources across the native load region. Preview fast and changed-module gates pass.
- Merged `8c2edddc`: Phase 4a: preserve source-frame unfolding through local notation. Preview fast and changed-module gates pass.
- Merged `37fb9f68`: Phase 3.3: retain the full decoded object through the prologue copy. Preview fast and changed-module gates pass.
- Merged `595318cc`: Phase 3.3: adapt exact saved slots and returned caller resources. Preview fast and changed-module gates pass.
- Merged `eb5adc9a`: Phase 4a: connect exact positive-blob exit to fee and count. Preview fast and changed-module gates pass.
- Merged `f8b8ad50`: Phase 4b.2: compose Main prefix into exact DecodeEntry boundary. Preview fast and changed-module gates pass.
- Merged `eba07a64`: Phase 4b.2: compose Main caller into concrete decoder entry. Preview fast and changed-module gates pass.
- Merged `72a39b08`: Phase 4b.2: prove concrete success dispatch and terminal contracts. Preview fast and changed-module gates pass.
- Merged `cc1e6d87`: Phase 3 and 4b: integrate exact native boundaries. Preview fast and changed-module gates pass.
- The updated preview verifies 38 module targets. All final assumption lines report Closed. Integration head: `cc1e6d87`. CP3, CP4, and CP5 remain open.

- Merged `e85edfb2`: zero-offset memcpy cursor rules. The unchanged whole-array loop closes. Focused modules and check-fast pass.
- The automatic register packing closes the complete authorization caller fixture. The loan and restored-memory witnesses need further rules.
- The full final-call fixture closes with all registers, stack memory, object memory, MMIO, and trace resources. A reusable conversion rule remains pending.
- The Rocq service restarted automatically after exceeding its memory limit. The tail track confirmed healthy service. No toolchain changed.
- The module monitor now applies proof limits to ignored scratch proofs. The scratch compiler also enforces these limits.

- Merged `b8ec12ec`: the reusable final-call resource conversion. Both lemmas are Closed. Scratch: 8.259 s, 1,350,016 KiB. The actual module and check-fast pass.

- Pending tail export `65464c17`: the complete prefix reaches the exact transaction entry at `0x14f04`. It preserves the full object, saved slots, and caller resources. Assumptions are empty. Scratch: 19.522 s, 1,503,624 KiB. Focused build and check-fast pass.
- The restored authorization exit closes with the address-matched memory-word packing candidate. Scratch: 11.513 s, 1,460,092 KiB. The statement stays unchanged.

- PR 9 remains open from `islaris-native` to `main`. Port PR 104 remains open from `zkvm-layout` to `main`. Neither PR was merged.
- The prefix export needs a tracked proof-size repair. The tail track will split its closed composition into header/load, copy, and prologue lemmas. Its public statement and resources stay unchanged.

- The executor track identified the block-tactic defect: TRACE_LET hides the next event constructor after the word read. Unfolding TRACE_LET before instruction dispatch closes the unchanged raw suffix fixture. Scratch: 4.756 s, 849,504 KiB. The root patch awaits the healthy module gate.

- The loan diagnostic found premature framing in witness helpers. The helpers must frame only selected ownership. This preserves loan scratch memory. Selected-only tests expose a remaining packed-register form. The transaction track will inspect its exact target before another rule change.

- The current-map raw suffix repairs compile with zesu_block. The five suffix lemmas, exact contract target, and decoder termination predicate all print Closed. Assumption audit: 6.508 s, 1,351,040 KiB. The contract target needed an explicit ISA import.

- Pending prefix repair `7c530904`: load handoff, copy handoff, and public export. All three lemmas are Closed. All three MCP audits have empty assumptions. Actual module: 54.972 s, 1,576,636 KiB. Staged check-fast: 12.699 s, 1,356,484 KiB, j16. The service restarted automatically during the full-file audit. The public audit passed with compiled handoffs.

- Fixed-point scheduling closes the complete authorization caller with selected-only framing. Scratch: 6.258 s, 1,169,484 KiB. The private loan now takes `bv_unsigned sp + 1896 < machineRamEnd defaultMap`. Its caller derives this exact fact from transactionLoopSourceFacts. Public predicates stay unchanged. The retained register predicates already permit the restored Bits64 values.

- The system selector opens exact-valu register predicates and preserves general shape facts. The complete authorization exit closes with this selector and the existing four-word handoff. Scratch: 169.447 s, 5,299,292 KiB.
- Three specialized bounded loan cases close: empty/empty 169.469 s, 3,122,936 KiB; empty/nonempty 235.031 s, 3,484,912 KiB; nonempty/empty 225.261 s, 3,336,540 KiB. The fourth case remains running.
- The oversized loan stopped at 300.108 s, 4,470,368 KiB. The transaction track split it into four specialized modules, shared predicates, and a small composition.
- Pending tail `d0939fd2`: the native final byte-list call preserves complete return resources. Its statement uses metadata events. The terminal snapshot needs an additive payload variant. The root approved this variant with unchanged code and memory.
- Pending tail `2c6e160a`: the three-instruction final setup preserves the count slot and caller frame. Assumptions are empty. Actual module: 32.149 s, 1,623,404 KiB. Staged check-fast passes.

- All four specialized loan cases close within the limits. The nonempty/nonempty case takes 284.104 s and 3,701,720 KiB. The transaction track awaits the shared selector commit for production verification.
- The additive final-call payload fixture closes in 11.512 s with 1,307,520 KiB. The refactored metadata fixture also closes. Its public statement stays unchanged.
- The complete register-selector check-fast gate passes. The final suffix and contract targets compile. The final assumption audit remains pending.

- Merged `8266ba22`: Phase 3 and 5 shared packing, TRACE_LET dispatch, system selectors, and physical decoder termination definitions. Check-fast and all touched proof targets pass. Seven assumption lines are Closed. Audit: 6.508 s, 1,344,288 KiB. The physical decoder hypothesis remains an explicit definition. No decoder theorem or trace was added.

- Tail found an internal boundary defect. The load adapter forgets copied stack words as uninitialized memory. The suffix later reads these words. The root approved an additive typed stack predicate. The exact schema and preservation points remain pending. Existing closed adapters stay unchanged. The terminal contract will retain its required resources.

- Merged `146fa8eb`: additive copied-tail words and exact caller predicates in Interfaces. All 16 cells follow the pinned stores. The legacy predicates stay unchanged. Before: free stack ranges of 104 and 32 bytes. After: free 8 bytes and typed copied words. Actual Interfaces.vo and check-fast pass. Both definitions are Closed. Audit: 1.752 s, 1,260,084 KiB. Fast gate: 0.577 s, 143,620 KiB. The corrected prefix and tail exports remain pending.
- The earlier four-track preview fast gate passes in 238.874 s with 2,690,728 KiB. The root will refresh this preview with the typed boundary and latest payload commit before its proof gate.

- The tail chain needs additive exact payload adapters for calls at 0x1594c and 0x1595c and bytes calls in 0x158e0..0x15920. The root approved the existing exact encoder pattern. Legacy metadata adapters stay unchanged.
- The Rocq service rejected the transaction caller audit above its 16 GiB service limit. The service restarted automatically. The root approved the scratch/compiler fallback and a reduced final audit after recovery. No toolchain changed.
- During the preview proof gate, total CPU use measured 59.7 percent. Available memory measured 101,710,940 KiB. The gate uses j32; each track uses j16. The module monitor remains active.

- Merged `0b5e7020`: Phase 4b.2: compose concrete decoder outcomes into terminal resources. Preview fast and changed proof gates pass.
- Merged `f87373c0`: Phase 4b.2: prove whole Main contract with decoder and writer hypotheses. Preview fast and changed proof gates pass.
- Merged `98a28b24`: Phase 5.3: compose completed executor instruction runs. Preview fast and changed proof gates pass.
- Merged `2c682d8a`: Phase 4a: close both native blob branches through fee and count. Preview fast and changed proof gates pass.
- Merged `979d57c1`: Phase 4a: collect native zero-authorization code. Preview fast and changed proof gates pass.
- Merged `be2bdfe1`: Phase 4a: derive live authorization loop facts. Preview fast and changed proof gates pass.
- Merged `0ef6e6bf`: Phase 3.3: identify the exact main payload prefix. Preview fast and changed proof gates pass.
- Merged `6a2348c9`: Phase 3.3: connect exact native loads to header entry. Preview fast and changed proof gates pass.
- Merged `58b91fca`: Phase 3.3: match exact header events to output model. Preview fast and changed proof gates pass.
- Merged `c135a192`: Phase 3.3: match exact value events to output model. Preview fast and changed proof gates pass.
- Merged `a5d0776e`: Phase 3.3: derive exact prefix facts from witness resources. Preview fast and changed proof gates pass.
- Merged `4fddd2c7`: Phase 3.3: connect native entry trace to exact region events. Preview fast and changed proof gates pass.
- Merged `fa675c5c`: Phase 3.3: preserve exact frames across entry adapters. Preview fast and changed proof gates pass.
- Merged `e89313b6`: Phase 3.3: compose the exact copy frame into header resources. Preview fast and changed proof gates pass.
- Merged `ef87ba45`: Phase 3.3: derive exact prefix callee guards from native code. Preview fast and changed proof gates pass.
- Merged `cd58013c`: Phase 3.3: export the exact native prefix to transactions. Preview fast and changed proof gates pass.
- Merged `fa26dcf5`: Phase 3.3: split exact prefix composition at closed handoffs. Preview fast and changed proof gates pass.
- Merged `8e100195`: Phase 3.3: preserve exact resources through final byte-list call. Preview fast and changed proof gates pass.
- Merged `c4254c0e`: Phase 3.3: preserve exact frame through final call setup. Preview fast and changed proof gates pass.
- Merged `35627a0a`: Phase 4a: prove exact final payload call and byte-list model. Preview fast and changed proof gates pass.
- Merged `490c90ae`: integrate 20 track commits. The integration tree equals the verified preview tree. All changed proof targets and neighbor targets pass. The main factory still takes decoder and writer hypotheses. CP3, CP4, and CP5 remain open.

- Pending `fde40d46`: eight bounded authorization modules. All seven actual theorem assumptions are Closed. Focused gate: 285.915 s, 5,286,324 KiB, j16. Case times: 178.41 s, 225.45 s, 224.65 s, and 279.29 s. Fast gate: 122.658 s, 2,546,616 KiB, j16. The reduced caller and frame audits pass.
- Pending tail `5fade61f`: exact final payload setup, byte-list call, and epilogue composition. Its assumptions are empty. Actual module: 17.355 s, 1,214,092 KiB, j16. Fast gate: 24.296 s, 984,400 KiB.
- The initial decoder composition import produced a cycle through WriteFailure and DecodeMachine. The root removed the physical-contract import. The composition now takes generic entry and exit predicates. Its physical caller can instantiate these predicates. The pure composition scratch is Closed: 0.751 s, 652,732 KiB. Its final gate remains running.

- Merged `4050dbba`: generic completed-run composition through decoder boundary predicates in Adequacy. The entry and exit predicates instantiate the physical decoder hypothesis without an import cycle. Actual module and check-fast pass. All assumption lines are Closed. Fast gate: 39.465 s, 1,345,164 KiB. No decoder trace or decoder proof was added.

- The copied-word residual matches an 8-byte read against a packed word view. The shared normalizer proves bounds and a value equality before rewriting. It unfolds only two wrapper heads. Automation imports no Proofs module. The actual zesu_block regression closes automatically: 1.502 s, 701,928 KiB. Three regression assumptions are Closed. Focused PackedWordValues and All targets pass. The final fast gate runs.

- Merged `5b295b96`: packed copied-word normalization in native blocks. The three generic lemmas are Closed. The actual residual regression closes with zesu_block. Fast gate: 213.893 s, 2,688,784 KiB, j32. The tail track will verify the typed load leaves.

- The next preview freezes tx at `63f81d34` and tail at `b5e8157b`. It includes the eight authorization modules, count caller, persistent count continuation, payload setup, and final sequence. The fast and proof gates run with j32 and the shared cache. The renewed module monitor applies the required limits.

- The original eight-instruction typed load block closes with zesu_block and the shared word normalizer. Its entry definition stays unchanged. Assumptions are Closed. Scratch: 59.819 s, 2,858,304 KiB. The tail track will implement four additive typed load leaves.

- The four loan cases recompile after the shared word rule. The longest case takes 291.71 s with 3,674,200 KiB. All other cases stay below 231 s. No limit occurred. An oversized case must split at borrow and restoration boundaries before another full attempt.

- The authorization preview fast gate passes: 241.448 s, 2,694,612 KiB. Its proof gate rejects the nonempty/nonempty loan at the module limit: 301.77 s, 3,659,376 KiB. The group gate takes 527.387 s with 5,294,320 KiB. Other targets finish. The root requested a sound borrow/restoration split. The transaction track will not rerun the case unchanged. The root will merge the independent tail commits separately.

- Merged `e00e3446`: exact final payload setup. Preview check-fast and actual proof target pass.
- Merged `b5e8157b`: exact final payload sequence through the call and epilogue. Its assumptions are Closed. Preview check-fast and actual proof target pass.
- Merged `fb3f9a91`: integrate the two independent tail commits. The integration tree equals the verified preview tree. The branch is pushed.
- The typed load stage at 0x14dc0 must retain exact x10 through x13 values. These values come from offsets 800 through 824. The repaired final store leaf closes in 54.314 s with 3,129,604 KiB. The third leaf reports packed-word register subsumption. The root will extend shared automation for that goal.

- Merged `ca4a8013`: normalize packed words in register subsumption and pure BV equalities. The exact x10 residual closes with zesu_block. Five regression assumptions are Closed. Audit: 2.503 s, 707,176 KiB. Actual PackedWordValues and All targets pass. Check-fast: 223.269 s, 2,689,524 KiB, j32. The branch is pushed.
- The authorization loan split closes its borrow and restoration scratches. Borrow: 143.669 s, 3,251,876 KiB. Restoration: 188.473 s, 2,839,596 KiB. Both are Closed. The actual grouped gate runs before commit. The original bounded statement and linear loan stay unchanged.

- The next tail preview freezes `bf5d2307` after rebase onto `ca4a8013`. It includes payload calls `9024df47` and `701c805f` and five additive typed handoffs. Every new theorem is Closed. All five typed handoff MCP audits report empty assumptions. The preview proof gate waits for the current root Iris gate.

- The executor carrier diagnostic reached a folded pure invariant after its semantic tuple fixed the bytes/suffix ambiguity. The existing group opener repeatedly extracts a persistent source. The root tested selected-source removal on a minimal persistent-group lemma. Its assumptions are Closed: 2.759 s, 677,040 KiB. The exact carrier diagnostic now tests this fix. No tracked proof changed.

- The pure-source regression exposed a destruct-name hazard. Clearing the selected sep source can clear a new child with the same name. The corrected helper clears only extracted pure sources. It rejects existing pure and sep heads syntactically before guarded unfolding. Three regression lemmas are Closed, including caller-frame preservation: 4.264 s, 689,464 KiB. The exact carrier retest runs. The root will apply the shared helper after the current Iris gate.

- Pending split `61dc9267`: actual grouped gate passes in 269.307 s with 3,212,564 KiB, j16. Borrow takes 186.99 s. Restoration takes 235.46 s. The unchanged bounded theorem is Closed. Its reduced Rocq audit has empty assumptions. Fast gate: 281.141 s, 2,556,516 KiB. The preview freezes this commit with source commits `19a0bf83`, `306fe424`, and `50382423`.
- The root approved a private signature loan for nine unchanged saved words and lower16 scratch at sp-48. The retained predicate already owns that scratch. The loan must restore the original retained predicate and authorization bytes in Q. The track found two additional BitsShape64 register owners. Their corrected exact schema remains pending approval.

- The current gate hits two additional proof limits. ExactByteListsPublicPrefix: 300.64 s, 2,226,144 KiB. TransactionsCarrierChunk150ecCall: 300.07 s, 4,443,892 KiB. The root requested exact sound split boundaries. Neither module will rerun unchanged.
- The module monitor wrongly classified Export/Determinism.v as non-proof code. It contains the executor determinism proofs. The monitor killed it at 61.94 s with 960,908 KiB. The root corrected this proof module to the authorized 300 s and 6 GiB limits. Future monitor records include the worktree and classification. The actual target must pass before the merge.

- The split/typed preview fast gate fails after the monitor kills Determinism under its mistaken non-proof limit. Gate: 544.963 s, 2,696,048 KiB. The preview has no Determinism.vo; the root has its verified artifact. The corrected-limit actual target now runs before the fast gate retries.
- The root tested the actual TransactionsInvariant source with the corrected pure helper. It extracts the required invariant equation and closes within the five-second tactic bound. Its assumptions are Closed: 1.753 s, 1,065,708 KiB. The stopped carrier attempt did not identify its active tactic. A future carrier diagnostic needs explicit completion markers.

- Merged `9024df47`: Phase 3 CP3: prove exact suffix byte-list payload call at 1595c. Preview fast and actual new/neighbor proof targets pass.
- Merged `701c805f`: Phase 3 CP3: prove exact suffix byte-list payload call at 1594c. Preview fast and actual new/neighbor proof targets pass.
- Merged `bf5d2307`: Phase 3 CP3: retain copied stack words through value and caller handoffs. Preview fast and actual new/neighbor proof targets pass.
- Merged `19a0bf83`: Phase 4a: close bounded transaction authorization loans and handoffs. Preview fast and actual new/neighbor proof targets pass.
- Merged `306fe424`: Phase 4a: connect exact transaction authorization count caller. Preview fast and actual new/neighbor proof targets pass.
- Merged `50382423`: Phase 4a: close native transaction authorization count continuation. Preview fast and actual new/neighbor proof targets pass.
- Merged `61dc9267`: Phase 4a: split nonempty authorization loan at linear handoff. Preview fast and actual new/neighbor proof targets pass.
- Merged `605b71da`: integrate seven source and tail commits. The integration tree equals preview `cacb41901fba9f79ecd65811433e7fcd3b92c993`. All 20 new and three neighbor targets pass. Proof gate: 500.618 s, 5,313,772 KiB, j32. Fast gate: 0.629 s, 136,812 KiB. The branch is pushed. The transaction build slot is released. CP3, CP4, and CP5 remain open.
- Pending `ba1907ad`: four typed load leaves and their additive specification. All four assumption lines are Closed. All four final Rocq audits have empty assumptions. Actual build: 104.656 s, 2,676,504 KiB, j16. Fast gate: 54.854 s, 1,354,960 KiB. The full copied prefix remains pending.
- The existing UninitWords import closes the exact suffix payload probe. No new local rule is needed. Audit: 17.268 s, 1,603,244 KiB. Root shared exports remain pending after the current Iris gate.

- Merged `556cba38`: fix folded pure resources, export scratch-word rules, and normalize stack indices from defaultMap. Eleven regression assumptions are Closed. Check-fast: 209.411 s, 2,669,088 KiB, j32. Focused actual targets pass. The branch is pushed.
- The latest Iris gate fails: 2190.021 s, 4,926,968 KiB. Ten residual proof errors remain. The stack-index residual now passes unchanged tests. Two proof modules require sound splits before another full compilation. CP3, CP4, and CP5 remain open.
- The next preview freezes tail `84bc2c89` and transactions `2c4d4fcb` on shared base `556cba38`. It contains 23 new modules. The tail branches now report equivalent rebased commits `8d3a5e44`, `ad366fc2`, and `847e2277`. Public statements remain unchanged.
- The root approved additive payload predicates for descriptor pairs (936,944), (952,960), (968,976), and (984,992). Each predicate preserves exact payload and return resources. The root approved a preserving byte-list size lemma. Its scratch assumptions are Closed: 1.252 s, 1,047,040 KiB.

- The pending prefix/zero preview passes check-fast: 235.564 s, 2,666,616 KiB, j32. The first proof command used the wrong DecodeTermination directory. The corrected command now checks all 23 new modules and three adjacent modules.
- The exact carrier raw diagnostic closes without obsolete LET aliases. It uses the exact bytes tuple and shared folded-pure promotion. Assumptions: Closed. Scratch: 45.305 s, 2,002,124 KiB. Two additional finisher regressions are Closed: 1.502 s, 688,192 KiB. The transaction track will apply this repair after its signature block.
- The root assigned both over-limit proof splits to the executor track. The public statements and resources stay unchanged. The carrier splits into definitions, native jump, and public wrapper. The byte-list prefix splits at the encoder return PC 0x15c34.

- Pending `eb786f42`: exact private signature loan. Three actual assumption lines are Closed. All three final Rocq audits report empty assumptions. Actual grouped gate: 280.640 s, 4,037,208 KiB, j16. Final fast gate: 3.004 s, 605,552 KiB. The loan preserves register shapes and restores the original retained resources.
- The tail track strengthens only internal call families with explicit stack, payload, saved registers, and trace tail. Existing variants stay unchanged. The first 0x158f0 call is Closed: 28.533 s, 1,828,256 KiB. No public permitted input is removed.

- The prefix/zero proof preview fails at the legacy ExactValueBlock witness w2. Gate: 978.328 s, 5,267,316 KiB. No new module reaches a resource limit. The new blanket All export of UninitWords changes that legacy packing path. The root removes the blanket export. Payload modules retain explicit imports. No witness alias or public statement change is introduced.
- The signature entry reports generic valu owners with BitsShape64 facts. A shared opening rule derives typed bv64 witnesses through valu_has_bits_shape. Its three-register/frame regression is Closed: 1.252 s, 680,172 KiB. The shared gate runs before workers rebase.
- Pending `3c4528fb`: preserve byte-list resources while deriving stored size facts. The final audit has empty assumptions. Actual gate: 180.896 s, 2,295,996 KiB, j16. Fast gate: 155.889 s, 2,641,368 KiB.

- Merged `2151cd64`: expose typed BitsShape64 register witnesses and scope scratch-word instances to explicit imports. The actual shared opening regression preserves its caller frame and is Closed: 1.001 s, 681,404 KiB. Check-fast: 215.135 s, 2,691,432 KiB, j32. The branch is pushed.
- Pending `ea1daeb2`: repair the legacy carrier adapter with semantic bytes packing and shared pure closure. Both original lemmas are Closed. Final type audit has empty assumptions. Actual target: 37.205 s, 1,961,940 KiB. Fast gate: 2.318 s, 605,552 KiB.
- Pending `14608b96` and `dd7829a3`: split both over-limit modules and correct whitespace. All five proof statements are Closed. All five final audits have empty assumptions. Grouped actual gate: 117.683 s, 4,413,752 KiB. Fast gate: 162.917 s, 2,640,224 KiB. Whitespace follow-up fast gate: 0.604 s, 138,420 KiB.
- Pending `88b13ac7`: exact tail payload suffix. Its final audit has empty assumptions. Scratch: 1.502 s, 1,060,904 KiB. Focused actual target passes. Fast gate: 0.524 s, 137,164 KiB.

- The new preview freezes tail `88b13ac7`, transactions `ea1daeb2`, and split track `dd7829a3` on `2151cd64`. Check-fast passes: 248.266 s, 2,693,252 KiB, j32. The proof gate checks 36 changed modules and four adjacent modules.
- The bounded 0x151a0 diagnostic confirms its x11 value. Four scratch regions are absent before the machine handoff. The integration track will report the exact ownership boundary. No proof uses the contradictory old bound.
- Eleven legacy upper bounds in six transaction files use mapRamBase twice. Ruling 2 requires machineRamEnd defaultMap - 8. The root approved that exact internal correction. The frozen public contract remains unchanged. The integration track will log the corrected statements and rerun affected proofs.

- The root restored effective MCP use. Health reports Coq 8.19.2+lsp on the pinned islaris switch. Cached-preamble mode fails with No node at point. Stable file mode works. The root linked its private _build/default to agents/orch/default after saving the empty fallback directory. The actual shared shape regression passes rocq_start, rocq_check, rocq_step_multi, rocq_compile_file, and rocq_verify. Print Assumptions is Closed. Module M reports empty assumptions. No service restart or toolchain change occurs. Workers will try stable file mode before a preamble fallback.

- Merged `7008b4d1`: enforce MCP evidence and coordinator-approved proof fallbacks in AGENTS.md. Check-fast: 0.537 s, 148,736 KiB. The branch is pushed. All active workers accept the policy. Future main/exec dispatches will repeat it. The coordinator rejects proof commits without interactive and final MCP evidence.
- Pending `68f441de`: eleven internal RAM bound corrections. Three affected theorem audits are Closed and report empty assumptions. All six focused modules pass. Fast gate: 211.050 s, 2,696,304 KiB. The unchanged adjacent 151a0 proof also passes: 37.566 s, 2,138,272 KiB. Its original source proof passes Module M verification. No ownership rule is needed; the old impossible bounds caused the earlier residual.
- Pending `51c5e430`: five exact byte-output call families with fixed stack, payload, and trace tail. All five final audits report empty assumptions. Matching seven-target build: 383.885 s, 4,033,196 KiB. Fast gate: 217.496 s, 2,663,660 KiB.
- Pending `70404275`: two exact saved-register byte-list call families. Both statements are Closed. Stable interactive MCP, final compilation, and both Module M audits pass. Fast gate: 0.588 s, 136,836 KiB.

- The user authorizes one scoped plan edit: mark consistent MCP use as a critical condition. The root adds its gate field and section 7.1 workflow. Proof merges require MCP evidence or an exact, recorded, approved fallback. Checkpoint reports must confirm this condition. No other plan wording changes. PROJECTS.md stays unchanged.

- Merged `8d3a5e44`: CP3: preserve copied tail words through typed native loads. Preview fast and changed/adjacent proof gates pass.

- Merged `ad366fc2`: CP3: compose exact entry with the copied-word transaction caller. Preview fast and changed/adjacent proof gates pass.

- Merged `847e2277`: CP3: prove exact payload output at the 158e0 suffix call. Preview fast and changed/adjacent proof gates pass.

- Merged `58203dd9`: Phase 4a: connect exact zero-authorization continuation. Preview fast and changed/adjacent proof gates pass.

- Merged `a353e74d`: Phase 4a: factor retained live authorization resources. Preview fast and changed/adjacent proof gates pass.

- Merged `eb786f42`: Phase 4a: preserve source resources through the signature loan. Preview fast and changed/adjacent proof gates pass.

- Merged `3c4528fb`: Phase 3: preserve byte-list resources when deriving sizes. Preview fast and changed/adjacent proof gates pass.

- Merged `14608b96`: Phase 4a: split carrier call and exact byte-list prefix. Preview fast and changed/adjacent proof gates pass.

- Merged `ea1daeb2`: Phase 4a: restore semantic carrier packing and pure facts. Preview fast and changed/adjacent proof gates pass.

- Merged `dd7829a3`: Phase 4a: trim carrier call specification whitespace. Preview fast and changed/adjacent proof gates pass.

- Merged `88b13ac7`: Phase 3: identify exact tail payload fragments. Preview fast and changed/adjacent proof gates pass.

- Merged `382f1aca`: integrate eleven track commits. The tree equals verified preview `2612a2bc3f0c78861d504c22032ea548a0a92f48`. All 36 changed and four adjacent modules pass. Proof gate: 937.930 s, 5,269,944 KiB, j32. Initial fast gate: 248.266 s, 2,693,252 KiB. The final instruction sync gate passes. No new module limit occurs. The branch is pushed. CP3, CP4, and CP5 remain open.

- The 2026-09-14 amendment activates the `auto` track. Git cannot create `islaris-native/auto` while `islaris-native` exists as a branch ref, so the least-change branch is `islaris-native-auto`. The worktree, build directory, ownership, Phase order, MCP gate, and auto-first checkpoint order otherwise match the dispatch. Root transferred its uncommitted RAM-bound selector prototype to `auto` and kept no Automation edit.

- Amendment sequencing deviation: ruling-2 trace extraction and map integration already landed in `97e2729d` before the later amendment. The generated `a<addr>_spec.v` files still use `Global Existing Instance`, so A3 is absent. Auto will prepare the generator patch. Root will re-emit only the derived Rocq wrapper files from the existing traces and will not invoke Isla trace extraction again. The next `check-iris` will gate the map, existing regenerated traces, and Phase A together. This keeps one binary trace generation.

- Merged auto `89aaefd0` through integration commit `4b6ca999`: add the normalized machine-bound selector and two tests. Both tests are Closed. Root MCP start, check, step, compile_file, and original-statement verification pass with empty assumptions. Preview check-fast passes in 248.125 s with 2,693,560 KiB at j32. Auto's earlier MCP final tools could not resolve its private load path, so Root performed the required final MCP verification before merge. The branch is pushed.

- Merged auto Phase 0 `7fa3827a` through integration commit `968023a2`: add the automation-debt measurement and three unit tests. Baseline: 287 new-style modules, 315 toggle-pair files, 44 new-style callee poses, 180 new-style `Unshelve` uses, and 6/43 median/maximum `instr_body` proof lines. The benchmark takes 70.521 s overall and 19.720 s in `zesu_run`, with 2,765,868 KiB peak memory. Preview check-fast passes with 76 evidence tests. The benchmark used the approved Dune fallback after MCP could not resolve `Index.lookup`. The branch is pushed.

- Merged tail `8a564ddc`: preserve fixed byte-list payloads and exact saved registers.
- Merged tail `3f964582`: retain fixed byte-list tails and exact saved registers.
- Merged tail `72f4711c`: connect the raw byte-list trace to the exact native call.
- Merged tail `96b8bec7`: derive exact caller stack bounds.
- Merged tail `18f1c3e7`: connect the transaction exit to the raw output call.
- Merged tail `0b1aefb7`: compose the exact raw byte-list call.
- Merged tail integration `bdebcffe`. The tree equals preview `c9171364ca899eacf78f71a5bf6ee2eca5ae58f8`. All 26 changed and adjacent targets pass. The proof gate takes 314.458 s with 4,013,228 KiB peak memory at j32. Check-fast passes in 0.491 s. The branch is pushed. CP3 remains open.

- Merged exec `1ca1bb6d`: derive eleven transaction bounds from `machineRamEnd defaultMap`.
- Merged transactions `1dcde37f`: connect the exact source signature entry and return.
- Merged transactions `65dd69f4`: compose the complete source signature continuation.
- Merged transactions `a4664f81`: restore the complete source heap at the backedge.
- Merged transactions `f3209d0b`: derive authorization loop facts from source rows.
- Merged transactions `f8a778fd`: preserve the checked authorization fact export.
- Merged transactions `23279cd4`: supply complete native code to the transaction backedge.
- Merged transactions `152cb9dd`: compose the source backedge continuation.
- Merged transactions `71cfb63c`: factor live transaction composition frames.
- Merged transactions `aebd1d43`: factor the live blob field guard.
- Merged transactions `c5920c4c`: split live transaction guards.
- Merged transactions `511f9632`: normalize chunk 151ac bounds and close the final register goal with `zesu_run`.
- Merged integration `1a76e884`. The tree equals preview `fda7b0ac31c1c432ac6e3e5895d7ca615b82ef20`. Check-fast passes in 3.138 s. All 26 changed and adjacent proof targets pass in 1,004.506 s, with 5,235,676 KiB peak memory at j32. No module exceeded its limit. The branch is pushed. CP3 remains open.

- Merged auto A1 `ad0c029d` through `aa8a61bf`: add global identity-then-wand instruction continuation matching and four closed regressions. Root MCP health, start, check, step, compile, and original-statement verification pass. The warm benchmark takes 19.635 s in `zesu_run`, versus 19.720 s at baseline.
- Merged A1 integration `2d5cf9e6`: export the rule, add exact local opt-outs for Memcpy and ValueBlock, and ratchet all 321 existing legacy opt-outs. New files have a zero allowance. The preview tree equals `a9d3c3a8837f46aafa7249a01d4616e9d8337e50`. The fresh automation gate passes in 223.976 s with 2,697,420 KiB peak memory. Both legacy targets and all four regressions pass. The final check-fast passes in 2.597 s. The branch is pushed. CP3 remains open.

- A1 exposed the old manual wand mode in twelve `WriteSuccessNativeSuffix*.v` files during the full tail dependency gate. Auto approved an exact local opt-out for those files. No proof text or public statement changed. Commit `86532e00` applies and ratchets the opt-outs. The corrected suffix and tail gate passes in 201.615 s with 2,218,180 KiB peak memory.
- Merged tail `4363cf91` through integration `dac7eff0`: connect the exact raw return to the withdrawal load at `0x15678`. Its three statements are Closed and have empty MCP verification assumptions. The preview tree equals `dad1a61be71a5eebf89ef96012ac33f9f85010f4`. Check-fast passes in 2.168 s. The branch is pushed. CP3 remains open.

- Islaris emitter A3 `b519aff`: change only `frontend/decomp.ml` from `Global Existing Instance` to `#[export] Existing Instance`. The patched frontend builds. No Isla trace extraction ran. The pre-existing unrelated Islaris worktree changes remain untouched.
- Merged auto A3 `7b53e8ca` through `a93b28c6`: unfold named code lists without general `simpl`, and preserve a symbolic `S n` in the closed regression. Root MCP health, start, check, step, compile, and original-statement verification pass with empty assumptions. The preview tree equals `a7c71d00eedb86383e45d06907175100a3b49a0d`. Check-fast passes in 244.430 s with 2,691,676 KiB peak memory. The branch is pushed. CP3 remains open.

- The 2026-09-15 root `check-iris` fails in 1,638.075 s, with 5,193,668 KiB peak task memory at j32. Twenty-seven first proof errors remain. Six legacy `WriteSuccessTransactionsCarrierChunk14f*Raw.v` modules exceed the 300-second limit. The module monitor stopped their exact children. No checkpoint passed. Auto groups proven A1/A3 regressions; TX captures a sound post-load handoff; tail splits the slow ValueBlock proof.
- The root A2 preview proves and verifies `code_continuation_with_pre` through MCP with assumptions `[]`. Its `check-fast` fails because unchanged legacy `WriteSuccessValueBlock.v` reaches the 300-second limit. Tail owns the sound `0x14f04` split. Root delays the A2 merge until the gate is green.
- Staged A2+A6 preview plus six A3 suffix fallback calls and six exact old-wand selector opt-outs passes 15 changed and adjacent proof targets in 145.850 s, with 2,624,768 KiB peak memory at j32. The three hash targets that failed the last Iris gate now pass in 51.680 s. Four TX selector and continuation targets, three old tail selector targets, and post-withdrawal MMIO framing still need first residual classification. TX and tail own the proof edits after the shared merge; auto owns reusable rules. No checkpoint passed.
- The private ValueBlock handoff at `0x14ed4` previously requested two exact words. The pinned stores at `0x14ee8` and `0x14ef0` create them from uninit16 at stack offset 104. Root approved uninit16 at the private handoff, with unchanged public `0x14f04` resources. Tail logs the precise statement change and proves the suffix before merge.
- MCP selector audit: `rocq_health` reports the pinned Islaris switch and a working pet. Root preview MCP starts `OptionalAddressSome15190`, checks its exact prefix, and finds `mmio_range (604086456 + 8) 16` before the old symbolic selector. Auto's guarded normalized selector names that resource in 0.1 s. The unchanged later `iEval (rewrite !reg_col_cons reg_col_nil)` times out under MCP. Root approves only that existing remainder for a focused Dune fallback; TX must report the actual result and verify the original statement before merge. No rule or proof merge is approved by this note.
- Representative carrier fallback approval: TX's stable MCP theorem lookup for raw `0x14f8c` misses `writeSuccessTransactionsAt14f90CarrierSpec` despite a focused dependency build; stable line mode returns empty goals and `proof_finished=true` before the target theorem. Root approves a shell compiler fallback for one new post-LBU split candidate only. TX must close the unchanged original theorem, enforce 300 s/6 GiB, report the focused result, and run MCP `rocq_verify` Module M with assumptions `[]` before Root considers a merge. The six unchanged oversized modules remain stopped.
- ExactValueBlock selector diagnosis fallback: auto MCP theorem lookup misses `writeSuccessExactValueSpec`, and position mode returns an empty proof state despite Tail's focused split artifacts. Root approves one private source overlay with a single exact A1 opt-out after the split merge, followed by one focused Dune target and Module M assumption audit. This diagnosis leaves tracked source and the public theorem unchanged. No hygiene exception or proof edit is approved until the overlay result is reported.
- Tail sound split `fb83a75c` preserves `write_success_value_block` and its exact `0x14f04` exit. Its two suffix lemmas use 224 bounded callback steps. All three Print Assumptions lines are Closed; four MCP compile_file calls and three original-statement Module M audits pass with assumptions `[]`. Tail's focused target passes in 10.646 s/1,250,476 KiB and its j16 fast gate passes in 134.840 s/2,663,492 KiB. The combined A2+A6+Tail orchestrator preview fails because the unchanged ValueBlock child reaches 300.36 s/1,873,396 KiB at one core; the monitor stops only that child. Root isolates and gates Tail against a93 before the automation rules. This gate order is a least-change prerequisite for Phase A; auto owns the slow selector diagnosis. No checkpoint passed.
- Merged Tail `fb83a75c` through integration `422246b3`: the isolated a93+Tail preview check-fast passes in 130.898 s/2,223,652 KiB at j32; diff checks pass. The native public theorem and exact post remain unchanged, all three audited assumptions are `[]`, and hygiene allowances do not grow. Root pushed islaris-native through open PR 9. Tail rebased its next exact withdrawal-count entry as `2b16ad5b`. CP3 remains open.
- Merged Tail withdrawal-count entry `3b1a5178`, rebased as `2b16ad5b`, through integration `4b6f4dbf`: the model, exact count frame, and caller-entry adapter preserve the count word, witness observation, copied stack words, and downstream continuation. Four assumption lines are Closed and the original Module M audits report `[]`. Preview check-fast passes in 0.517 s/148,332 KiB; six changed and adjacent proof targets pass in 305.112 s/3,923,676 KiB at j32. No module crosses its individual limit. Root pushed PR 9. The 0x1568c call and branch composition remain open; CP3 is open.
- TX carrier hygiene coordination: the new `14f8cHead.v` replaces both copied forbidden `solve_zesu_ld_array_at` calls with the existing `zesu_run`; Head and shortened Raw both compile Closed. The original Raw's single long proof shrinks below 40 lines. Root moved its 1-long-proof/103-line allowance to Head without changing the aggregate limit, using an uncommitted coordinator-owned baseline patch in the TX worktree so TX can run its required precommit check-fast. TX commits only PostLbu, Head, and Raw. The two staged live bridges wait for A6 and a separate matching gate. Root will merge the three-file proof SHA and identical allowance transfer in one integration commit; then remove the obsolete Raw forbidden-name allowance. No committed Root state increases a ratchet. The carrier original statement stays unchanged. This coordinated gate is the least-change resolution of the precommit dependency cycle.

- Merged Tail exact withdrawal status branch `ff99d240` as integration `2edbf40f`: CountFrame factoring equals the prior frame by reflexivity, and the typed zero/nonzero branch resources preserve the first x18 slot. Proofs and assumptions are Closed. Preview check-fast passed in 0.551 s/147,852 KiB; five adjacent proof targets passed in 10.448 s/1,402,000 KiB at j32. PR 9 remains pushed and open; CP3 remains open.

- Merged TX `0x14f8c` carrier split `f283a2a7` as integration `0d56a236` with the unchanged original Raw statement: PostLbu and Head close the sound handoff, and Head replaces two forbidden array helpers with `zesu_run`. Root transferred the same 103-line allowance from Raw to Head and removed Raw's two-call hygiene allowance in the same commit. Preview check-fast passed in 0.546 s/144,784 KiB; changed and neighboring native proofs passed in 181.144 s/4,026,512 KiB at j32, with each proof below 300 s/6 GiB. Root check-fast passed in 128.714 s/2,192,532 KiB. The TX agent reported original Module M assumptions `[]` and the closed handoff lemmas; PR 9 is pushed and open. CP3 remains open.

- Merged Tail pure count-zero equivalence `8ea7d115` as integration `5509b298`: the existing exact withdrawal-count witness proves the zero branch exactly, with no instruction exclusivity premise. The lemma and its model assumptions are Closed; original-statement MCP verify returns `[]`. Preview check-fast passed in 0.505 s/145,176 KiB; four adjacent proof targets passed in 12.736 s/1,441,632 KiB at j32. Root check-fast passed in 0.752 s/149,948 KiB. PR 9 is pushed and open; the 0x1568c caller and CP3 remain open.

- Merged Tail ValueBlock local A2 hint opt-out `f6504ac8`, rebased `eefca099`, as integration `ee9b3f8b`: exactly one `Local Remove Hints subsume_instr_some_pre_inst : typeclass_instances.` follows the existing IslarisCode import. The public `write_success_value_block` statement is unchanged, Print Assumptions is Closed, and original MCP verify reports `[]`. The private late handoff with A2 priority20 returned to 14.662 s from a 15.714 s baseline; priority20 had capped at 210.033 s and priority200 at 240.034 s. Tail focused proof passed in 18.834 s/1,514,052 KiB, j16 fast101.267 s/2,189,572 KiB. Preview fast passed in 121.353 s/2,354,680 KiB and focused native proofs12.124 s/1,293,360 KiB at j32; Root fast passed in 118.664 s/2,189,500 KiB. PR9 remains pushed/open; the A2+A6 bounded ValueBlock proof passed in 18.659 s/1,544,992 KiB, and combined preview check-fast passed in 97.846 s/2,191,356 KiB at j32. A4 awaits its ratchet-flat commit before the single rule merge.

- Merged Auto Phase A2 `c6df7c87`, A6 `af238d75`, and A4 `71587c4d` as integration `36a11d5b`, with Root's single `Automation/All.v` Rewrites export: all new rules and five original test statements Print Assumptions Closed and MCP verify `[]`. Auto j16 precommit fast passed in 213.853 s/2,664,808 KiB, and its unchanged Chunk15048 max zesu_run was 17.799 s versus a 19.635 s baseline (9.35% lower). The prior A2+A6+Tail full preview passed in 97.846 s/2,191,356 KiB; full Phase A preview check-fast passed in 210.735 s/2,703,516 KiB at j32 and five test modules passed in 5.243 s/866,236 KiB. Root check-fast passed in 207.130 s/2,699,568 KiB. Debt ratchets returned to local rewrite files78, manual destructuring43, IslaTraces removals46. A sample during Root's sequential proof imports measured 3.6% total CPU, load6.03, 130.1 GiB available, and 8.0 GiB swap used; no broad CPU claim follows from this sample. PR9 is pushed and open; the deterministic existing-spec emitter wrapper update and one full Iris map/trace/rules gate follow before another checkpoint.

- Approved A3 emitter derivative after the previously completed single Isla extraction: exactly one existing instance line changed in each of the 339 ignored generated `_spec.v` modules, from `Global Existing Instance` to `#[export] Existing Instance`. The pre/post SHA256 of the sorted path-and-file corpus is `02beab3359c3e523922282999a5fb186558c187b757a13e34a43332f233074dc` / `f51bfb353b9567b2429740cff3a356a87a5be07e7bffc9010d6ca42aafcc090e`. The Root, TX, Tail, Main, and Exec trace mirrors have the same result hash; Auto links Root's mirror while testing. Traces live in ignored generated/isla-traces and are regenerated from the pinned tooling; neither raw trace data nor dump, binary, trace generator, or Islaris ISA model changed in this derivative. This is the least-change resolution of the 2026-09-14 amendment after its approved one-time Isla extraction already occurred. Five manifest files live in `_build/agents/orch/logs/EMITTER_WRAPPERS_A3_*_SHA.json`. Root check-fast with the new wrappers passed in 203.731 s/2,679,160 KiB at j32. The full Iris map/wrapper/rule gate fails before CP3; its bounded diagnostics follow.

- Root Phase A/map/A3 full `check-iris` at `36a11d5b` exited 2. The bounded log `_build/agents/orch/logs/CHECK_IRIS_PHASE_A_MAP_A3_2026-09-15.log` reports 44 first file errors: 34 older Transactions files (mostly missing `H7` after proof selection), three older authorization/withdrawal Iris resource type mismatches, and one Tail suffix native residual. The module monitor stopped `WriteSuccessExactByteListsPublicRawPrefix.v` at 300.49 s/2,201,280 KiB. Auto owns the shared selector regression; Tail and TX inspect native residuals and preserve original contracts. No checkpoint is reported and no unchanged failed gate is repeated.

- Merged Auto's urgent A6 instruction-bundle selector `9e394d5e` as integration `262cc3ea`: two exact generated-lookup regression statements and both original neighbouring BlobHashesEmit and StorageKeysLoads0 proofs close without new assumptions. Auto j16 precommit check-fast, Root j32 preview check-fast, both adjacent proof targets, and Root j32 precommit check-fast passed. The change adds only guarded matching for bundled `instr pc (Some inst) ∗ rest` and keeps debt ratchets flat. PR9 is pushed and remains open. Auto, TX, and Tail rebase once; CP3 stays open pending the older Iris residuals.

- Merged TX's two native outer-loop helpers `b690d4f5` as integration `f628621c`: current-row facts and a 28-item code bundle preserve the exact transaction-loop resources and unchanged hypotheses. Both new lemmas Print Assumptions Closed. The j32 merge preview and Root precommit `check-fast` passed; both focused proof targets passed in the preview and on Root. PR9 is pushed/open. The outer iteration premise, exit resources, and CP3 remain open.

- Merged TX's local row-word selector annotation `3824b9f3` as integration `a4a691cf`: one `#[export] Hint Unfold transactionRowWord : zesu_selectors` sits beside its TX definition. The existing gas-load contract statement is unchanged, Print Assumptions Closed, and its original MCP verification has empty assumptions. The j32 merge preview and Root precommit `check-fast` passed; the focused original GasLoads proof passed twice. Debt ratchets remain flat. PR9 is pushed/open; the outer-loop caller remains open.

- Merged Tail's six suffix hash block preamble repairs `094529dd` as integration `2cbd8967`: six existing Word0/1/2 Load/Pack `zesu_block` theorems keep their original statements and resources, and all six Print Assumptions Closed with empty MCP original-statement verification assumptions. Tail j16 fast and six-proof targets, j32 merge preview fast and six-proof targets, and Root j32 precommit fast and six-proof targets passed. PR9 is pushed/open. The suffix caller, PublicRawPrefix sound split, and CP3 remain open.

- Merged TX's canonical authorization-count factor `11008ce5` as integration `445e0eb3`: the exact current-row validity and row248 equality yield the count word, u64 bound, and 144-byte row length. The theorem is Closed; rocq_compile_file and original-statement rocq_verify return empty assumptions. TX j16 mandatory fast passed; j32 merge preview and Root fast and focused proof targets passed. PR9 is pushed/open. The zero/nonempty outer-loop handoffs and CP3 remain open.

- Merged Auto's bounded-current H7 and integer byte-word rules `bc5a83e5` as integration `141cb914`, first at this checkpoint: existing Hooks.v liAStep names the map-bounded current unsigned witness before Lithium liImpl discards it; Rewrites.v proves a universal integer-offset byte equality and a narrowly typed side-condition instance, without bitvector wrap or literal RAM range facts. Four owned public tests and six original 14f20/f24/f28 Module M statements Print Assumptions Closed and MCP verify `[]`; disposable old proof tests used exact import-order and optional rewrite pilot edits and left both original H7 rewrites unchanged. Auto j16 mandatory fast passed in 189.153 s/2,693,220 KiB, private three-original target passed in 101.676 s/1,784,324 KiB; j32 merge preview fast, two test targets, and Root precommit fast passed. Hygiene and debt ratchets remain 78/43/46. PR9 is pushed/open. TX owner must commit the three bounded import/Hstart/callback pilot fixes after its own green gates; the prior TX zero-bridge preview passed on the old Root tree and awaits re-preview on this merged rule tree. Full Iris still needs source changes before a repeat; CP3 remains open.

- The private one-lemma TX zero Hstep scratch reaches a sound final resource handoff after its native signature/count guards and exact blob-tail event/0x153d0 field guard, then hits the 300.147 s proof limit at 1,756,736 KiB. The earlier exact event/field prefix passed in 4.255 s. TX will split only that final linear Iris resource handoff, preserve the public Hstep statement/P/trace/frames and machine proof, and test one private typed handoff lemma before another full compilation. No checkpoint is valid yet.

- Merged TX's exact zero-blob and current-field bridges `a9c91859`, rebased `3c47db8a`, as integration `34eb5696`: both unchanged entry/exit handoffs are Closed and preserve the source frame and blob-tail output trace. TX private focused target passed in 73.343 s/1,695,956 KiB, mandatory j16 fast passed, ZeroBlobBridge MCP original statement verified with `[]`; FieldRegion MCP compile printed Closed, and a bounded exact-parameter `coqc_scratch` Module M audit printed Closed after MCP shared_defs verification timed out and MCP rejected `End M`. The exact rebased preview tree matched its SHA; j32 old and after-Auto preview fast and two focused targets passed, and Root precommit fast passed twice. Root removed one extra blank EOF line during integration; no proof statement or tactic changed. PR9 is pushed/open. The private zero Hstep has an exact instr_pre_wand handoff that closes in milliseconds but still needs a checked public composition. CP3 remains open.

- Merged Auto's guarded folded-tail resource selector `bf4b8d8e` as integration `f33e9a1b` before the TX helper: actual count-frame and branch mstatus/x9 regression statements Print Assumptions Closed and MCP original-statement verification returned `[]`. The unchanged native Tail status probe reached its zero-successor resource through `zesu_block; zesu_open_resource_groups; zesu_run`. Auto mandatory j16 fast passed in 211.229 s/2,692,216 KiB, final focused target passed in 161.615 s/4,044,076 KiB; Root preview j32 fast and focused actual tests passed, and Root precommit j32 fast passed. The warm unchanged benchmark took 0.803 s against the 0.731 s baseline (+9.85%, below the 10% ratchet). Debt ratchets 78/43/46 remain flat; no trace, generator, interface, or proof-owner file changed. PR9 is pushed/open. Tail must rebase and close the native zero-successor adapter; older Iris modules keep CP3 open.

- Merged Auto's exact descriptor-pure selector `d1313d67` as integration `edea1156` before the TX zero helper: two actual descriptor resource statements Print Assumptions Closed and return MCP verification assumptions `[]`. The matcher opens only a folded byte-array owner paired with the exact requested descriptor-length fact and retains the original array. Auto focused target passed in 230.615 s/2,671,604 KiB and mandatory j16 fast in 132.022 s/2,543,320 KiB; Root j32 preview fast and exact regression focused target passed, and Root j32 precommit fast passed. Auto corrected a local missing-NUL hash separator; the canonical 339 A3 wrapper corpus still matches the approved `dfab73e7` digest byte-for-byte, and no trace was changed. All debt ratchets stay flat; PR9 is pushed/open. Tail must rebase before the original 0x1568c count post-data adapter; CP3 remains open.

- Merged TX's typed zero-field-to-loop helper `6e57430b`, rebased `586bd19c` then `26313eb1`, as integration `9b92350e`: original source facts/validity, native Code, and persistent 0x153d0 current-field entry imply the exact `instr_body 0x14f08 transactionLiveLoopState` without an extra LoopState premise or changed trace/frame. MCP source compiler printed Closed and the focused source target passed; the full original theorem-mode verify timed out, so an approved exact ignored Module M audit printed Closed in 57.313 s/1,698,004 KiB. TX j16 private focused gate passed with all individual children under 300 s/6 GiB, and mandatory check-fast passed. Root j32 preview check-fast passed before and after Auto's descriptor selector; the final focused helper target passed on `edea1156`, and Root precommit j32 fast passed. The preview patch SHA equals the rebased TX patch SHA. PR9 is pushed/open. The original zero Hstep still needs a closed composition; a later clean TX pilot gate stopped an unchanged authorization-loan child at 306 s/3,465,192 KiB, so TX is splitting it at existing checked LoanRemainder handoffs. The full Iris gate and CP3 remain open.

- Merged Auto's exact tail array selectors `76d81c04` as integration `f6c7d005` before TX's loan split: four public actual tests Print Assumptions Closed and MCP original-statement verification assumptions `[]`. An explicit guarded selector opens only the exact requested first array from an anonymous hash/drop pair; another opens the exact whole `(byte array ∗ pure length)` package. Both preserve full arrays and later resources. Tail ignored native 0x15690 and 0x1568c probes reached their next owners without array splits. Auto j16 focused206.951 s/2,667,160 KiB and mandatory fast58.292 s/2,540,588 KiB passed, debt ratchets stayed flat, global Finish and All export list did not change. Root j32 preview fast and four-test focused target passed, and Root j32 precommit fast passed; PR9 is pushed/open. Controlled same-mode MCP Finish readings were clean Root0.829 s and array preview0.828 s, so these explicit rules added no measurable time. Both readings exceed the unchanged Phase A4 absolute 0.804 s limit; the absolute timing ratchet stays open for a quiet retest, with no change to its limit. CP3 remains open pending the copied Word0, TX word-image, transaction loop, Tail terminal handoffs, and full Iris gate.

- Merged TX's sound empty/nonempty authorization-loan split `8d41b475` as integration `32553b31`: two typed Borrow/Restore handoffs preserve the original `transactions_source_authorization_memory_emptynonempty` statement, its blob owners, and its loan frame. TX checked both handoffs and the original theorem through Rocq MCP with Print Assumptions Closed and original rocq_verify assumptions `[]`. TX j16 focused and mandatory check-fast passed; Root j32 preview check-fast and three focused targets passed, with each changed proof child below 300 s/6 GiB, followed by Root j32 precommit fast. The preview and rebased TX patch match. PR9 is pushed and open. Three H7 pilots remain TX-only uncommitted work, and the outer transaction loop, Tail terminal handoffs, full Iris gate, and CP3 remain open. The absolute Finish timing ratchet remains open for a quiet controlled retest.

- Merged Auto's narrowly guarded exact offset16/24 byte-word image rule `4c6198bc` as integration `e05d855d`: Rewrites.v uses the existing true integer array byte-equality theorem only for matching RVal_Bits words, and Finish.v invokes it under a two-second guard. Two public fixtures retain the original `writeSuccessTransactionWord` statements, Print Assumptions Closed, and MCP original rocq_verify assumptions `[]`; no TX source, trace, contract, or All export changed. Auto j16 focused2.483 s/1,018,084 KiB and mandatory check-fast162.884 s/2,694,572 KiB passed; Root j32 preview fast, TransactionWordImage and unchanged Finish focused, and Root j32 precommit fast passed. A quiet original MCP Finish feedback of 0.767 s passes the unchanged absolute 0.804 s warm ceiling, while debt ratchets stay flat at hints78/manual43/trace removals46/toggle320/unshelve1781. The canonical 339-wrapper trace corpus remains byte-for-byte unchanged; the temporary read-only trace link was removed. PR9 is pushed/open. TX must rebase and retest original f24/f28; copied Word0 and the Tail terminal composition remain open, and CP3 awaits a green full Iris gate.

- Periodic Root j32 `make check-iris CHECK_AGENT=orch AGENT_JOBS=32` on integration `e05d855d` began 07:47 EDT, met the six-hour interval, and exited 1 after 1,874.466 s/5,199,368 KiB with 44 first file errors and no new 300 s/6 GiB proof cap. Most failures are old TX H7 selections or old selector `No matching clauses`, including TX's original Chunk14f20/24/28 pilots; three old WithdrawalsRest/Authorizations* modules pass a Lithium tuple `(tail,suffix,prefix,prefix++suffix,processed,processed+S remaining,base,())ₗ` of type `spec *ₗ list *ₗ nat *ₗ Z *ₗ ()` where Iris expects `iProp Sigma`. Tail's 0x15980 segment and PostWithdrawalsBytes resource goals and ExactTailRawLoad export remain open. Auto owns the guarded reusable old-tuple matcher; TX and Tail own the native residuals and preserve original public statements. The full Iris gate is red, so CP3, CP4, and CP5 remain open. Root staged Auto's separate copied Word0 patch `f5cc81a8` for its required j32 preview; PR9 stays pushed/open at e05 until that gate passes.

- Merged Auto's exact first let-bound copied tail-word selector `f5cc81a8` as integration `cb014887`: ResourceGroups.v opens only a requested `(frameSp+24 ↦ₘ Word0)` first owner and retains the other fifteen copied stack words. The public original owner fixture `writeSuccessExactCopiedTailWords sp decodedBytes -∗ writeSuccessExactCopiedTailWords sp decodedBytes` compiled Closed, Print Assumptions prints `Closed under the global context`, and qualified MCP rocq_verify returned assumptions `[]`. Auto j16 focused467.782 s/2,694,656 KiB aggregate and mandatory fast43.569 s/1,355,972 KiB passed with every child below the proof caps; debt ratchets 78/43/46/320/1781 stayed flat. Root j32 preview check-fast215.005 s/2,687,988 KiB and CopiedTailWords focused target passed; Root j32 precommit fast210.870 s/2,683,424 KiB passed. The canonical trace corpus and Finish/All export list remain unchanged; PR9 is pushed/open. Tail will rebase once and test original status and CountCall probes, then the paced 0x1568c descriptor adapter. The 07:47 full Iris gate on e05 remains red on 44 older files; CP3, CP4, and CP5 remain open.

- Merged TX's unchanged zero-authorization complete iteration `6b29aa99` as Root `b81ab923`: both typed handoffs and the public original theorem Print Assumptions Closed, qualified single-lemma audit Closed, handoff MCP verify assumptions `[]`; full shared_defs MCP verify timed out at 120 s. TX j16 renamed focused passed in 1,369.013 s/5,243,112 KiB and mandatory fast127.296 s/2,581,676 KiB. Root j32 preview fast0.502 s/147,748 KiB and three focused targets1,309.501 s/5,258,716 KiB passed with all watched children below 300 s/6 GiB; Root precommit fast0.656 s/147,488 KiB passed. PR9 is pushed/open. The exact nonempty iteration, complete outer loop, terminal contract, full Iris gate, and CP3–CP5 remain open; TX's separate H7 pilots and Tail B2 commits await their own preview gates.

- Merged TX's original H7 pilots `1db24f43` as Root `3358e803`: Chunk14f20/24/28 public carrier and raw original statements compile Closed, MCP verify assumptions `[]`; f24/f28 use one built-in `Unshelve. all: try zesu_run.` for measured offset16/24 byte-word equalities, keeping H7 rewrites and statements unchanged. TX j16 focused8.513 s/1,094,612 KiB and mandatory fast0.610 s/139,564 KiB passed; Root j32 preview fast0.735 s/146,880 KiB, focused7.634 s/1,095,752 KiB, and precommit fast0.541 s/150,848 KiB passed. PR9 is pushed/open; the nonempty TX iteration and Tail B2 await preview, while the 44-error full Iris gate and CP3–CP5 remain open.

- Merged TX's unchanged nonempty-authorization complete iteration `ade495a8` as Root `395a1cb6`: typed count/field handoffs MCP verify assumptions `[]`, public original theorem compiler and scoped qualified audit Print Assumptions Closed; full shared_defs MCP verify timed out at 120 s. TX j16 focused115.150 s/1,868,616 KiB and mandatory fast0.663 s/142,052 KiB passed; Root j32 preview fast0.500 s/147,244 KiB, three focused targets286.773 s/4,830,232 KiB, and precommit fast0.532 s/147,736 KiB passed with no watched proof cap. PR9 is pushed/open; TX universal step and outer exact closure, Tail B2, terminal contract, full Iris gate, and CP3–CP5 remain open.

- Merged Tail's Phase B2 additive exact encoder-int contract `2ec0f4a3` as Root `39c1164d`: the new ret:bv64 body/pre derive from the existing native ret:Z payload body through a Closed entry adapter and `instr_pre_wand`; the old payload and public framed statements remain unchanged, and both original theorem audits return MCP assumptions `[]`. The B2 before/after statement and equivalence proof are logged in `PUSH3_tail_PROGRESS.md`; the payload, return registers, stack16, MMIO16, RAM, and output trace stay exact. Tail j16 focused78.012 s/4,117,116 KiB and mandatory fast42.453 s/1,358,016 KiB passed; Root j32 preview fast0.526 s/148,080 KiB, focused74.655 s/4,107,168 KiB, and precommit fast0.554 s/148,416 KiB passed. Full-source exact-call MCP verify restarted at its internal 30 s pet limit; the scoped original-statement MCP verify passed. PR9 is pushed/open; Tail status/CountCall and TX outer closure still block CP3, and the last full Iris gate remains red on older files.

- Proposed native-plan section 5.3 wording for lead review (Auto B1): "For each handwritten contract and proof file, `check_spec_shapes.py` ratchets uninferable existentials, predicates without `LithiumUnfold`, disjunctive specs, and frame parameters in closed specs. New files start at zero. Run its unit tests and the proof-hygiene ratchets before a checkpoint. Keep each per-file baseline flat." Auto's nine checker unit tests passed in private work. The owners must add `LithiumUnfold` hooks for `encoderIntExactReturn` and `transactionLiveNonemptyCountEntry` before the B1 checker merges. Root did not edit the lead's active plan or `PROJECTS.md`.

- Merged TX's universal exact zero/nonempty transaction step `3fe29c65` as Root `764e6d10`: the 0x14f08 Hstep has no region premise and keeps the original complete Code, persistent next-iteration guard, and exact live invariant; fresh MCP tactics Closed, compiler Closed, and qualified original-statement audit Print Assumptions Closed. Full MCP verify restarted at the 16-GiB pet limit, so the scoped audit passed in 77.579 s/1,889,984 KiB. TX j16 grouped universal/outer focused153.614 s/1,923,528 KiB and mandatory fast0.486 s/141,056 KiB passed. Root j32 preview fast0.501 s/146,604 KiB, focused universal635.183 s/4,822,164 KiB, and precommit fast0.510 s/151,172 KiB passed; all watched children remained below module caps. PR9 is pushed/open; the separate persistent outer export, Tail chain, Contract.v composition, and full Iris gate still block CP3–CP5.

- Merged TX's persistent exact outer Löb export `4cdeb42a` as Root `20d8970f`: the public statement consumes complete Code and `□ instr_pre 0x15668 (transactionLiveLoopExit ...)`, and proves `□ instr_pre 0x14f04 (transactionLiveLoopState ...)` with no new premise. Plan deviation: a proposed `instr_body 0x14f04` export could not follow from the existing Löb theorem's persistent pre, because `instr_pre_to_body` derives pre from a guarded body; Root approved the plan 3.3 persistent-pre interface without changing live predicates or the frozen contract. MCP compiler and qualified original-statement Print Assumptions Closed; full shared_defs verify timed out at 120 s, so the scoped audit passed in 77.330 s/1,896,652 KiB. TX j16 grouped focused153.614 s/1,923,528 KiB and mandatory fast0.486 s/141,056 KiB passed; Root j32 preview fast0.675 s/147,352 KiB, focused93.321 s/1,929,616 KiB, and precommit fast0.531 s/149,652 KiB passed. PR9 is pushed/open. Tail still must supply the exact 0x15668 continuation, Root must compose Contract.v, and the last full Iris gate is red; CP3–CP5 remain open.
- Merged Auto's guarded first PostData whole-array opener `9b386b5d` as Root `78245eba`: the original-owner fixture is Closed under MCP, and scoped original-statement verification lists no assumptions. Root j32 preview fast213.633 s/2,687,844 KiB, adjacent focused target1.722 s/1,094,544 KiB, and precommit fast207.756 s/2,686,424 KiB passed. Private Tail probes advance status and CountCall past the first array without splitting arrays; the rebased actual goal now needs a narrow requested-term correction. PR9 is pushed/open; CP3–CP5 remain open.
- Merged Tail's exact encoder-return B1 `LithiumUnfold` hook `44f2db39` as Root `68efa2db`: the exact return and framed caller original statements stay unchanged and MCP Closed with scoped assumptions `[]`. Tail j16 focused80.483 s/4,116,180 KiB and mandatory fast0.635 s/139,288 KiB passed. Root j32 preview fast, focused Call+Framed, and precommit fast passed; the one-instance change is pushed on PR9. CP3–CP5 remain open.
