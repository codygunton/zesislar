# Automation validation report — draft

This draft records checkpoint evidence for decodeItem and free.
It does not declare the validation complete.
The intended final destination is `docs/ai/AUTOMATION_VALIDATION_REPORT`.
The current deliverable remains under `build/stock-zisk/automation-validation/final-report/`.
The source boundary is `1caa440a0f98488e978f4ac13f046383fb26289b`, tag `cp-av-matrix-free`.
No plan file, proof, contract, or prediction changed.

## Pattern-coverage matrix

The matrix copies the measured cells from the integrated matrix checkpoint. [S09, S16]
The two free columns represent different experiments.
The hold-out result remains final after training starts.

| Pattern | decodeItem observation | Free hold-out | Best free training: run3 ON |
|---|---|---|---|
| propagate | Nine Auto blocks close | 0/12; pure equalities | 4/12 verified; eight pure range conjunctions remain |
| introduce | Two production closures; other sampled obligations remain | 0/28; equalities and pure conjunctions | 12/28 verified; 16 blocks retain pure obligations |
| store-literal | R2 retains region/index obligations | 0/1; list witness | 0/1; list witness |
| store-symbolic | No measured sample | 0/1; memory selection | 0/1; memory selection |
| return-with-frame | R3 suffix comparison remains open | 0/2; memory selection | 0/2; memory selection |
| return-without-frame | No measured sample | No measured sample | No measured sample |
| loop | Two rule-off fold-step residuals; no completed R4 comparison | No measured sample | No measured sample |
| call | No measured sample | No measured sample | No measured sample |

The original free labels have 44 instances across 43 blocks.
Block `42160` has store and return labels.
The original store count is 0/2 across the two store subtypes.
Do not sum pattern denominators.
A residual label describes the recorded first goal.
It does not identify every active goal or establish its cause.
The bound matrix retains the reported goal groups and exact first-goal text. [S09]

The nextUint64 column remains a placeholder for reviewed results.
Its ten-block prediction exists and remains explicitly predicted in the source matrix.
Contract, fold-fact, registration, profile, and bridge preparation do not establish native closure.
The alloc column remains a placeholder.
This report inspected no alloc source or results.

### Free experiment history

| Experiment | Interactive-empty blocks | Verified closures | Remaining blocks | Evidence limit |
|---|---:|---:|---:|---|
| Frozen hold-out 724 | 0 | 0/43 | 43 | Final result; the hold-out is spent [S04] |
| Training1, result758 | 0 | 0/43 | 43 | Generator and introduction changes do not revise the hold-out [S05] |
| Training2, result805 plus supplement | 12 | 12/43 | 31 | Original load-path failure and later validation stay separate [S06] |
| Training3 OFF, original854 | 12 | 6/43 | 31 | Six final compilations time out [S07] |
| Training3 ON, original854 | 16 | 8/43 | 27 | Eight final compilations time out [S07] |
| Training3 OFF, with uncapped supplement | 12 | 12/43 | 31 | The supplement verifies unchanged retained sources [S08] |
| Training3 ON, with uncapped supplement | 16 | 16/43 | 27 | This is the current best verified training result [S08] |

The first invalid launch, run706, remains a separate launch defect. [S11]
It does not replace the corrected hold-out result.
The original854 records remain immutable after the verification supplement.
An interactive-empty state alone does not prove compilation or exact verification.
All four goal groups must be considered.
Those groups are active goals, focus stack, shelved goals, and given-up goals.
The best ON result still has 27 open states and 53 active goals. [S07, S08]

### Best-training residual shapes

| Open pattern | First-goal classes | Limit |
|---|---|---|
| propagate | Eight Iris pure conditions | The rows retain cast buffer-length bounds |
| introduce | Fifteen Iris pure conditions and one pure equality | Fourteen leaf rows and two alignment/class range rows remain |
| store-literal | One list witness | The checkpoint does not select the witness |
| store-symbolic | One memory obligation | The first goal requests a memory resource |
| return-with-frame | Two memory obligations | `42160` overlaps the symbolic-store row |

The fourteen leaf rows comprise seven XOR, three literal, three subtraction, and one alignment/candidate row. [S17]
The ten range rows comprise seven buffer-bound, one alignment-bound, and two size-class rows.
The source records preserve signed/unsigned comparison spellings.
The distinct `42110` subtraction/candidate and `42130` alignment/candidate shapes remain separate.
These shapes establish no missing-rule cause or proof applicability.

## Regression limits

The plan targets at most 300 compiler CPU seconds and 6 GiB peak memory per block.
It targets zero hand lines except loops, where the limit is 20.
It also targets roughly 30 interface lines per introduced quantity.
These are report criteria, not measurements from this metadata task.

| Scope | Recorded result | Assessment |
|---|---|---|
| Production `6a08` | Three-sample median 62.944 CPU seconds; peak 1.599 GiB; manual lines 0 | Meets the recorded block targets [S01] |
| Production `6aa8` | Three-sample median 54.638 CPU seconds; peak 1.601 GiB; manual lines 0 | Meets the recorded block targets [S01] |
| R1c `6974` control | OFF median 596.866219; ON median 405.724374 CPU seconds | Accepted under the authorized relative median criterion; the absolute 300-second target remains distinct [S01] |
| Final R1d controls | Three Auto cost regressions; both targets remain open | Candidate closes failed [S01] |
| R2 final candidate | Auto CPU rises 48.685%–111.362%; native store target remains open | Candidate closes failed [S01] |
| Training3 encoding candidate | ON Auto `69e0` and `6a6c` fail Qed | Candidate remains unmerged [S07, S08] |
| Fourteen retained final compilations | Uncapped compiler CPU spans 7.731404–24.096384 seconds | Tool-side timeout records do not establish slow proof search [S08] |
| Other hand blocks | No measured rule-on manual-line count in this checkpoint set | Unknown, not zero [S01] |
| Free aggregate cost and lines per quantity | No complete matched denominator and cost series selected here | Placeholder; do not infer compliance |
| nextUint64 and alloc | Results remain outside this draft | Placeholder |

The uncapped records measure final compilation and verification of retained sources.
They do not measure new interactive search or a new native run.
CPU time, request wall time, admission time, and peak RSS remain different measures.
A fixture success does not establish a native comparison result.

## Per-function text

The six interface categories count physical lines, including comments, blank lines, and per-function JSON.
The manifest rules define exact file ranges and prevent overlap.
Block proofs, composition, tests, and exports remain separate categories.
Generic automation text remains outside the per-function interface count.
No retained old module receives deletion credit.

| Category | decodeItem original baseline | decodeItem `cp-av-r1-r3` snapshot | Free checked value-bound snapshot |
|---|---:|---:|---:|
| contracts | 2438 | 2496 | 571 |
| introductions | 3438 | 3688 | 610 |
| exit meanings | 2963 | 3114 | 109 |
| loop steps | 913 | 965 | 0 |
| registrations | 154 | 326 | 342 |
| generator JSON | 3970 | 6299 | 9503 |
| Interface total | 13876 | 16888 | 11135 |

The decodeItem values bind exact Root `6e08631942efd13d229ff7a46a01ab6a3c42384a`. [S03]
They are not a fresh recount of the report Root.
The free manifest matches the SHA recorded in its checked value-bound checkpoint. [S10, S21]
Its snapshot base is `3c8ab7b0f769176f509e16824faf675adef3674b`.
Earlier free totals omitted the then-untracked design and are not comparable complete counts. [S19]
The introduction family adds 516 interface lines under its earlier inherited counting scope. [S12]
Do not add that delta again to the later complete manifest total.
The nextUint64 and alloc counts remain placeholders in this draft.
A future report needs a matched current snapshot before comparing lines per introduced quantity.

### Hand-text measurements

| Measure | Recorded count | Scope |
|---|---:|---|
| Fifteen baseline bodies | 1106 | Nonblank lines strictly between `Proof` and `Qed`; includes automation |
| Promoted baseline bodies | 73 | The original `6a08` and `6aa8` bodies |
| Retained baseline bodies | 1033 | Thirteen remaining bodies |
| Physical hand audit | 1059 | Includes structural lines under the deterministic audit rule |
| Conditional redundancy | 52 whole lines plus 26 partial lines | No proved deletion credit |

The 1059 physical lines comprise spatial 378, machine 222, pure finisher 163, branch/handoff 137, trace/return 128, and encoding/image 31. [S01]
The mixed-line record contains 444 lines.
The spatial subset comprises output handling 130, frame/stack 67, input normalization 2, and other 179.
Output handling means literal-offset selection, bounds, callbacks, and framing for whole arrays.
It does not mean physical ownership splits.
These counts measure text, not machine instructions, execution cost, or solver coverage.
The known manual-after values are zero for `6a08` and `6aa8`.
The other thirteen manual-after values remain unknown in this evidence scope.

## Rule outcomes

| Rule or change | Checkpoint outcome | Scope limit |
|---|---|---|
| R1a plus both mask normalizers | `6a08` and `6aa8` close with `zesu_block` alone | Production promotion uses the canonical-domain data repair [S01, S15] |
| R1c | Accepted under the authorized median criterion | Correct witness assignment does not close `6a38` or `6ad8` [S01] |
| R1d / FinishFacts | Closed failed | Both native targets remain open; Auto cost failures remain recorded [S01] |
| R2 / MemoryAccess | Closed failed after three candidates | The native whole-array store obligation remains [S01] |
| R3 / ReturnRoute | First suffix comparison fails; later diagnostics remain bounded evidence | No native closure follows from successful fixtures or compositional compliance [S01] |
| R4 / LoopStep | Data facts and audits exist | No completed native ON/OFF result in this selected scope [S01] |
| E3 | Contract boundary changes | Do not credit an unmeasured paired effect to a rule [S01] |
| Free leaf introductions | Twelve conditional keyed introductions pass their data checks | The hold-out remains spent; no range becomes a new entry premise [S12] |
| Successor binding correction | Generated successors use fresh existential values | The correction is separate from rule benefit [S13] |
| Encoding candidate | Training3 ON verifies 16 blocks versus OFF12 | Auto regressions keep the candidate unmerged [S07, S08] |

The frozen free launch enables EntryIntro, both mask forms, and ConjunctMatch.
ReturnRoute, FinishFacts, and MemoryAccess remain excluded from that frozen set. [S18]
The earlier `cp-av-r1-r3` recount has a different switch scope.
Its inactive ConjunctMatch status must not replace the later freeze state. [S03]

## Completion placeholders

- The nextUint64 result section awaits its reviewed checkpoint scope.
- The alloc section awaits its authorized unseen validation and reviewed result.
- A matched final text recount remains pending.
- The final regression table needs all measured blocks and compatible timing scopes.
- Eight findings below still need immutable checkpoint evidence.
- The final root Iris gate, final report destination, and completion tag remain pending.

This draft does not declare `automation-validation-complete`.
It does not update the plan or the earlier pattern study.
It records no new proof, native comparison, or performance measurement.

## Appendix: findings F1–F51

Each numbered line gives only the supported checkpoint scope.
F1–F34 use the immutable owner-metrics snapshot bound by the Phase1 closing checkpoint. [S02, S20]
F3 and F14 include their recorded corrections.
Missing records remain placeholders.

1. **F1.** The historical RamFault comparison records 3.67 times CPU without a closure change. [S20]
2. **F2.** The initial R1a consumer changes none of its four target residuals. [S20]
3. **F3.** The initial per-step R1a consumer slows Auto controls; the later goal-side control stays within its recorded limit. [S20]
4. **F4.** Goal-side introduction advances the targets; the later successor-witness selection requires a separate repair. [S20]
5. **F5.** The profile attributes no separate EntryIntro cost; overlapping tactic percentages must not be added. [S20]
6. **F6.** Integer mask normalization advances the inequality; a separate bitvector reduction is required. [S20]
7. **F7.** The first R2 candidate leaves6b08 at its memory-region obligation. [S20]
8. **F8.** The first R2 Auto comparison exceeds its 10 percent limit at 69a4 and 6ab4. [S20]
9. **F9.** R1c selects the intended successor witnesses at 6a38/6ad8 but leaves pure obligations. [S20]
10. **F10.** The early head-only R1c candidate regresses6a14/6ab4 with provenance obligations. [S20]
11. **F11.** R3 fixtures separate valid returns from unknown or misaligned cases; fixtures do not establish native coverage. [S20]
12. **F12.** The second R2 candidate leaves6b08 open and exceeds the Auto cost limit. [S20]
13. **F13.** The historical R1c diagnosis identifies a head-only inequality assignment; later selection restricts eligible fact heads. [S20]
14. **F14.** Correction: one introduction instance existed; C1BDomain versus DomainAt caused an applicability mismatch, not duplicate-instance shadowing. [S20]
15. **F15.** Registered region controls close the target cast; unregistered and switch-off controls retain obligations. [S20]
16. **F16.** The registered-head R1c candidate selects the intended bare bigEndian payload witness. [S20]
17. **F17.** The R2 diagnostic converts the modulus spelling before selecting the array region. [S20]
18. **F18.** The per-conjunct registered-pure R1c candidate exceeds Auto cost limits. [S20]
19. **F19.** The free contract correction adds the omitted8-byte header before the first native run. [S20]
20. **F20.** R2 closes failed after three candidates; the native store obligation remains. [S20]
21. **F21.** The near-limit R1c single sample triggers the authorized three-sample median comparison. [S20]
22. **F22.** The canonical-domain data repair permits6a08/6aa8 production closure with zesu_block alone. [S20]
23. **F23.** The first-native-run tooling removes the requirement for an earlier abstract-stop baseline. [S20]
24. **F24.** R1c passes its authorized median criterion:596.866219 seconds OFF versus405.724374 seconds ON. [S20]
25. **F25.** Production medians are62.944 seconds for 6a08 and 54.638 seconds for 6aa8, with about 1.60 GiB peak memory. [S20]
26. **F26.** The first R1d comparison leaves targets open and exceeds two Auto cost limits. [S20]
27. **F27.** The early R3 suffix batch retains existential residuals; its instrumentation interruption limits coverage. [S20]
28. **F28.** The conditional redundancy audit finds52 whole-line and 26 partial-line opportunities among 1059 physical lines; it proves no deletion. [S20]
29. **F29.** Five completed R3 ON suffixes remain open; both 6b08 arms fail in common setup. [S20]
30. **F30.** R1d closes failed after its placement repair; FinishFacts remains excluded from the freeze. [S20]
31. **F31.** The 1059 physical lines classify as 378 spatial,222 machine,163 pure,137 branch,128 trace,31 image. [S20]
32. **F32.** R3 diagnostic037 stops before jalr and measures no masked-return refusal. [S20]
33. **F33.** The 378 spatial lines comprise 130 whole-array offset handling,67 frame bookkeeping,2 input normalization,179 other. [S20]
34. **F34.** R3 diagnostic040 retains folded alignment and decoder-shape differences; exposure alone does not complete the route. [S20]
35. **F35.** PLACEHOLDER: the checkpoint set lacks a sealed F35 observer-cost source.
36. **F36.** PLACEHOLDER: the checkpoint set lacks a sealed F36 filtered-observer comparison.
37. **F37.** PLACEHOLDER: the checkpoint set lacks a sealed F37 late-printer measurement.
38. **F38.** PLACEHOLDER: the checkpoint set lacks a sealed F38 trigger-trial record.
39. **F39.** Run706 is a launch defect, not the hold-out result; the separate void ruling preserves its history. [S11]
40. **F40.** PLACEHOLDER: the checkpoint set lacks a sealed F40 capture-limit measurement.
41. **F41.** The frozen free hold-out remains FINAL0/43:28 pure equalities,12 Iris pure conditions,2 memory obligations,1 list witness. [S04]
42. **F42.** Follow-up: twelve conditional leaf introductions are checked after the spent hold-out; all ranges remain implications inside facts. [S12]
43. **F43.** The successor-binding correction existentially binds successor values and preserves all 24 decodeItem generated boundaries byte-for-byte. [S13]
44. **F44.** Training1 verifies0/43 after the generator and introduction changes; it does not replace the hold-out. [S05]
45. **F45.** PLACEHOLDER: a sealed static instruction-mapping checkpoint is needed; no arithmetic-coverage cause is asserted.
46. **F46.** PLACEHOLDER: the checkpoint set lacks a sealed F46 capture-cost record.
47. **F47.** Training2 has 12 interactive-empty cases and 12 verified closures after its validation supplement;31 blocks remain open. [S06]
48. **F48.** Training3 ON has 16 interactive-empty cases;69e0/6a6c Auto regressions keep the encoding candidate unmerged. [S07]
49. **F49.** PLACEHOLDER: retain nextUint64 results for the later reviewed report; this draft reports preparation only.
50. **F50.** The separate uncapped supplement verifies all 14 retained timeout sources, giving OFF 12 and ON 16 verified closures. [S08]
51. **F51.** Training3 ON retains 10 range rows and 14 leaf rows; the leaf shapes are7 XOR,3 literal,3 subtraction,1 alignment/candidate. [S17]

## Checkpoint identities

The full untracked certificate binds every source SHA and the report bytes.
The following source labels identify immutable committed files or a checkpoint-bound snapshot.
They do not assert a fresh replay of the original proof certificates.

| Source | Checkpoint path or bound snapshot | SHA-256 |
|---|---|---|
| S01 | `phase1-closing/TABLES.md` | `080405133594f91ff5615aa6b00f16f3227fdcac5da379da385d077fd583193a` |
| S02 | `phase1-closing/CHECKPOINT.json` | `8773104dd73d86de95522eecf0ad879d955c7b5d1352f4faf22e0a975620ca72` |
| S03 | `r1-r3-root-recount/CHECKPOINT.json` | `1a8fae8e17c85cb12c2601d36886105f7abb22536817d3e410e6cc95682f444f` |
| S04 | `free-first-result/RESULT-REPORT.json` | `08f1f79f50625c7e252707fef3fce24e79982ca672e294d107842bcdf9f4ae43` |
| S05 | `free-training-1/REPORT.json` | `24b48f89f563b1c3c4724ae240315c08746582955694d4fa2a520e05d6ab397c` |
| S06 | `free-training-2/REPORT.json` | `013de5b4ccab3d119bc64af178b1d919205eb6f26ef9051c631e9a8f4b5233b7` |
| S07 | `free-training-3/REPORT.json` | `7893c8833b32b848a991458c679f009a587c4d21a9a635873533663386cfa4bc` |
| S08 | `free-training-3-uncapped/REPORT.json` | `494e2a303fb095948e5c9d379f5fbcfc3b18f92c84622de86fa8a0c88de76f1f` |
| S09 | `pattern-matrix/MATRIX.json` | `3d441a45e6b9021d5a77f43f8eb50923997afa8b4e14a9446f6d05260243b32a` |
| S10 | `free-value-bound-hints/CHECKPOINT.json` | `715cc17c2303320eac2e7bb8a805d7e0b6f8018dfffde2fcb7c9b77da16d65dd` |
| S11 | `free-first-result/F39-VOID-RUN.json` | `0b661aa75885b4dccde29eb622e582e8e8917cc38ea33f79420632dc10f30c04` |
| S12 | `free-leaf-introductions/CHECKPOINT.json` | `0e3ebf997e1e8e91313c6d1c221bb2af6c6d2eec788cb1631863ad8a5b4afcd3` |
| S13 | `free-successor-binders/CHECKPOINT.json` | `2db880755f40cce33ca67599bd9dcf21e6b7029df43a9c91a365f5e509c59e8b` |
| S14 | `free-contract-correction/CHECKPOINT.json` | `c11734038a0d0f520ae854affa1263995bda33762f928620ec19dcd0686fbc3d` |
| S15 | `r1-r3-integration/CHECKPOINT.json` | `de643b0a4d21ba80a326137ba754f395c6bda7644ac3584881c866b2cdff3f11` |
| S16 | `pattern-matrix-free/CHECKPOINT.json` | `be4005f1b9c0b4b4e0327636bff4eb90690eb8af545de58ef86a1c966e698445` |
| S17 | `free-training-3/DETAILS.json` | `247e1225e7d2c831f2b59b484fe200f0f98f7b2f8647e79abb07ecc1cb485819` |
| S18 | `rules-frozen/CHECKPOINT.json` | `5160ee86c0577a09cc8bfbadff9f1857681fb00f3a219cd147678134753ad23d` |
| S19 | `free-register-bounds/CHECKPOINT.json` | `49d293a073663ebe72fcb9cf55fe927cbc0f4b23de9392b5c6d44a2fe10cc09b` |
| S20 | `/home/cody/zesislar/.worktrees/spec-b-av-nextuint64-contracts/_build/phase1-closing-final026/METRICS.json` | `ea00709c3c3c36b9b0d4c87d26f194b1734a51d133d1a801ffdc0e3216f60433` |
| S21 | `ZesuSsz/Evidence/free_function_text.json` | `4d7d62fec811b2dc06e326424d5bf87e55e73e39b8814bd2d6f585d2a602a60d` |

All repository source rows bind report Root `1caa440a0f98488e978f4ac13f046383fb26289b`.
S20 remains an external immutable snapshot bound by S02.
S21 is the exact manifest bound by S10.
