# Automation validation report — 2026-10-17

The study produced two decodeItem promotions and twelve accepted free training closures.
The frozen free hold-out remains **0/43**.
The accepted best training result is **12/43 verified**.
The unmerged encoding candidate reached **16/43 verified**, but it broke two decodeItem controls.
Training 5 was cancelled under the user’s redirection.
This report uses recorded checkpoints only.

## 1. Why the hand suffixes existed

| Reason | Attempted method | Closing result | Evidence |
|---|---|---|---|
| Entry facts were absent from the context | Source-keyed, goal-side `ZesuEntryIntro` | Accepted; two decodeItem promotions and twelve free class closures | F3, F22, F47; Phase 1/2 tables |
| Search committed successor witnesses too early | Registered-head witness selection with a static cache | Accepted on medians; correct witnesses do not close remaining side conditions | F4, F9, F24 |
| Integer and bitvector mask arithmetic | Two mask normalizers | Accepted; contributes to the two promotions | F6, F22 |
| Cast, slice, and no-wrap side conditions | `FinishFacts` under registered bounds | Failed after two candidates; targets stay open and Auto costs exceed limits | F26, F30 |
| Output-store region selection | `MemoryAccess`, using base and literal offset | Failed after three candidates; session success did not establish native application | F7, F12, F17, F20 |
| Masked return, frame decode, alignment, and routing | `ReturnRoute` | Fixtures pass; first native comparison fails; no accepted native closure | F11, F29, F34, F38, F46 |
| Fold invariant at a back edge | Keyed `ZesuLoopStep` data facts | Audits and facts exist; no measured native rule comparison | backedge-heads checkpoint |
| Boolean path selector in the 698c join | Two explicit entry alternatives | Accepted contract convention; paired closure effect was not measured | cp-av-e3 |
| Contract and generator shape | Register-based bounds, keyed facts, fresh successor binders, and own-map lookup resources | Confirmed effect on free; twelve training closures without a new rule | F42–F44, F47, F55, F57 |
| Previously unseen instruction encodings | Encoding normalization | Four extra diagnostic closures regress two Auto controls; goal-only candidate gives no gain; work closes unsolved | F45, F48, F52, F56 |
| Boxed callee installation | Compositional contract and a proved bridge | Bridge proved; caller operation returns no response at its CPU bound; no hang location is established | compositional-exit and bridge checkpoints; F53 |

Four reasons acquired accepted methods: entry introduction, witness assignment, mask arithmetic, and join selection.
The join result is a contract convention, not measured paired proof closure.
Contract phrasing also produced the largest measured transfer gain.
Stores, returns, finisher conditions, encodings, loops, and calls remain open automation questions.
The suffix-reasons source predates the redirection; its pending final encoding candidate was cancelled.

## 2. Phase 1 closing tables

### Rule results

| Item | Result | Limit |
|---|---|---|
| R1a + R1b + R1b′ | `6a08` and `6aa8` close with `zesu_block` alone | Canonical-domain data repair forms part of the production scope |
| R1c | Accepted under the authorized median criterion | Correct witnesses at `6a38`/`6ad8`; pure obligations remain |
| R1d | Closed failed after two candidates | Three final Auto cost failures; both target proofs remain open |
| R2 | Closed failed after three candidates | Native store target remains; final Auto costs rise 48.685%–111.362% |
| R3 | First suffix comparison failed | Five completed ON suffixes remain open; `6b08` fails in common setup |
| R4 | Data facts and back-edge audits only | No completed native ON/OFF comparison |
| E3 | Flat Literal/ShortString entries integrated | No measured final paired closure benefit |

The R1c same-tip medians are 596.866219 CPU seconds OFF and 405.724374 ON, a 32.024236% decrease.
The earlier failed single-sample comparison remains recorded separately.
Relative acceptance does not establish the absolute 300-second block target.

| Production promotion | Median compiler CPU seconds | Peak GiB | Samples | Manual lines after promotion |
|---|---:|---:|---:|---:|
| `6a08` | 62.944 | 1.599 | 3 | 0 |
| `6aa8` | 54.638 | 1.601 | 3 | 0 |

The baseline counts nonblank body lines strictly between `Proof` and `Qed`, including automation.
The manual-after column uses a different measure.
Unknown manual-after values do not mean zero.

| Block | Baseline body lines | Manual after |
|---|---:|---:|
| `6960` | 66 | Unknown |
| `697c` | 63 | Unknown |
| `698c` | 78 | Unknown |
| `69b0` | 90 | Unknown |
| `69e8` | 73 | Unknown |
| `6a08` | 49 | 0 |
| `6a24` | 158 | Unknown |
| `6a38` | 29 | Unknown |
| `6a40` | 60 | Unknown |
| `6a78` | 89 | Unknown |
| `6aa8` | 24 | 0 |
| `6ac4` | 169 | Unknown |
| `6ad8` | 66 | Unknown |
| `6ae0` | 71 | Unknown |
| `6b08` | 21 | Unknown |
| Total | 1106 | Two measured zeros; thirteen unknowns |

The promoted baseline bodies contain 73 lines.
The retained baseline bodies contain 1033 lines.
The separate physical audit counts 1059 lines, including structural lines, at exact Root `6e086319`.
Each line receives one primary kind under a deterministic priority rule.

| Primary kind | Physical lines |
|---|---:|
| Spatial reasoning | 378 |
| Machine steps | 222 |
| Pure finishing | 163 |
| Branch/case handoff | 137 |
| Trace lookup/return | 128 |
| Encoding/image facts | 31 |
| Total | 1059 |

The spatial subset contains 130 output-offset lines, 67 frame/stack lines, two input-normalization lines, and 179 other lines.
Output-offset work selects, bounds, calls back, and frames whole arrays; it does not physically split ownership.
The redundancy audit identifies 52 whole-line and 26 partial-line conditional opportunities.
These 78 opportunities prove no native deletion.
Mixed and structural lines remain separately documented in the source audits.

## 3. Phase 2 closing tables

| Run | Interactive-empty blocks | Verified closures | Control/integration limit |
|---|---:|---:|---|
| Frozen hold-out 724 | 0 | 0/43 | Final spent hold-out |
| Training 1, 758 | 0 | 0/43 | Generator and introduction changes do not revise the hold-out |
| Training 2, original 805 | 12 | 0/43 | Compilation environment fails before validation |
| Training 2, validation 810 | 12 | 12/43 | Same statements verified after loadpath repair |
| Training 3 OFF, original 854 | 12 | 6/43 | Six final compilations time out |
| Training 3 ON, original 854 | 16 | 8/43 | Eight final compilations time out; two Auto regressions |
| Training 3 OFF, supplement 872 | 12 | 12/43 | Existing retained sources validated; no new native run |
| Training 3 ON, supplement 872 | 16 | 16/43 | Diagnostic result only; candidate remains unmerged |
| Training 4 OFF, 995 | 12 | 12/43 | Nine Auto controls pass |
| Training 4 ON, 995 | 12 | 12/43 | Nine Auto controls pass; maximum recorded CPU change +4.94% |
| Final candidate / Training 5 | Not run | Not run | Cancelled by user ruling |

The accepted best training result is twelve verified closures, not sixteen.
The sixteen-closure arm fails Auto blocks `69e0` and `6a6c`.
The uncapped supplement does not erase those regressions.
Its fourteen compilations take 7.7–24.1 compiler CPU seconds.
Those measurements do not time a new native search.
Training 4 produces no leaf gain and loses the four diagnostic range closures.
Its 31 open states retain 61 active goals.

The initial hold-out contains 28 pure equalities, twelve Iris pure conditions, two memory goals, and one list witness.
Later first-goal classifications describe exported shapes, not proof-failure causes.
Void launches, compilation failures, interactive closure, and verified closure remain separate outcomes.

## 4. Pattern coverage

| Pattern | decodeItem observation | Free hold-out | Accepted free training | nextUint64 | Alloc |
|---|---|---|---|---|---|
| Propagate | Nine baseline Auto blocks close | 0/12 | 0/12; range conditions remain | Pending continuation | Not run |
| Introduce | Two production promotions; remaining side conditions | 0/28 | 12/28; sixteen entries remain open | Pending continuation | Not run |
| Store, literal offset | Region/index residuals | 0/1; list witness | 0/1; list witness | Pending continuation | Not run |
| Store, symbolic offset | No measured sample | 0/1; memory goal | 0/1; memory goal | Pending continuation | Not run |
| Return, with frame | Native suffix comparison remains open | 0/2; memory goals | 0/2; memory goals | Pending continuation | Not run |
| Return, without frame | No measured sample | No sample | No sample | Pending continuation | Not run |
| Loop | Two rule-off fold residuals; no completed R4 comparison | No sample | No sample | Pending continuation | Not run |
| Call | No measured sample | No sample | No sample | Pending continuation | Not run |

The exact nextUint64 result status is **pending the bounded six-block continuation**.
No per-pattern closure fraction is inferred from its partial results.
The accepted free column uses the twelve-closure checkpoint, not the historical run3 ON matrix column.
The historical run3 ON column records four propagation closures and twelve introduction closures.
It remains diagnostic evidence because its candidate regresses two controls.
C’s closing snapshot preserves that historical column and marks nextUint64 pending.
Pattern labels overlap; denominators must not be summed.
Free has 44 labels across 43 blocks because `42160` has store and return labels.
Alloc is **NOT RUN**, reserved unread.

## 5. Per-function text

Counts use physical lines, including comments, blank lines, registration text, and per-function JSON.
The six interface categories exclude generic automation, block proofs, composition, tests, and exports.
These are checkpoint snapshots, not a new current-main recount.

| Category | decodeItem baseline | decodeItem integrated | Free fully counted | nextUint64 |
|---|---:|---:|---:|---:|
| Contracts | 2438 | 2496 | 571 | 643 |
| Introductions | 3438 | 3688 | 781 | 0 |
| Exit meanings | 2963 | 3114 | 109 | 79 |
| Loop steps | 913 | 965 | 0 | 229 |
| Registrations | 154 | 326 | 343 | 111 |
| Generator JSON | 3970 | 6299 | 9503 | 4128 |
| Total | 13876 | 16888 | 11307 | 5190 |

Free grows from the recorded 983-line early scope to 11307 fully counted lines.
Of its apparent 9419-line jump at the register-bound snapshot, 9392 lines expand the counting scope.
The remaining 27 lines change the inherited scope.
The expanded generator category includes design/profile JSON and source-embedded tables.
The later 171-line ite family and one-line umbrella export remain counted despite no isolated closure benefit.
Retained helper modules receive no deletion credit.
The decodeItem integrated count binds `cp-av-r1-r3`; it is not a fresh report-root count.

## 6. nextUint64 and reserved scope

**Status: pending the bounded six-block continuation.**

The fixed non-call scope is Root `f58fde97`, with nine boundaries; caller entry `6274` is excluded.
The available evidence records residuals at `62b8` and `62c0`; their exact bindings appear below.
Block `62cc` stops without a response; its final Pet CPU is 15856.67 seconds, or 4.40463 hours.
The stop record retains the label “no response within 4.2 CPU-hours”.
No hang location is established.
The continuation records a `62d8` residual with three active goals and first goal `FindMemMapsTo`.
Its aggregate CPU is 100.66573 seconds, and owned closure is complete.
The six-block continuation includes this completed `62d8` attempt; five proof entries remain unexecuted.
The `62e4` attempt is a launch defect with zero primary calls.
These partial records are not a complete nine-block result.
The records support no completed-instruction count for any row.
Prediction [6191876275](https://github.com/codygunton/zesislar/issues/13#issuecomment-6191876275) remains unchanged.
The ten-block inventory includes nine non-call blocks and one caller block.
The caller is not rerun for this closing report.
Caller record 924 observes 7200.8 Pet CPU seconds without a response at Root `bdac7cf9`.
Instruction progress, call return, and the residual are unavailable; the block is not verified.
The original bridge at `bdac7cf9` and repaired bridge at `f58fde97` are separate proved deliverables.
Root gates pass for the repaired bridge; that does not prove the caller block.
Definition, data-lemma, and bridge verification do not establish native block closure.
No alloc block was inspected or run for this report.

## 7. Methods that proved out

- Trace the real goal before changing a rule. Trace evidence identified launch, encoding, and instruction-map defects.
- Register predictions before experiments. Compare OFF/ON sources with nine Auto controls; use authorized medians near the limit.
- Count all per-function text. Preserve counting-scope changes instead of describing them as newly written proof text.
- Correct contracts before the first valid run. Preserve earlier source packets and record the correction explicitly.
- Verify exact statements and compiled assumptions. An interactive-empty state or a successful launcher does not establish a theorem.
- Keep a spent hold-out immutable. Label every later comparison as training.

The accepted contract conventions remain distinct from tactic improvements.
A fixture result does not establish native applicability.
Compiler CPU, request wall time, admission time, and peak memory measure different things.

## 8. Open questions and limits

1. Which native search step prevents the measured region rule from reproducing its session result?
2. Which return decode, alignment, and route steps require a generic rule at the real native goal?
3. Can encoding normalization preserve branch hypotheses and Auto behavior while closing new native shapes?
4. Can whole-array literal-offset work replace the dominant spatial hand text without changing the ownership boundary?
5. What prevents the keyed fold facts from restoring the native back-edge invariant?
6. Which call-proof operation prevents the caller from returning within its measured bound?

The new study owns these questions; this report starts no repair or new run.
Orch reviews the report and owns integration and the completion tag.

## Checkpoint sources

The source table binds immutable checkpoints and checked snapshot files.
C’s snapshot passed focused checks; its publication gate was separate and pending when this report assembled.
The report does not claim that snapshot was already integrated.
The original report draft remains historical.
One later issue comment will amend only the pending A2 result after its complete table exists.
The completion tag follows that amendment and Orch’s review; this publication creates no tag.

| Source | Exact path | SHA-256 |
|---|---|---|
| Phase 1 tables | `build/stock-zisk/automation-validation/phase1-closing/TABLES.md` | `080405133594f91ff5615aa6b00f16f3227fdcac5da379da385d077fd583193a` |
| Phase 1 checkpoint | `build/stock-zisk/automation-validation/phase1-closing/CHECKPOINT.json` | `8773104dd73d86de95522eecf0ad879d955c7b5d1352f4faf22e0a975620ca72` |
| decodeItem recount | `build/stock-zisk/automation-validation/r1-r3-root-recount/CHECKPOINT.json` | `1a8fae8e17c85cb12c2601d36886105f7abb22536817d3e410e6cc95682f444f` |
| Free hold-out | `build/stock-zisk/automation-validation/free-first-result/RESULT-REPORT.json` | `08f1f79f50625c7e252707fef3fce24e79982ca672e294d107842bcdf9f4ae43` |
| Training 2 | `build/stock-zisk/automation-validation/free-training-2/REPORT.json` | `013de5b4ccab3d119bc64af178b1d919205eb6f26ef9051c631e9a8f4b5233b7` |
| Training 3 validation | `build/stock-zisk/automation-validation/free-training-3-uncapped/REPORT.json` | `494e2a303fb095948e5c9d379f5fbcfc3b18f92c84622de86fa8a0c88de76f1f` |
| Training 4 | `build/stock-zisk/automation-validation/free-training-4/REPORT.json` | `a2e8c2f6161d3c1eb9860da9dde8ceb0939b177b051e84d74cb9659d64389d8b` |
| Free text | `ZesuSsz/Evidence/free_function_text.json` | `f4ec959c74534aaa0779aa3b872a9f7ef71e19121599607b9e92ac4afe10a61a` |
| nextUint64 text | `ZesuSsz/Evidence/nextUint64_function_text.json` | `d8e8223ec0f3819ffe9c3938c34d6ade82d7099c066b728b5d3cca2e959de6b3` |
| Caller measurement | `/home/cody/zesislar/.worktrees/worker2-p0-native-trace-6f4d/_build/nextuint64-caller-cpu-result924/MEASUREMENT.json` | `142699253e7a80f05354438c91f98bcd0e92ae06105e44580e1df86b32863fc6` |
| Caller seal | `/home/cody/zesislar/.worktrees/worker2-p0-native-trace-6f4d/_build/nextuint64-caller-cpu-result924/REPORT.json` | `9ff6b876d21e7ae44aa77b74259da0786682bef732fbc5b4269bf53b7adfa248` |
| 62cc stop | `/home/cody/zesislar/.worktrees/worker2-p0-native-trace-6f4d/_build/nextuint64-nine-own-map-stop1018/REPORT.json` | `f5c1ec3814a967f4535908fa0d057e58539f96e2baa6859ba727f7443bef6e20` |
| 62d8 result | `/home/cody/zesislar/.worktrees/worker2-p0-native-trace-6f4d/_build/nextuint64-nine-own-map-continuation1022/results/0x800d62d8/RESULT.json` | `a979f736115f0262e9464b152c8025df25295fb545dd9528706b74ec61297fc0` |
| 62b8 evidence | `/home/cody/zesislar/.worktrees/worker2-c-nextuint64-nine-own-map/_build/nextuint64-nine-own-map-first1010/native/block_0x800d62b8/evidence.json` | `105bff9f027dda90f5baf7adc51f3874506a7f00f391c4d1e04ba45376fecf3c` |
| 62c0 evidence | `/home/cody/zesislar/.worktrees/worker2-c-nextuint64-nine-own-map/_build/nextuint64-nine-own-map-first1010/native/block_0x800d62c0/evidence.json` | `388510ea0506675adf9d8fc28e02105e97145013dc131757716c7ad64c69ebeb` |
| C review snapshot | `/home/cody/zesislar/.worktrees/spec-c-part-a-closing/_build/part-a-closing002/REVIEW-SNAPSHOT.json` | `98d2ea5f8455dc8bd4cae4260a6942ca48afc0cdfdb16aaa2eee46a14a7fcf04` |
| C CLOSING.json | `/home/cody/zesislar/.worktrees/spec-c-part-a-closing/_build/part-a-closing002/sources/build/stock-zisk/automation-validation/phase2-closing/CLOSING.json` | `9ed6e98bdcad1f46e7d1849c64f877a6a448e3a061efc88466b66d9368aa1f80` |
| C TABLES.md | `/home/cody/zesislar/.worktrees/spec-c-part-a-closing/_build/part-a-closing002/sources/build/stock-zisk/automation-validation/phase2-closing/TABLES.md` | `7eabcc966d8159d2f1d57dd377bbdd01f6d9128df9da7af7b92d398e4025391a` |
| C MATRIX.json | `/home/cody/zesislar/.worktrees/spec-c-part-a-closing/_build/part-a-closing002/sources/build/stock-zisk/automation-validation/pattern-matrix/MATRIX.json` | `aace03bffe83a45ce659e1a87c4032f20241addbb0884435ee4022cf3d5d69d3` |
| C README.md | `/home/cody/zesislar/.worktrees/spec-c-part-a-closing/_build/part-a-closing002/sources/build/stock-zisk/automation-validation/pattern-matrix/README.md` | `4f33cdcc255064ea657563b56ed1e209a08059691f6fccf4aa9a24a85b1d84d8` |
