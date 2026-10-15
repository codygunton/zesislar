# Phase 1 closing tables

This note updates `phase1-closing-002` from the owner metrics and issue13.
It adds no proof, native run, or timing measurement.
The metrics snapshot is authoritative only for the exact values it records.
Unknown measurements remain unknown.

## Rule outcomes

| Item | Prediction | Recorded result | Closing status and evidence |
|---|---|---|---|
| R1a | Introduce four entries. preserve nine Auto blocks. | The first consumer changes no target. The goal-side repair reaches mask facts and committed successor witnesses. | Initial failure. repaired frontier only. [#13:6176908918](https://github.com/codygunton/zesislar/issues/13#issuecomment-6176908918) [#13:6177861662](https://github.com/codygunton/zesislar/issues/13#issuecomment-6177861662) |
| R1b | Close 6a08/6aa8 after integer mask normalization. | The integer inequality passes. The bitvector equality remains. Nine Auto controls pass. | Closure prediction fails. frontier advances. [#13:6178898344](https://github.com/codygunton/zesislar/issues/13#issuecomment-6178898344) |
| R1b' | Close 6a08/6aa8 with the bitvector mask reduction. | Both blocks close with `zesu_block` alone. Canonical-domain applicability requires the later C1BDomain repair. | Two production closures. empty assumptions. [#13:6179571469](https://github.com/codygunton/zesislar/issues/13#issuecomment-6179571469) [#13:6186102018](https://github.com/codygunton/zesislar/issues/13#issuecomment-6186102018) |
| R1c | Select the correct successor witnesses without unacceptable Auto cost. | Early candidates misassign witnesses or cost too much. The final cached-head candidate preserves witnesses but leaves pure obligations. | Accepted under the authorized median criterion. No 6a38/6ad8 closure. F24. [#13:6185428394](https://github.com/codygunton/zesislar/issues/13#issuecomment-6185428394) |
| R1d | Close 6a38/6ad8 under registered bounds. preserve Auto results and cost. | Both candidates leave targets open. Final Auto failures:69a4+20.881585109%,6a14+17.758603137%,6ab4+22.920209807%. | Closed failed after two candidates. FinishFacts stays excluded. F26,F30. [#13:6186887100](https://github.com/codygunton/zesislar/issues/13#issuecomment-6186887100) |
| R2 | Resolve output stores and reach the return route. preserve Auto cost. | Three candidates leave 6b08 at the store to outputPointer+24. Final Auto costs rise 48.685%–111.362%. | Closed failed. MemoryAccess stays inactive. Store work remains manual. F20. [#13:6184005012](https://github.com/codygunton/zesislar/issues/13#issuecomment-6184005012) |
| R3 | Close six retained return suffixes. preserve nine Auto controls. | Five completed ON suffixes remain open at the masked-target instruction-trace existential. Both 6b08 arms fail in common setup. | First comparison fails. Diagnosis/repair remains pending. Fixtures do not establish native success. F29,F32,F34. [#13:6186547372](https://github.com/codygunton/zesislar/issues/13#issuecomment-6186547372) |
| E3 join split | Keep rules-off behavior. close 697c/69e8 with the intended rule combination. | The flat Literal/ShortString contract boundary is integrated. These sources provide no final paired closure result for both predecessors. | Contract change recorded. Native paired outcome unknown. no rule credit. [#13:6182273054](https://github.com/codygunton/zesislar/issues/13#issuecomment-6182273054) |
| R4 / loop step | Reduce the two loop proofs through a keyed preservation step. | The loop facts and back-edge audits exist. The allowed sources provide no completed native ON/OFF comparison. | No measured native closure claim. [#13:6170766793](https://github.com/codygunton/zesislar/issues/13#issuecomment-6170766793) |

R1c acceptance changes the decision under the authorized criterion.
It does not erase the original failed single-sample comparison.
The current production switch state remains distinct from comparison acceptance.
ReturnRoute, ConjunctMatch, and MemoryAccess remain inactive at `cp-av-r1-r3`.

## Timing and measurement decisions

| Scope | OFF CPU seconds | ON CPU seconds | Decision |
|---|---:|---:|---|
| R1c 6974, three-sample medians, same tip a8787469 | 596.866219 | 405.724374 | -32.024236%. accepted |
| R1c 6974, earlier frozen-baseline sample | 463.684895 baseline | 511.737565 | Exceeds510.0533845 threshold. preserve superseded failure |
| Final R1d 6a38 | 48.567473 | 58.675421 | Both proofs remain open |
| Final R1d 6ad8 | 72.576667 | 85.030575 | Both proofs remain open |

[#13:6185428394](https://github.com/codygunton/zesislar/issues/13#issuecomment-6185428394) [#13:6186740154](https://github.com/codygunton/zesislar/issues/13#issuecomment-6186740154)

The R1c median limit is 656.5528409 CPU seconds.
The near-limit policy uses medians for initial changes from +8% through +12%.
The original frozen comparisons remain separate.
These samples measure compiler CPU, not request wall time or an isolated tactic.
The recorded probe policy uses 64 GiB, unlimited CPU, no wall deadline, and zero swap.
Different imported source scopes limit isolated tactic attribution.

| Production block | Median CPU seconds | Peak GiB | Samples | Manual hand lines |
|---|---:|---:|---:|---:|
|6a08|62.944|1.599|3|0|
|6aa8|54.638|1.601|3|0|

The production rows come from F25 and the owner block metrics.
Both blocks close with `zesu_block` alone at Root 6e086319.
The early 70.392/80.437-second records do not specify their clock type in the inherited source.
Do not label those early values as CPU measurements.

## Fifteen-block baseline and current evidence

The baseline counts nonblank physical lines strictly between `Proof` and `Qed` at c7c59161.
It includes automation lines.
The zero values below count manual lines after native promotion.
These are different measures.
A question mark means no measured rule-on manual count exists in the cited sources.
It does not mean zero.

| Block | Baseline body lines | Rule-off CPU seconds | Rule-off peak GiB | Manual after | Recorded native boundary |
|---|---:|---:|---:|---:|---|
|6960|66|29.337|1.452|?|No new native closure recorded|
|697c|63|1401.816|3.336|?|R2 join residual. final E3 pair unknown|
|698c|78|174.161|2.769|?|R3 helper suffix open. flat alternatives not tested|
|69b0|90|553.931|4.232|?|R3 suffix open|
|69e8|73|1490.116|3.619|?|Final E3 paired outcome unknown|
|6a08|49|17.791|1.183|0|Production closure|
|6a24|158|1100.191|2.828|?|No completed R4 comparison|
|6a38|29|28.326|1.161|?|Correct witnesses. R1d pure conjunction remains|
|6a40|60|553.082|4.308|?|R3 suffix open|
|6a78|89|739.918|4.646|?|R3 suffix open|
|6aa8|24|17.632|1.187|0|Production closure|
|6ac4|169|995.381|2.779|?|No completed R4 comparison|
|6ad8|66|59.840|1.413|?|Correct witnesses. R1d pure conjunction remains|
|6ae0|71|775.287|6.194|?|R3 suffix open|
|6b08|21|627.807|4.237|?|R2 store residual. R3 common setup fails|
|Total|1106|Not aggregated|Not aggregated|2 known zeros.13 unknown|13 hand modules remain|

[#13:6175892853](https://github.com/codygunton/zesislar/issues/13#issuecomment-6175892853) [#13:6185501863](https://github.com/codygunton/zesislar/issues/13#issuecomment-6185501863)

The two promoted baseline bodies total 73 lines.
The thirteen retained baseline bodies total 1033 lines.
The separate physical audit counts 1059 lines because it includes `Proof`, `Qed`, and structural lines.
Its deterministic counting rule governs its totals.
Do not equate 1059 with a rule-on manual-line measurement.
The initial study's 1153 aggregate and 65 shared lines use another boundary.

## Remaining hand lines by obligation kind

Scope: thirteen hand modules at exact Root 6e08631942efd13d229ff7a46a01ab6a3c42384a.
Each physical line receives one primary kind.
The priority order is machine, trace/return, encoding/image, branch/handoff, spatial, pure finisher.
A structural line inherits the next direct line in its proof.
At the proof end, it inherits the previous direct line.
The separate mixed record preserves all detected kinds.

| Block | Machine | Trace/return | Encoding/image | Branch/handoff | Spatial | Pure finisher | Total |
|---|---:|---:|---:|---:|---:|---:|---:|
|6960|25|3|0|11|17|12|68|
|697c|9|5|11|4|14|22|65|
|698c|5|19|11|1|38|6|80|
|69b0|9|20|1|0|55|7|92|
|69e8|16|12|5|5|18|19|75|
|6a24|55|2|0|46|42|15|160|
|6a38|3|2|0|9|4|13|31|
|6a40|8|18|1|2|26|7|62|
|6a78|9|20|1|0|55|6|91|
|6ac4|57|2|0|44|47|21|171|
|6ad8|10|2|0|15|16|25|68|
|6ae0|8|18|1|0|36|10|73|
|6b08|8|5|0|0|10|0|23|
|Total|222|128|31|137|378|163|1059|

F31 records 444 mixed lines and 59 structural lines.
These counts measure physical text, not time, instructions, or solver success.
The registered-fact audit identifies 52 whole-line and 26 partial-line opportunities.
All 78 opportunities remain conditional.
It proves no native deletion.
The standalone R1d query routes are absent from that exact audit Root.
The flat 698c entries also differ from the retained Hand helper boundary.

## Spatial subtypes

The input set contains only the 378 primary spatial lines from the preceding audit.
The audit does not reclassify other primary kinds.

| Block | Output literal-offset handling | Input take/drop | Frame/stack | Other | Total |
|---|---:|---:|---:|---:|---:|
|6960|0|0|10|7|17|
|697c|0|0|0|14|14|
|698c|17|0|13|8|38|
|69b0|36|0|13|6|55|
|69e8|0|0|0|18|18|
|6a24|0|0|0|42|42|
|6a38|0|0|0|4|4|
|6a40|16|0|8|2|26|
|6a78|36|0|13|6|55|
|6ac4|0|0|0|47|47|
|6ad8|0|2|0|14|16|
|6ae0|20|0|9|7|36|
|6b08|5|0|1|4|10|
|Total|130|2|67|179|378|

Output handling means literal-offset selection, bounds, callbacks, and framing for whole arrays.
It does not mean physical array splits.
The two input sites normalize slice values.
They do not split input ownership.
Three lines match multiple spatial subtypes.
The upstream set includes 195 mixed lines and 14 structural lines.
No subtype count establishes that a generic store rule can discharge those lines.
The return-only trace denominator is 100 lines across six return blocks.
The full trace/return count is 128 across all thirteen modules.
The frame count covers seven modules.
Do not use 128/6 or 67/8 as source-derived rates.

## Per-function interface text

| Category | Baseline | Recorded integration scope | Change |
|---|---:|---:|---:|
|contracts|2438|2496|+58|
|introductions|3438|3688|+250|
|exit_meanings|2963|3114|+151|
|loop_steps|913|965|+52|
|registrations|154|326|+172|
|generator_json|3970|6299|+2329|
|Total|13876|16888|+3012|

This table preserves the frozen integration recount from the inherited draft and owner metrics.
It does not assert a fresh count of current main.
Generator JSON includes per-function design JSON and source-embedded constant tables.
The earlier 16901 conservative sum included 13 unscored test lines.
No retained old module receives deletion credit.
The candidate removal set contains 15 modules and 2998 lines, with zero removal credit.
Generic automation text is outside this per-function interface total.
Block proofs, composition, tests, and exports remain separate categories.

## Findings F30–F34

| Finding | Closing record | Limit |
|---|---|---|
|F30|Final R1d targets remain open. Three Auto CPU comparisons fail. FinishFacts is excluded.|Two candidates only. no native repeat follows.|
|F31|1059 lines:378 spatial,222 machine,163 pure,137 branch,128 trace,31 image.|Primary-kind priority.444 mixed lines remain separately recorded.|
|F32|Diagnostic 037 stops at the sequential PC before jalr.|It measures no masked-return refusal.|
|F33|378 spatial lines:130 output,2 input,67 frame,179 other.|Whole-array handling, not array splitting.|
|F34|Diagnostic 040 reaches the masked return. Alignment stays folded in layout. decoder terms retain N.to_nat8 and a frame-relative offset.|The hint still refuses after exposure. Completion/repair is pending.|

F30–F32 also appear in issue13 comment6187028684.
F33–F34 come from the current owner metrics. the retrieved comments do not contain a final repair outcome.
R3's first failure remains distinct from its later diagnostic and any future repaired comparison.
The 3a compositional theorem later passed Root gates at d77840e1.
That result does not prove R3 closure.
The free hold-out and nextUint64 native results remain unknown.
No new run follows from these tables.
