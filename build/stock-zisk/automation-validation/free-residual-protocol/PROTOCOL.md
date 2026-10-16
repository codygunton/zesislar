# Free residual classification protocol

Classify only the first captured residual after the coordinator releases its bundle.
This page uses existing decodeItem rule-off evidence.
It reports no free observation.

## Input and record

1. Record the frozen SHA, block, arm, command, state, and exact capture path/hash.
2. Copy the goal, context, evar assignments, and available goal-group counts.
3. Classify each captured target by its actual type and surrounding obligation.
4. Keep all matching classes when the evidence does not select one class.
5. Record missing fields as unknown. Send the classification without changing the proof.

Keep foreground, focus stack, shelf, and given-up groups separate.
Zero foreground goals do not establish completion.
A launcher exit does not establish proof success.
An import, transport, or resource failure without a residual receives no semantic class.
Do not open a new session, unfold predicates, or run tactics for this protocol.

## Classes

| Class | Identification from the capture | Historical example and frozen mapping |
|---|---|---|
| Z-binder evar | The target requests an unresolved Z witness. The capture must show its binder/evar identity. A Z-valued equality alone does not qualify. | 6a08/6aa8 [O]. R1 introduction and masks are active. A missing source fact remains possible. |
| Pure-conjunction committed witness | The target is a pure conjunction. Recorded witness assignments show a committed successor value that the required facts do not support. | 6a38/6ad8 [O]. ConjunctMatch is active. Pure arithmetic alone does not establish this class. FinishFacts remains inactive. |
| mem_mapsto_kind | The exposed target contains the actual mem_mapsto_kind resource-selection obligation. Preserve width, address, base, and array terms. | 698c/69b0/6a40/6a78/6b08 [O]. MemoryAccess remains inactive. Map this to the memory-access hand pattern. |
| Store-index existential | The target requests a nat store index or its shelved address equation. The captured operation must identify a store. | 6ae0: SHELVED_SIDECOND (?Goal:nat) = outputPointer+16-outputPointer [O]. MemoryAccess remains inactive. Preserve extent and no-wrap obligations. |
| Fold-accumulator step | The equality compares the shifted/combined accumulator with a prefix fold at the successor index. Preserve the byte array and widths. | 6a24/6ac4 [O]. Map this to the loop hand pattern. A registered data step does not establish an active loop consumer. |
| Trace-lookup existential | The target requests an isla_trace witness for selectedCodeLookup or an explicitly captured instruction-lookup relation. An unrelated existential does not qualify. | 698c rule-off suffix: masked saved-return target [T]. ReturnRoute remains inactive. Associate a return only when the captured target/context establishes it. |
| Other | The capture does not establish a preceding class. Record the exact head and the missing discriminator. | The bv8 input-head witness at 6960 and historical Boolean-path conjunctions at 697c/69e8 [O] need separate detail. Do not relabel them as Z witnesses. |

## Ambiguity and limits

Preserve every active target in capture order.
Do not select the most familiar class or replace the first residual with a later goal.
A conjunction without recorded witness assignments stays ambiguous or other.
A nat witness without an identified store stays ambiguous or other.
A missing/truncated context prevents a context-based classification.
Report multiple candidates and the exact missing discriminator.

Keep branch polarity, accepting guards, current/successor indices, and implicit widths unchanged.
Class names describe obligation shapes, not proven causes or solver applicability.
Existing stock rules can share these shapes.
An active frozen rule does not prove that it fired.
An inactive named rule does not exclude all existing automation for that shape.
Do not assign an evar, add a premise, or infer closure from this table.

## Frozen boundary and evidence

Root e8131be295b89a1821b3ba760f39e7aad1e8647d is cp-av-rules-frozen.
EntryIntro, both MaskNormalizer forms, and ConjunctMatch are active [F].
ReturnRoute, FinishFacts, and MemoryAccess are inactive [F].
F20/F30 record failed R2/R1d experiments. F24 records R1c median acceptance.
These findings do not change the classification test.

[O]: [decodeItem rule-off table](https://github.com/codygunton/zesislar/issues/13#issuecomment-6175892853), Root 680b56ad, fifteen full-block attempts.
[T]: Report 578, Root b7359b55, filtered rule_off suffix captures. The 698c target is a helper, not either public flat alternative.
The 6b08 suffix fails during common setup and supplies no return-route verdict.
The original fifteen-block table has no first trace-lookup residual.
Do not merge that full-block scope with the retained suffix scope.
[F]: The bound freeze checkpoint, Approved.v, and switch inventory.
CHECKPOINT.json binds the exact snapshots and filtered records.
No new proof, native run, alloc inspection, or free-result inspection occurred.
