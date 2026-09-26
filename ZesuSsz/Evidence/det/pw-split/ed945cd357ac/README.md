# Post-withdrawals split preparation

Root: `ed945cd357ac`.
Split PC: `0x156fc`.
Status: a compiled conditional scaffold, not a proved physical split.
The prefix and suffix remain explicit Phase C obligations.
No whole-segment theorem is proved.

## Boundary

The prefix range is `[0x156e8, 0x156fc)`.
The suffix range is `[0x156fc, 0x15744)`.
The instruction at 0x156fc is the second Encoder.int JALR.
It has not executed at the handoff.
The preceding AUIPC at 0x156f8 fixes x1 to 0x156f8.
The first integer return contract fixes x5 to the IO-context address and x11 to 8.
The load at 0x156f4 fixes x10 to value word 14, at sp+1144.
The exact first payload is consumed.
`exactPostWithdrawalsFirstTail` retains the second exact payload and every later event.
The original arrays and caller frame remain intact.
The handoff exposes seven top-level conjuncts.

The composition keeps the frozen entry at 0x156e8 and the frozen suffix-hashes exit at 0x15744.
Its local exit frame is copied from the frozen `builder-seg-pw` draft.
No public contract, Interfaces predicate, Automation rule, trace, or binary changed.
The composition requires both native block implications explicitly.
The ordinary code and helper premises must discharge those implications in Phase C.
The legacy IntPair lemmas use Any payloads and cannot discharge these exact obligations.

## Verification

`rocq_health` passed with Coq 8.19.2+lsp and the local Islaris switch.
Two `rocq_start` attempts failed with `No node at point`, reason `crashed`.
The second attempt used a fresh session after private load-path initialization.
Root authorized bounded guarded scratch fallback.

The composition compiled in 1.773 seconds with 1,332,588 KiB peak RSS.
`Print Assumptions write_success_exact_post_withdrawals_from_split` printed `Closed under the global context`.
`rocq_verify` passed with method `shared_defs` and an empty assumptions list.
`rocq_compile_file` failed before proof compilation.
It selected the base directory and reported duplicate `IslaTraces.allocator_get` theories.
The paths were `generated/isla-traces/allocator_get/dune:3` and `generated/isla-traces/isla-traces/allocator_get/dune:3`.
The private artifacts were copied from the completed immutable arm.
The immutable arm was not changed.

## Residual

The prefix probe used only `zesu_block` and goal-printing commands.
It took 8.538 seconds with 1,559,236 KiB peak RSS.
The probe did not reach the handoff.
It stopped at the first load from sp+1136 with two arithmetic goals and one memory-lookup goal.
The sealed caller frame hides the value array.
`prefix-residual.txt` preserves the complete context and all three goals.
`PrefixProbe.v.txt` preserves the diagnostic probe as text.
It is not an executable proof source.
No hand-proof reconstruction or new rule was added.
The composition has two manual proof lines.
The final bounded prefix attempt has four manual proof lines.
It uses the existing Hwf stack facts and attempts the existing frame unfold lemmas.
It took 10.822 seconds with 1,386,016 KiB peak RSS.
The alignment goal closed.
The remaining goals are the RAM bound and the first memory lookup.
The attempted frame rewrite did not expose the sealed array.
`prefix-five-residual.txt` preserves the complete final context and both goals.
Proof development stopped after this attempt.

Root must queue check-fast and the cheap preview before this preparation can be committed.
The branch must remain unmerged.

## Composition hand-line record

The automation-only composition probe does not close.
`composition-residual.jsonl` stores its complete residual and context.
`CompositionProbe.v.txt` stores the exact diagnostic source.
The two manual composition lines remain necessary.
This probe changes no physical-prefix obligation.

## Root check-fast and artifact retry

Root check-fast passed with exit 0 in session 87042.
It took 646.673 seconds with 2,708,532 KiB peak task RSS.
The subsequent focused scratch preview found stale copied `Interfaces.vo` assumptions.
The mismatch concerns `IslaTraces.write_success_09.a14d34_spec`.
Root started the focused Dune target to refresh its dependencies.
The retry is session 15411.
Its log is root's `preview-pw-split-focused-dune.log`.
The focused Dune retry passed with exit 0.
It took 298.814 seconds with 4,103,896 KiB peak task RSS.
These measurements include the dependency refresh.
The physical prefix and suffix remain open.
No further proof development is authorized.
