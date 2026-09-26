# T3 array priority

The source root is `ed945cd3`. The candidate is opt-in through `Switches.ArrayLoadPriority`.
The v2 dispatcher tries the guarded array selector before its ordinary search.
The v1 dispatcher does not change.

The selector reads the table's load parameters.
It selects the raw trace only after it finds an owned initialized array that covers all eight bytes.
It opens a sealed bundle through existing registered equivalences only when needed.
A failed guard restores the original lookup goal.
The selector uses no address or boundary predicate name.
It imports no support-fact module.

Both real fixtures explicitly import `InterfacesCoverage`.
The control stops at the bare-word load precondition at `0x156e8`.
The switched fixture passes that load and reaches the encoder call at `0x156f0`.
Its remaining goal includes the output-event trace inclusion and return resources at `0x156f4`.
The segment does not close.

The three selector tests are closed under the global context.
They check the inactive switch, an owned array, and a bare word.
The table retains the non-array case.

The checks use guarded scratch compilation with completed root-arm dependencies.
The `.v.txt` fixtures show the normal candidate import for reproduction after its focused build.
The development fixtures used `Load` for the new rule because its `.vo` did not yet exist.
MCP file-based start, check, and step_multi confirm the array selection and proof.
MCP compile_file and verify cannot resolve this workspace's project imports.
The logs record the accepted guarded scratch fallback.

Root must queue focused checks and check-fast before commit.
Root then queues the candidate arms.
The switch-alone arm must remain separate from the matched-support control and candidate.

## Exact split diagnostic

`PWPrefix156fc-five.v.txt` uses the exact boundary definitions from pushed `builder-pw-split` at `de275134`.
It adds only the T3 switch and explicit existing support imports.
The boundary does not change.
Five hand lines took 53.833 seconds with peak RSS 2,174,396 KiB.
The first array load executed.
Two goals remain: the first output-event inclusion and the return wand to the next load at `0x156f4`.
`prefix-five-residual.jsonl` and the log retain both goals.
The attempt stopped at five hand lines.
The physical prefix and full segment remain open.

`selector-initial-goals.jsonl` contains real MCP initial-goal captures for all three selector tests.
These records explain the tests' deliberate manual selection steps.

## T3 and exact T6 diagnostic

The combined diagnostic uses T6 tactic text from `5b19de94`.
Its SHA256 is `5efe6c82f6dac610909754fc4d55406c2cd1ce463668a6ac7c083c218ecb9a04`.
The split boundary remains exactly the `de275134` boundary.
The diagnostic removes the broad frame rewrite and extra arithmetic pass.
Three hand lines remain.
The guarded compile took 146.804 seconds with peak RSS 2,193,652 KiB.
The first load executes.
T6 opens the first return bundle.
Two goals remain: the first output-event inclusion and the bare-word load at `0x156f4`, from `sp + 1144`.
The second load already uses its table specification.
The current T3 selector only intercepts instruction lookup.
No physical prefix or full segment closes.
The attempt stops on this residual.
This diagnostic changes hand lines, so its time is not a matched timing comparison.
All exact sources and both goals remain in the adjacent files.

## Matched three-line control

The paired sources differ only in the T6 switch instance.
Both use the same boundary, tactic text, support imports, and three hand lines.
T3 alone took 87.964 seconds with peak RSS 2,099,508 KiB.
It leaves the output-event inclusion and the return-resource wand.
T3 with T6 took 146.804 seconds with peak RSS 2,193,652 KiB.
It leaves the same inclusion and the next bare-word load precondition.
T6 opens the return bundle but closes no physical prefix or segment.
`prefix-t3-t6-paired.jsonl` records the pair.
Both full residuals remain in the logs.
The diagnostic stops here.

The committed log copies remove trailing whitespace only.
The JSON residual records retain the complete raw goal text.
