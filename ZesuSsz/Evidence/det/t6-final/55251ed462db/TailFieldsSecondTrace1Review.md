# Matched TF2 return-site validation

Candidate: `5b19de94` (unchanged).
Dependencies: immutable `ed945cd357ac` arm.
State source: `determinism/_build/agents/det/det/boundary/write_success_exact_tail_fields_second_segment_trace1.v`.
Inference record: `determinism/ZesuSsz/Evidence/det/trace_tail_fields.write_success_exact_tail_fields_second_segment.1.spec.json`.
The recorded entry declares the first Boolean output as 0.
Both diagnostics use the same inferred statement and explicit support imports.
They import `InterfacesCoverage` and `WriteSuccessExactPrefixStackFacts`, as the measured source did.
Only the candidate enables the immutable T6 rule and dispatch.
Neither diagnostic changes a public segment statement.

Control tactic: 15.257 s (15.118 user CPU, 0.052 system CPU).
Control scratch: 17.395 s; peak RSS 1,433,256 KiB.
The control stops at the recorded Boolean return wand:
`encoderBooleanClosedReturn 0 (writeSuccessFrameSp witness) (Z_to_bv 64 (88476 + 4)) tail -∗ zesu_ld_spec 88480 "x8" "x2" 96`.

Candidate tactic: 77.057 s (76.393 user CPU, 0.255 system CPU).
Candidate scratch: 79.687 s; peak RSS 2,098,044 KiB.
T6 opens the Boolean return bundle.
The search answers the load at `0x159a0` and the following load at `0x159a4`.
It reaches the integer call at `0x159ac`.
The next goal needs nine uninitialized bytes at `sp-9` and the integer-output trace for post word 9.
The goal also contains the integer return continuation at `0x159b0`.
The existing other-branch Boolean trace inclusion remains a second goal in both checks.

The complete goals and contexts are in `TailFieldsSecondTrace1ControlResidual.txt` and `TailFieldsSecondTrace1CandidateResidual.txt`.
Both diagnostics end with `Abort`; no segment theorem closes.
Added hand proof lines: zero.
No gate, arm, new rule, support default import, boundary change, or segment merge occurred.

## Named-site evidence

TF1 opens the bytes return bundle and stops at missing `sp+936` ownership.
This matched TF2 check opens the Boolean return bundle and reaches the integer call.
The two diagnostics establish progress at both named T6 sites.
Neither diagnostic establishes segment closure.
Candidate `5b19de9408b1bbad9b44a11e5d9c9046656467ac` remains the queued arm.
No further proof steps, rule changes, or statement changes follow this measurement.
