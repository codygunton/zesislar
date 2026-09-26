# TF3 harness repair

The original B2 record stays unchanged.
The corrected record preserves both goals before shelving.
The summary selects the Prop goal after shelving.

| Record | Seconds | Outcome | Class | Goals |
| --- | ---: | --- | --- | --- |
| Original B2 | 5.9 | stalled | unknown | First goal only: `spec` |
| Corrected capture | 5.2 | stalled | C1 | `spec`; full `spec_trace` residual |

The original record is `../../b2-current-root/7dfa8d5a0d6f/write_success_exact_tail_fields_third_segment.jsonl`.
The corrected record is `tf3-after.json`.
Its `goals` array contains both complete conclusions.
Its `raw_goals` field contains the complete printed goals.

The call is at 0x159b8.
The callee is Encoder.optionalU64 at 0x15bc8.
The return is at 0x159bc.
The contract is `encoderOptionalEntryBoundary`, which names `zesuEncoderOptionalU64ExactCallSpec`.
The unresolved spec tail is `?Goal`.
No contract, proof, rule, trace, baseline record, or benchmark collector changed.

The capture uses the final zero-goal-safe `all:` RAW markers.
The focused tests check zero-goal output and repeated markers for two goals.
