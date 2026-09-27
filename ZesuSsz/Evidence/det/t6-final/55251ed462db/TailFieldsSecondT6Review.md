# T6 tail fields 2 diagnostic

Candidate: `5b19de94` (unchanged).
Artifacts: immutable `ed945cd357ac` arm.
Statement source: `builder-seg-tf2:ZesuSsz/Proofs/WriteSuccess/WriteSuccessExactTailFieldsSecondSegment.v`.
The diagnostic preserves this statement and enables T6 explicitly.
The scratch file inlines the immutable candidate rule, switch, and v2 dispatch.
It adds no support imports to the frozen draft.

The direct attempt takes 3.795 s.
The guarded scratch check takes 5.278 s and 1,341,656 KiB peak RSS.
Two goals remain, one for each branch at the first Boolean call.
Both goals need a trace-tail witness and its inclusion against
`writeSuccessExactTailFirstBranchEvents witness`.
Neither goal reaches a return wand.
Therefore this direct attempt does not test bundle opening in the actual segment.

The complete goals and contexts are in `TailFieldsSecondT6Residual.txt`.
Hand proof lines added: zero.
The diagnostic ends with `Abort`; no segment theorem closed.
No boundary, contract, candidate source, or default import changed.
