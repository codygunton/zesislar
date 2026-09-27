# T6 tail fields 1 diagnostic

Candidate: `5b19de9408b1bbad9b44a11e5d9c9046656467ac` (unchanged).
Baseline artifacts: `ed945cd357ac` immutable arm.
Statement source: `builder-seg-tf1:ZesuSsz/Evidence/det/wp5/drafts/WriteSuccessExactTailFieldsFirstSegmentDraft.v`.
The diagnostic preserves the statement and adds the opt-in T6 switch.
The guarded scratch file inlines the candidate rule, switch, and v2 dispatch.
The scratch file imports support facts explicitly.
No support fact becomes a default import.

The direct attempt consumes the first bytes call and opens its return bundle.
It stops at the load specification for `0x158f0` (`88304`).
The goal needs a word at `bv_unsigned sp + 936`.
The context contains slots `sp+920` and `sp+928`, but no slot `sp+936`.
The complete context and residual are in `TailFieldsFirstT6Residual.txt`.

Timing: `zesu_block` 12.788 s; scratch 14.288 s; peak RSS 1,516,820 KiB.
The diagnostic ends with `Abort`; no segment theorem closed.
Hand proof lines added: zero.

## Entry resource gap

`Interfaces.v:289` defines `writeSuccessExactTailFieldsEntryBoundary`.
Its alias at line 291 fixes offsets 920 and 928.
`WriteSuccessExactSuffixBytesPayloadSpec.v:28` defines the underlying entry.
Its memory frame is `exactSuffixBytesPayloadFrame`, defined at line 10.
Lines 15 and 16 own only the two selected stack words and abstract `P`.
The frozen segment instantiates `P` with `hashBase ↦ₘ∗ hashBytes ∗ P`.
It does not require the eight descriptor words at `sp+936..sp+992`.
It does not require the later payload buffers.

Resource counterexample, without a machine proof: choose `sp=0x10000`,
`size=0`, `bytes=[]`, `hashBytes=[]`, `data=0`, `hashBase=0`, and `P=True`.
The numerical entry bounds permit this stack pointer.
The owned stack words lie at `sp+920` and `sp+928`.
The empty arrays supply no ownership at `sp+936`.
This example shows missing ownership, not a proved machine execution counterexample.

No boundary, candidate source, plan, or generated segment changed.
