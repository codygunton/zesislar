# Interior byte slices

The generic rule lends an interior slice from an owned byte array.
The rule retains a continuation that restores the original array.
The return step consumes that continuation after the callee returns the same bytes.
The synthetic tests cover a 32-byte slice at offset 152 in a 592-byte array.
The trace matcher accepts a snapshot prefix against the same plain event prefix.
The inclusion proof retains snapshot predicates when both prefixes constrain snapshots.
The slice rule selects the matching trace tail before it creates the call witness.

These six native proofs use the unchanged `headers_open` entry records.
Each proof uses the exact `writeOutputContract` and `zesu_block`.
All six proofs close with `Qed` and have no assumptions.
Rocq compiled the complete `0x14e28` proof and both regression files.
See `results.json` for timing and memory.
