# Trust boundary

The final proof will use Rocq to check all theorem terms.
The committed EVM-Sail decoder remains inside that checked statement.

Coq 8 cannot compile the generated decoder recursion in practical time.
The current statement therefore accepts its decoder action through `DecoderModel`.
A later Rocq 9 build must bind that field to the committed `decode_stateless_input` action.

The setup also trusts external generation tools.
The pinned Sail compiler generates the EVM decoder snapshot.
Isla executes the Sail RISC-V model symbolically.
Z3 removes infeasible paths.
Islaris translates the remaining traces to Rocq.
Nix and Zig build the pinned endpoint ELF.
Nix also exposes the pinned Zesu source and generates the entry instruction dump.

The ELF hash binds machine work to one binary.
The snapshot manifest binds reference work to one EVM-Sail extraction.
The trace generator binds each entry smoke test to one instruction opcode.

Evidence files do not occur in any compliance target.
They only help reviewers inspect contract boundaries.

The generated Level 1 Rocq map is not dynamic evidence.
The contracts use its ELF-derived PC regions and exit PCs.
Nix regenerates this map from the pinned CFG and rejects a changed snapshot.

The dynamic evidence build clears the QEMU guest environment.
It requires two independent runs to produce byte-identical traces and reports.

The contract evidence framework checks only clauses visible in the QEMU trace.
Current checkers cover `zkvm_exit` and `writeFailure`.
It does not convert successful evidence into a theorem premise.
The report names each contract clause that the trace cannot measure.
