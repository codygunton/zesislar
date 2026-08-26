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

The ELF hash binds machine work to one binary.
The snapshot manifest binds reference work to one EVM-Sail extraction.
The trace generator binds each entry smoke test to one instruction opcode.

Evidence files do not occur in any compliance target.
They only help reviewers inspect contract boundaries.
