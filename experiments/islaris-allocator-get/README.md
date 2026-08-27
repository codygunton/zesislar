# Islaris `allocatorGet` experiment

This experiment covers the eight instructions from `0x14ccc` through `0x14ce8`.
The body reads two input words from the stack and writes the allocator pair to the next two slots.

Run `make allocator-get-traces` to regenerate the traces.
Run `make proof` to check the Islaris and Level 1 theorems in
`ZesuSsz/Experiments/AllocatorGet.v`.

The focused configuration places RAM from `0x20000000` through `0x3fffffff`.
The dump constrains each stack access to this range and requires eight-byte stack alignment.
The configuration fixes `mtvec` mode to direct mode.
This prevents Sail from exploring its invalid reserved trap-vector mode.
The configuration keeps the production RV64IM extension set.

The theorem proves the following behavior:

- The body loads the input words into `x12` and `x13`.
- The body computes the allocator state address in `x10`.
- The body computes the allocator vtable address in `x11`.
- The body writes both allocator addresses to the output stack slots.
- Control reaches `0x14cec`.

The terminal `instr_pre` resources state the final register and memory values.
`allocatorGetTermination` certifies the nine-PC path and its eight-instruction bound.
`level1AllocatorGet` combines both proofs into the native Level 1 field.
