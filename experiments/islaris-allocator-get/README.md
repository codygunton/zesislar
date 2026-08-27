# Islaris `allocatorGet` experiment

This experiment covers the eight instructions from `0x14ccc` through `0x14ce8`.
The body reads two input words from the stack and writes the allocator pair to the next two slots.

Run `make allocator-get-traces` to regenerate the traces.
Run `opam exec --switch=$HOME/islaris -- dune build --root . ZesuSsz/Experiments/AllocatorGetIslaris.vo` to check the theorem.

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

The theorem does not prove the full Level 1 `allocatorGetContract`.
It does not connect the stack words to the endpoint state model.
