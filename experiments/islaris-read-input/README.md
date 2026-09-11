# Islaris `read_input` experiment

This experiment covers the eight reachable instructions from `0x10140` through `0x1015c`.
The twelve later instructions in the symbol range are unreachable alignment padding.

Run `make read-input-traces` to regenerate the traces.
Run `make proof` to check `ZesuSsz/Experiments/ReadInput.v`.

The proof stores the fixed input-buffer address in the caller's buffer slot.
It loads the input size from the I/O context and stores that size in the caller's size slot.
It preserves the input bytes, the saved frame word, and all framed registers.
Control returns to `0x14ccc` after eight instructions.

The focused configuration covers the production input, context, and stack addresses.
It also fixes `mtvec` to direct mode for Sail's possible memory traps.
