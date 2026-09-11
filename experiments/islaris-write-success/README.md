# `writeSuccess` Islaris proof

The profile selects proof regions by function name from the pinned CFG.
The generator derives every `writeSuccess` block from that CFG.
The dump generator adds only the local constraints for decoded-memory loads.
The Isla config supplies the machine-wide stack constraints.

Run `make write-success-traces` to generate the dump and untracked traces.
