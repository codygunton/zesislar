# Islaris `zkvm_exit` experiment

This experiment runs Islaris on the three contract steps at `0x101c4` through `0x101cc`.
The terminal self-loop at `0x101d0` is the postcondition PC, not a contract step.

Run `make zkvm-exit-traces` to regenerate the traces.
Run `make proof` to check the Islaris and Level 1 theorems in
`ZesuSsz/Experiments/ZkvmExit.v`.

The first store trace failed during Isla generation.
The project configuration described RAM as `0x80000000` through `0x83ffffff`.
The production I/O context is at `0x2401a0b8`, outside that range.

The focused `riscv64_zesu_exit.toml` configuration uses RAM from `0x0` through `0x3fffffff`.
The main project configuration remains unchanged.
It also constrains `x5` to the I/O context at the store instruction.
This makes the production exit-code store a valid physical access.

The theorem proves the following focused instruction behavior:

- `auipc` and `addi` compute `0x2401a0b8` in `x5`.
- `sd` writes the input `x10` value to `0x2401a0d0`.
- Control reaches the terminal PC at `0x101d0`.

The terminal `instr_pre` resources state the final register and memory values.
`zkvmExitTermination` certifies the four-PC path and its three-instruction bound.
`level1ZkvmExit` combines both proofs into the native Level 1 field.
