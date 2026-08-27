# Islaris `zkvm_exit` experiment

This experiment runs Islaris on the three contract steps at `0x101c4` through `0x101cc`.
The terminal self-loop at `0x101d0` is the postcondition PC, not a contract step.

Run `make zkvm-exit-traces` to regenerate the traces.
Run `opam exec --switch=$HOME/islaris -- dune build --root . ZesuSsz/Experiments/ZkvmExitIslaris.vo` to check the theorem.

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

The theorem does not prove the Level 1 `zkvmExitContract`.
It does not connect the memory write to the endpoint `exitCode` field.

`zkvm_exit_islaris_contract` lifts this result to `ZkvmExitArgs` and
`IslarisContractSpec`.
Its entry predicate requires a 64-bit exit code and owns the affected machine resources.
Its exit predicate owns the updated exit-code word at the terminal PC.

The pure `ContractImplements` theorem still needs a concrete endpoint state and step relation.
`Level1MachineModel` leaves both items abstract, so no theorem can connect them to these resources yet.

`ZkvmExitOperational.v` supplies a first concrete model from Islaris `seq_local_state`
and `seq_global_state` values.
It defines one contract step as one complete generated instruction trace.
The three step lemmas prove 10, 12, and 31 internal `seq_step` events.
`level1ZkvmExitCanonical` proves the bounded Level 1 field with a bound of three instructions.

This first operational model fixes unrelated registers to canonical values.
The production bridge must generalize those registers while preserving the same three trace proofs.
