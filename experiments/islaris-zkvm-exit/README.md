# Islaris `zkvm_exit` experiment

The native proof checks three instructions from `0x101c4` through `0x101cc`.
The terminal PC is `0x101d0`.

Run `make zkvm-exit-traces` to generate traces from the pinned binary.
The Evidence tooling generates the dump in `build/islaris-dumps/zkvm_exit.dump`.
All endpoints and main use `ZesuSsz/riscv64_zesu.toml`.
The RAM base is `0x20000000`.
The RAM size is `0x20000000`.
The profile constrains `x5` to the I/O address at the store.

The native theorem uses `zesu_block` and proves these effects:

- `auipc` and `addi` set `x5` to `0x2401a0b8`.
- `sd` writes `x10` to `0x2401a0d0`.
- Control reaches `0x101d0`.

Phase 5 proves termination separately with the verified executor.
