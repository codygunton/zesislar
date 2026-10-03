# Stock zesu on ZisK

The ELF uses unchanged stock zesu sources and the pinned ZisK runtime.
The guest host uses the upstream build recipe with two explicit ABI adapters.
The adapters live under `tools/stock_zisk/`.

## Source pins

| Source | Commit | Role |
|---|---|---|
| https://github.com/Consensys/zesu | d8071c422f0faf2c52d85b401192fdffc31fd5ac | Stock RV64IM object |
| https://github.com/0xPolygonHermez/zisk | fbbc69bcd2ea9a78d1a438b4a897bc48ff0b00a3 | v1.2.0-alpha runtime and linker |
| https://github.com/Consensys/zesu-zkvm | be591e90ecbd94b0a3185809ba5ed74268558fa3 | Author's ZisK guest build recipe |

`build.py` checks each HEAD and rejects tracked source changes.
`build-recipe.json` records these checks, commands, and artifact hashes.
No fork commits enter the stock object or the runtime.

## Build method

Stock zesu supplies `zig build rv64im-object -Doptimize=ReleaseFast`.
The guest repository supplies `zisk/Makefile`, `zisk/build.zig`, and `zisk/src/zisk_host.zig`.
Neither source repository supplies a ZisK Docker target.
The build follows those author targets inside a pinned runtime environment.
The host compiler is Zig 0.16.0 at `/usr/bin/zig`.
The build uses eight jobs and separate local and global caches.

The runtime container uses `zisk-eth-act-standards:latest`.
Its image ID is `sha256:3c7565636c6516f21c630b4b7e803de59574e9381b50e2b4ae082b2b20751318`.
The container limits are eight CPUs and 6 GiB.
The build does not use that image's preinstalled runtime library or `/zisk` source tree.
The build installs the exact release under `/opt/stock-zisk`.

```sh
bash /stock-zisk/ziskup/ziskup --version 1.2.0-alpha --cpu --nokey \
  --system --prefix /opt/stock-zisk --yes
ZISK_DIR=/opt/stock-zisk /opt/stock-zisk/bin/cargo-zisk toolchain install
cd /stock-zisk
CARGO_BUILD_JOBS=8 CARGO_TARGET_DIR=/output/zisk-target \
  cargo +zisk build -p ziskos-staticlib \
  --target riscv64ima-zisk-zkvm-elf --release --locked \
  --config 'profile.release.lto="fat"'
```

The release bundle is `cargo_zisk_linux_amd64.tar.gz` from the v1.2.0-alpha GitHub release.
`cargo-zisk` reports `1.2.0-alpha [cpu] (fbbc69b)`.
Cargo reports `1.94.0-dev (85eff7c80 2026-01-15)`.
Rustc reports `1.94.0-dev`.
The runtime build preserves its Cargo.lock and committed lib-float binaries.

The final host command is the upstream Zig guest target.
The build stages that recipe without changing the source checkout.
The stage uses the exact `ziskbuild/zisk_linker_script.ld` as `zisk.ld`.
Its SHA256 is `a251fe2ea5cb24fb54e088bf9da5eedd484c83a164e2a19eb51bf3cc4e103b61`.

```sh
python3 tools/stock_zisk/build.py \
  --zesu /tmp/worker2-stock-zesu \
  --zisk /tmp/worker2-stock-zisk-toolchain \
  --guest /tmp/worker2-stock-zesu-zkvm \
  --runtime-library _build/agents/worker2-stock-zisk/zisk-target/riscv64ima-zisk-zkvm-elf/release/libziskos_staticlib.a \
  --build-dir _build/agents/worker2-stock-zisk --out build/stock-zisk --jobs 8
python3 tools/stock_zisk/inventory.py --help
```

## ABI adapters

Stock `src/zkvm/root.zig` exports a void `main` and calls `zkvm_exit`.
The current upstream guest host exports `zkvm_log` and `zkvm_abort`, but lacks `zkvm_exit`.
`exit.zig` supplies that symbol through ZisK exit syscall 93.
The adapter places the exit code in a0 and the syscall number in a7.

Stock `src/zkvm/alt_fl_alloc.zig` requires writable `ZKVM_HEAP_POS` and `ZKVM_HEAP_TOP` globals.
The exact ZisK linker script supplies `_heap_bottom` and `_heap_top`.
`heap.S` initializes the two writable words from those linker symbols.
The adapter preserves the script and does not alias the runtime's private bump heap.
The actual heap range starts at `0xa0d34530` and ends at `0xbfff0000`.

## Verification and inventory limits

Watched object, toolchain, runtime, and final-link builds returned exit 0.
Their elapsed times were 19, 21, 22, and 3 seconds.
The reproducible build command also completed and produced the recorded recipe.
Five focused inventory tests passed.
ELF checks found entry `0x80000000`, no undefined symbols, and correct heap initialization.
The ELF uses soft-float RISC-V with compressed instructions in the Rust runtime.
The stock Zig object targets RV64IM.
No execution test or proof establishes guest correctness here.

`inventory.json` covers all 64 requested functions.
DWARF supplies exact source declarations and inline ranges.
The inventory distinguishes symbols, inline instances, and absent emitted instances.
Instruction counts cover concrete bodies when symbols exist.
Otherwise, counts cover the recorded inline ranges.
Overlapping inline ranges must not be summed as unique binary size.
Calls include direct calls, unresolved register calls, and external function tail calls.
Loops are cyclic components of the range-local control-flow graph.
Nested loops can share one component.
Inline range boundaries can omit edges outside those ranges.
Memory notes describe source use and native stack access, not proved pointer ownership.

`rlp.decodeItem` survives at `0x80116c34` with 464 bytes and 116 instructions.
It has no call sites and two cyclic components.
`INVENTORY.md` gives the compact function inventory.
`symbols.txt` preserves the complete ELF symbol table.
`disassembly.objdump` preserves the complete disassembly.
`SHA256SUMS` records the published artifact hashes.
