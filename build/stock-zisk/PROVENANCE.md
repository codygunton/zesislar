# Stock zesu on ZisK

This is stock zesu built with the authors' recipe at a different zesu revision.
The selected zesu commit is `b5483dda21d72405c50a22cb6406a1231e51a579`.
The authors' CI uses `329c0128`.
No release-ELF hash comparison establishes equality with a released artifact.

The build uses zesu-zkvm `be591e90ecbd94b0a3185809ba5ed74268558fa3`.
The runtime uses ZisK `fbbc69bcd2ea9a78d1a438b4a897bc48ff0b00a3`, release `v1.2.0-alpha`.
The build checks each source commit and rejects tracked source changes.

## Build and adapter test

The stock target is `rv64im-object` with `ReleaseFast` and Zig `0.16.0`.
The guest build uses the authors' `zisk/build.zig` and unmodified `zisk/zisk.ld`.
The first selected-target link used the unmodified `zisk_host.zig`.
That link passed without the appended `exit.zig`.
The recipe records the compiler hash, commands, host hash, object hash, and ELF hash.
The source checkout remains unchanged.

The object build took 18.530 seconds and used 468188 KiB peak memory.
The link took 3.066 seconds and used 301368 KiB peak memory.
Both commands allowed 24 workers.
These measurements report the maximum process memory from `wait4`, including child processes.
They do not report aggregate memory across concurrent processes.

## Preserved inputs

`build-recipe.json` records the original runtime archive and temporary object.
Their hash-named copies live in `~/zesislar-archive/stock-inputs/`.
The preservation step checked both copies against their original SHA256 hashes.
The original files remain in place.
The selected object also has a hash-named archive copy.

The runtime build used container image
`sha256:3c7565636c6516f21c630b4b7e803de59574e9381b50e2b4ae082b2b20751318`.
The mutable image tag does not identify the runtime input.
The original runtime command used `cargo +zisk build -p ziskos-staticlib`,
`--target riscv64ima-zisk-zkvm-elf --release --locked`, and
`--config 'profile.release.lto="fat"'`.

## Current evidence boundary

The ELF, disassembly, symbol table, and layout describe the selected revision.
The existing inventory, verification report, and comparison directory describe the earlier pilot.
The recipe labels those files as historical evidence.
The next step will replace the inventory with a scan of the selected ELF.
No execution test or proof establishes selected-target correctness at this checkpoint.
The exact platform model remains pending.

## Manifest checks

Run `python3 tools/stock_zisk/build.py --check --out build/stock-zisk`.
The check verifies source commits, source trees, empty patches, and build flags.
It checks the author recipe files and compiler executables against their hashes.
It checks preserved inputs, runtime inputs, the ELF layout, and every ELF section's bytes.
It regenerates the disassembly, symbol table, and layout report from the selected ELF.
The artifact identity binds later generated files to the recorded inputs and ELF.
Each derived file must declare that identity and its schema version.
A rebuild invalidates previously registered derived files.

The committed `bin/*` tools remain available for existing trace regeneration.
The manifest records their hashes.
The selected ELF build uses the separately recorded Zig and ELF tools.
This checkpoint does not migrate existing tools to Nix.

The runtime compiler executables also have checked archive copies.
This step reused the preserved runtime library.
It did not independently rebuild the runtime.
For a new output directory, supply the current recipe with `--runtime-build-recipe`.
