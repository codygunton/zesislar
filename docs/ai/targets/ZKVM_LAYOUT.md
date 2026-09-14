# Phase 7 ELF layout

The proof ELF stays frozen through CP5. The separate target prepares the Phase 7 relink.

## Linked map

| Region or symbol | Address or range |
|---|---|
| Executable `.text` | `[0x80000000,0x800070e0)` |
| Read-only `.rodata` | `[0x80008000,0x800087cc)` |
| Writable `.sdata` | `[0xa0430000,0xa0430010)` |
| Stack | `[0xa0000000,0xa0400000)` |
| Heap | `[0xa0431000,0xb8431000)` |
| Input buffer | `[0xb8431000,0xbc431000)` |
| I/O context | `[0xbc4310b8,0xbc4310d8)` |
| `_start` | `0x80000000` |
| `read_input` | `0x80000028` |
| `write_output` | `0x80000078` |
| `zkvm_exit` | `0x800000ac` |
| `memcpy` | `0x800000bc` |
| `main` | `0x80004b98` |
| `ZKVM_HEAP_TOP` | `0xa0430000` |
| `ZKVM_HEAP_POS` | `0xa0430008` |

The heap capacity is 384 MiB. The input capacity is 64 MiB.
The script maps the stack as a writable NOLOAD segment.
The script aligns rodata to a page boundary.
This alignment prevents qemu-user from removing execution permission from the last text page.
The script uses `SUBALIGN(4)` inside text.
The script adds no padding inside text.
The script preserves the runtime's existing instruction padding.

## Upstream constraints

[ZisK v1.2.0-alpha](https://github.com/0xPolygonHermez/zisk/tree/v1.2.0-alpha) resolves to `fbbc69bcd`.
Its `ziskbuild/zisk_linker_script.ld` fixes ROM at `0x80000000`.
Its `core/src/mem.rs` defines the stack, reserved registers, output range, and general-purpose RAM.
Its heap limit is `0xbfff0000`.
The stale eth-act linker script does not define this layout.

[OpenVM commit 16c26a32](https://github.com/openvm-org/openvm/tree/16c26a32) implements the RV64 preview target.
Its `crates/toolchain/transpiler/src/elf.rs` accepts 64-bit RISC-V executable files.
That loader checks the entry alignment and the segment bounds.
It decodes every word in an executable segment.
It requires contiguous executable segments.
The separate read-only segment prevents rodata decoding.
The target keeps all addresses below 4 GiB.

## Binary target and evidence

Binary PR [#104](https://github.com/codygunton/binary-fv-experiment/pull/104) stays open.
The target is `zesuSszDecodeZkvmElf`.
Its ELF is `/nix/store/4xrdwkcz8vn966rgr1jkqd802jmlblv5-zesu-ssz-decode-zkvm-rv64im-elf-d67f28c/bin/zesu-ssz-decode`.
The target reuses the pinned Zig object and the default host and context assembly.
The target generates a runtime copy that selects the heap capacity through `BINARY_FV_HEAP_MIB=384`.
The default runtime source path excludes the two new assembly and linker files.
The default target resolves to its exact pinned store path.
Its SHA256 is `3e13afeae5719e10c65a89ea1b8a9afdb60b360e7e18faa81c31a71a44dcd8fb`.
All 12 qemu-user vectors produce the same output bytes as the default ELF.
ZisK reaches writeFailure at step 4856.
ZisK reaches the exit spin at PC `0x800000b8` at step 4870.
A bounded 50,000-step run stays there without a fault.
The bounded run reports `EmulationNoCompleted` because the host stub spins.
The OpenVM CPU build passes in 39.65 seconds.
A bounded 10,000-instruction run reaches PC `0x800000b8` without a fault.
The runner reports `terminated=false` because the existing host stub spins.

## Measured instruction changes

The writeSuccess region retains all 825 instruction positions.
Its two changed words form the rodata reference at offsets 208 and 212.
Its other 79 `auipc` instructions target calls inside text.
The relink preserves those call encodings.
Main retains its instruction positions and changes four words.
The helper changes contain references to heap globals and the I/O context.
The start file grows from 32 bytes to 40 bytes because it initializes the stack.
The old text base and the new text base therefore do not give the body relocation delta.
The body delta is `0x7ffefee8`, which the tool obtains from `main`.
The tool maps named symbols exactly before it applies that delta.
It rejects a text symbol that violates the common body delta.

## Phase 7 procedure

1. Obtain the Phase 7 merge review after CP5.
2. Merge the binary PR through the coordinating session.
3. Update the binary flake input.
4. Emit the new map with `tools/machine_map_from_elf.py`.
5. Supply the explicit Sail policy record with `--policy-record`.
6. Add the emitted `zkvmMap` beside `defaultMap`.
7. Generate the configuration from that map.
8. Regenerate the dumps and traces for the new ELF.
9. Run `tools/relocate_pcs.py --dry-run --check` with both ELFs.
10. Review every proposed rewrite.
11. Resolve the synthetic instruction address in `Proofs/Tests/TraceResume.v` explicitly.
12. Run the tool with `--apply --check` only after the check passes.
13. Commit the address rewrite separately.
14. Rebuild every proof.
15. Run `check-iris` before CP6.

The map tool obtains addresses from sections, symbols, and load segments.
The ELF does not encode Sail flags.
The tool reads those flags directly from the explicit Coq policy record.
Its `--check` option rejects any difference between ELF addresses and the supplied record.
This input prevents a second copy of the policy constants.
Its JSON output and Coq output round-trip to all 38 `defaultMap` fields.
The record parser rejects expressions that it cannot evaluate.

The relocation tool defaults to a dry run.
It prints every rewrite with its file and line.
It preserves the encoded instruction words in dumps.
It rewrites dump PCs and symbolic branch targets.
A separate main-dump dry run reports 31 address rewrites.
Phase 7 regenerates changed instruction bytes from the new ELF.
It changes `.v` files, `.dump` files, and coverage files.
It checks literal `instr`, `instr_pre`, and `instr_body` addresses against the new disassembly.
It checks all files before it writes any file.
It requires `--check` for `--apply`.
The initial dry run reports 6,549 rewrites across 1,208 files.
It reports one synthetic instruction address outside the disassembly.
The tool accepts explicit `--exclude` paths for reviewed synthetic fixtures.
A second dry run excludes only `ZesuSsz/Proofs/Tests/TraceResume.v`.
That check passes with the same 6,549 rewrites.
The port track applies no rewrite.
