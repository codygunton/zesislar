# Selected ZisK platform checkpoint

The selected-target platform model remains unimplemented.
This checkpoint records source facts and a proposal for review.
It does not approve a replacement abstraction or change a contract.
Trace generation, the entry smoke test, and the return chains remain blocked.

## Artifact and source identities

The selected ELF has SHA256 `e44c18d54ae3d77832df92aceb6eb7119de8eb2e8f1f1b4e585a6e33ea04ff95`.
ZisK uses commit `fbbc69bcd2ea9a78d1a438b4a897bc48ff0b00a3`.
The guest recipe uses commit `be591e90ecbd94b0a3185809ba5ed74268558fa3`.
The local Isla snapshot uses commit `b58da9170470a422c9396983ac8f87f0a63ba6f8`.
The snapshot checkout has no tracked changes.
The audit records its IR hash and the hashes of the cited source files.

## Target memory and initialization

All ZisK references below use the selected source commit.
Intervals exclude their upper address.

| Region | Interval | Target behavior | Source |
|---|---|---|---|
| Input | `0x40000000..0x80000000` | Read-only, with the special cases below | `core/src/mem.rs:107-109,366-388` |
| Program ROM | `0x80000000..0x88000000` | ELF flags determine executable and readable segments | `core/src/mem.rs:137-141`; `transpilers/common/src/elf_extraction.rs:175-230` |
| Gap | `0x88000000..0xa0000000` | No mapped read or write section | `core/src/mem.rs:373-391,667-675` |
| RAM | `0xa0000000..0xc0000000` | Read-write | `core/src/mem.rs:113-115,341-357,658-688` |

The actual input limit is one GiB.
The nearby `128M` source comment does not match its hexadecimal constant.

The selected ELF has these occupied regions:

- The execute-only `.text` segment occupies `0x80000000..0x8010fd78`.
- The read-only `.rodata` segment occupies `0x8010fd80..0x80118678`.
- The `.bss` segment occupies `0xa0430000..0xa0d34520`.
- The initialized heap words occupy `0xa0d34520..0xa0d34530`.

ZisK keeps executable segments out of readable memory unless their ELF flags also permit reads.
The selected `.text` segment lacks that read flag.
The ELF layout report records the exact flags.

The emulator initializes the RAM region to zero.
It then applies ELF data and startup effects.
See `core/src/mem.rs:300-326` and `emulator/src/emu_context.rs:66-71`.
The linker sets `_init_stack_top` to `0xa0400000`.
The runtime loads that symbol in `ziskos/entrypoint/src/lib.rs:364-378`.
The stack occupies `0xa0000000..0xa0400000` and grows downward.
The system region occupies `0xa0400000..0xa0410000`.
The output region occupies `0xa0410000..0xa0430000`.
See `core/src/mem.rs:117-127`.

The initial `ZKVM_HEAP_POS` word at `0xa0d34520` contains `0xa0d34530`.
The initial `ZKVM_HEAP_TOP` word at `0xa0d34528` contains `0xbfff0000`.
The selected ELF bytes establish both values.
The allocator state starts at `0xa0534000`.
Its free lists start at `0xa0534008`.
These are startup facts, not assumptions that the heap stays unused at decoder entry.

## Access behavior that a model must preserve

ZisK accepts widths of 1, 2, 4, and 8 bytes.
Its indexed byte slices permit misaligned accesses.
See `core/src/mem.rs:337-409,464-570,658-688`.

An eight-byte read at `0x40000000` returns `Mem.free_input`.
See `core/src/mem.rs:366-368`.
The emulator initially places the input bytes at `0x40000008`.
See `emulator/src/emu_context.rs:66-68`.
Reads outside populated sections return zero within the remaining input interval.
See `core/src/mem.rs:383-388`.
This fallback returns zero for the whole access.
A flat byte map does not automatically reproduce a read that crosses a populated section boundary.
Decoder contracts must either exclude such accesses or preserve their target behavior explicitly.

The selected compiler enables `unaligned_scalar_mem` at `zesu/build.zig:715`.
The legacy transaction arm contains `ld a2,0(a1)` at `0x80001164`.
The following instructions read another eight bytes and four bytes from the same destination payload.
They implement the byte-slice copy in `src/stateless/rlp_decode.zig:471-481`.
The source checks the payload length, but it does not require eight-byte alignment.

For example, this source-level legacy transaction places its destination payload five bytes after the raw transaction address:

```text
dd80808094000000000000000000000000000000000000000080801b8080
```

An eight-byte-aligned raw address therefore gives these loads a misaligned payload address.
This evidence combines source inspection and selected instruction bytes.
It is not an execution of the selected ELF.

## Current Sail interface and exact limitations

The current project configuration defines one RAM interval and one generic ROM interval.
It disables PMP and misaligned accesses.
Its legacy RAM interval ends at `0x40000000`.
It does not describe the selected target.
See `ZesuSsz/riscv64_zesu.toml:39-57`.

The pinned IR exposes `rv_ram_base`, `rv_ram_size`, generic ROM and CLINT fields, and `rv_htif_tohost`.
See `riscv64.ir:19535-19633`.
Its physical-memory test checks interval membership, without an ELF permission table.
See `riscv64.ir:19636` and the `zwithin_phys_mem` definition.
Its checked reads and writes also dispatch to generic device handlers.
See `riscv64.ir:21449,21480,22034,22555`.
The configured HTIF address lies inside the target input interval.
Moving that address would not establish equivalence with ZisK.

The snapshot also supports locked PMP entries.
PMP means Physical Memory Protection.
It can express separate read, write, and execute permissions before physical-memory or device dispatch.
See `riscv64.ir:11023,11040,11151,22083,22588`.
Thus, the snapshot is not inherently limited to one permission interval.
However, PMP settings alone do not supply ZisK's special input value or zero-read fallback.
They also introduce system-register resources absent from the current project configuration.
No PMP-based platform contract was adopted here.

## Proposed decision

I recommend a dedicated ZisK platform adapter for the pinned Sail model.
The adapter should classify addresses from this ELF and the pinned target constants.
It should enforce the target permissions, widths, initialization, and input-read behavior directly.
It should remove generic ROM, CLINT, and HTIF dispatch from the selected decoder platform.
It should retain separately stated contracts for reachable ZisK services.
The current closure needs the `memcpy` CSR service.
The adapter must preserve the instruction semantics outside its platform hooks.
Its source, compiler, generated snapshot, and tests must enter the manifest.

The following table separates proposed enforcement from the required proofs.
No entry in its enforcement column describes an implemented model yet.

| Region | Pinned source | Proposed direct enforcement | Remaining proof obligation |
|---|---|---|---|
| Input | `core/src/mem.rs:107-109,366-388` | The adapter permits reads and denies writes. It implements the special word and whole-access zero fallback. | The state relation matches the input bytes, populated sections, and `free_input`. Caller proofs establish each decoder's permitted input footprint. |
| Executable text | `transpilers/common/src/elf_extraction.rs:175-230` | The adapter permits instruction fetches in executable segments. It denies data reads from the selected execute-only segment. | The code resources match the selected instruction bytes. Each control transfer stays within its approved region or callee contract. |
| Read-only data | `transpilers/common/src/elf_extraction.rs:253-268` | The adapter permits loads from readable ELF segments and denies stores. | The state relation matches the immutable segment bytes, including jump tables and the allocator vtable. |
| Gap | `core/src/mem.rs:373-391,667-675` | The adapter rejects accesses without a mapped section. | The decoder footprint excludes the gap and all forbidden boundary crossings. |
| RAM | `core/src/mem.rs:113-115,341-357,658-688` | The adapter permits bounded reads and writes of supported widths, including misaligned accesses. | The initial memory relation and each memory update agree with ZisK. Address arithmetic does not wrap. |
| Stack | `core/src/mem.rs:117-119`; `ziskos/entrypoint/src/lib.rs:364-378` | The adapter applies the RAM rules. Initialization supplies the selected stack top. | Frame ownership and stack bounds hold for all calls and returns. RAM permission alone does not prove stack bounds. |
| Heap | `zesu-zkvm/zisk/zisk.ld:147-153`; `core/src/mem.rs:113-115` | Initialization supplies the ELF heap words. The adapter applies the RAM rules. | The allocator proof preserves its bounds, metadata, free lists, and live allocations. |
| System and output | `core/src/mem.rs:121-127,644-653` | The adapter preserves the target RAM locations and any applicable target effects. | Each reachable runtime contract states its memory and observable effects. The current decoder closure needs the memcpy CSR contract. |

This proposal needs review before implementation because it changes the platform contract and system-register resources.
The coordinator must assign ownership of any contract or shared automation changes.
The existing file ownership permits the audit and configurations, but it does not authorize those shared changes.

A correspondence proof is an alternative that also needs explicit approval.
That alternative must state a relation between initialized ZisK states and the chosen Sail states.
It must establish matching instruction results, memory effects, and observable effects throughout the claimed decoder region.
It must include these six obligations from plan section 2.2:

1. Instruction fetches use permitted text addresses.
2. Loads use permitted input, read-only data, or RAM addresses.
3. Stores use writable RAM addresses.
4. Accesses do not cross forbidden boundaries or wrap an address.
5. Stack and allocator accesses remain inside their permitted regions.
6. Runtime effects satisfy their separately named contracts.

The state relation must also cover the special input word and the zero-read fallback.
It must preserve byte order and misaligned access behavior.
A footprint list alone does not prove this correspondence.
No such proof or abstraction accompanies this checkpoint.

## Current verification boundary

The source audit checked the target constants, load segments, stack symbol, and initialized heap words.
Its measurement was 1.212 seconds, 37504 KiB peak memory, and one worker.
The static closure and manifest checks pass under their recorded conditions.
The selected-target model enforces nothing yet because no selected model was adopted.
The raw dump remains unconfigured.
The entry proof and every return-site chain remain unrun.
The coordinator must obtain the platform decision before this work continues.
Independent artifact cleanup may continue while that decision remains pending.
