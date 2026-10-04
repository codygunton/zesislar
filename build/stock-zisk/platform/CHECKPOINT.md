# Dedicated ZisK platform layer

The adapter enforces the selected ELF regions through five platform hooks.
The build retains every other pinned IR declaration byte-for-byte.
The adapter does not change instruction or CSR semantics.
The selected configuration permits misaligned scalar accesses.
Generic ROM, CLINT, and HTIF fields remain declared but unused by the selected memory hooks.

The selected emulator creates a zero eight-byte header at 0x40000000.
It then appends a multiple-of-eight input at 0x40000008.
Mem::add_read_section merges these adjacent sections.
The input state relation therefore uses one populated section ending at 0x40000008 + input_len.
See core/src/mem.rs:240-293 and emulator/src/emu_context.rs:50-71 at the pinned commit.
The source audit found no runtime addition of input sections.
The ROM loader adds the selected ELF data sections at emulator/src/emu.rs:130-142.
Runtime input services can change free_input.
The adapter keeps that value in an explicit register.

An eight-byte header read returns zisk_free_input.
Other fully contained populated input reads use the memory bytes.
A read outside the populated section returns zero for its complete width when the fallback interval contains it.
A crossing from the header into the data remains contained in the merged section.
A crossing from the header past an empty section fails because its address precedes the fallback interval.

The smoke suite covers all eight enforcement-table rows.
It also covers forbidden input writes, text data reads, gap loads, misaligned RAM accesses, and input special cases.
It covers empty input, header sub-width reads, both section boundaries, ROM and RAM boundaries, and address wrap.
These instruction traces check platform enforcement.
They do not prove a decoder contract or a correspondence theorem.

PLATFORM.md retains the remaining proof obligations.
The adapter does not discharge caller footprints, allocator correctness, code identity, or runtime service contracts.
The memcpy CSR service remains outside this adapter.

The compiler uses Sail 0.17 and the local Isla plugin source.
The plugin changes one obsolete option assignment for the installed Sail API.
The build report records that patch and hashes the compiler and plugin.
The platform fragment binds the source, snapshot, configuration, and smoke traces for parent integration.
