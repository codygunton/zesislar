# decodeItem region traces

`make stock-decodeitem-region-traces` restores and checks the pinned `decodeItemRegions` group.
The logical owner is `ZesuSsz.Stock.DecodeItemRegions`.
The group contains 116 instructions, 15 loads, and 35 stores.
The existing `decodeItem`, `closure`, and `eql` groups keep their original bytes.

Each memory access has an unsigned 64-bit constraint.
The constraint preserves the packet's complete region union.
It compares the address with the region end minus the access width.
An input access also checks the dynamic input end and the subtraction width.
Stores permit only RAM.
The 50 Assume obligations remain open.
This group adds no contract premise and claims no native proof coverage.

`regions.json.gz` preserves the original packet with SHA256
`e9f2697fa7d5611887695b66130958957a672ee74707650e5f20fa91e3eb0eaa`.
`PATH-MAP.json` binds its historical source paths to retained files.
The tools use no host-path fallback.
The ELF descriptor reuses the existing `stock-zisk.eql-trace-input.v1` schema.
That schema names the ELF mapping, not the emitted group.

The first generation used main `d405a6efa83f8f7026806a2bbe66754635e0beec`.
It took 12.245 seconds with six workers.
Its peak child RSS was 115052 KiB.
The compressed records preserve the generation inputs and report.
