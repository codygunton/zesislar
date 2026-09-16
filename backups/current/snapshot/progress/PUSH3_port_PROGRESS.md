# PUSH3 port progress

The port track prepares Phase 7. The pinned proof ELF stays frozen through CP5.

## Deliverables

- Binary commit `b67884e8` adds the complete linker script, start file, target heap define, and Nix target.
- Binary PR [#104](https://github.com/codygunton/binary-fv-experiment/pull/104) is open and unmerged.
- The new ELF is `/nix/store/4xrdwkcz8vn966rgr1jkqd802jmlblv5-zesu-ssz-decode-zkvm-rv64im-elf-d67f28c/bin/zesu-ssz-decode`.
- The default rebuild resolves to the exact pinned ELF store path.
- Its SHA256 remains `3e13afeae5719e10c65a89ea1b8a9afdb60b360e7e18faa81c31a71a44dcd8fb`.
- All 12 qemu-user smoke vectors match the default output bytes.
- ZisK v1.2.0-alpha (`fbbc69bcd`) loads the ELF and reaches writeFailure at step 4856.
- ZisK reaches the exit spin PC `0x800000b8` at step 4870.
- A 50,000-step bounded run stays there without a fault.
- The CPU-only OpenVM build at `16c26a32b` passes in 39.65 seconds with j16.
- The bounded OpenVM run reaches PC `0x800000b8` after 10,000 instructions without a fault.
- The map tool matches all 38 `defaultMap` fields through JSON equality and a Coq round-trip.
- The relocation dry run reports 6,549 rewrites across 1,208 files.
- The instruction check reports one synthetic address at `Proofs/Tests/TraceResume.v:5`.
- No proof file changed.

## Tests and limits

Nix command: `nix build .#zesuSszDecodeZkvmElf .#zesuSszDecodeRv64Elf --no-link --print-out-paths --max-jobs 1 --cores 16`.
The command passed.
The script ASSERT pins match the ten first-link symbols.
The existing qemu plugin captures each `write_output` payload.
The smoke check concatenates those payloads before it compares each vector.
The new target maps its stack as a writable NOLOAD segment.
The target aligns rodata to 4096 bytes to avoid qemu-user page permission overlap.
These changes stay inside the approved layout.

ZisK initially failed at the link because `libiomp5` was absent from the library path.
The cached retry passed with `LIBRARY_PATH=/opt/intel/oneapi/compiler/latest/lib`.
The loader used that directory in `LD_LIBRARY_PATH`.

The tools passed `python3 -m py_compile`.
Four relocation cases check the start symbol, writeSuccess entry, output-size address, and an unchanged small literal.
The map tool reads Sail flags directly from the explicit Machine.v policy record.
It stores no duplicate policy constants.
The final zesislar commit waits for the orchestrator's map and trace update and the required `check-fast` gate.

## Dry-run counts

| Directory | Rewrites |
|---|---:|
| ZesuSsz/Compliance | 4 |
| ZesuSsz/Contracts | 11 |
| ZesuSsz/Export | 4 |
| ZesuSsz/Generated | 117 |
| ZesuSsz/Proofs/AllocatorGet | 33 |
| ZesuSsz/Proofs/ReadInput | 55 |
| ZesuSsz/Proofs/Tests | 160 |
| ZesuSsz/Proofs/WriteFailure | 171 |
| ZesuSsz/Proofs/WriteSuccess | 5845 |
| ZesuSsz/Proofs/ZkvmExit | 57 |
| tools | 92 |

Logs reside in the port worktree's `_build/agents/port/logs/`.

The second instruction check excludes only the reported synthetic fixture through an explicit command argument.
It passes with the same rewrite count.
The tool applies no rewrite.

Port commits: `b87abaf4` adds the ELF map tool. `2f246567` adds the dry-run relocation tool.
The pending final commit adds the layout document and rejects text symbols outside the common body delta.

A separate main-dump dry run reports 31 address rewrites.
The tool preserves encoded instruction words and rewrites branch targets and PCs.
The dump fixture stays unchanged.

Six machinePc offset cases pass in dry-run mode.
The cases check main, writeSuccess, the start entry, the gp pair, the main call, and the initial spin.
The tool adjusts body offsets by eight and handles the start insertion explicitly.

The Phase 7 address rewrite must exclude `ZesuSsz/Contracts/Machine.v` to preserve the pinned defaultMap.
The map tool supplies zkvmMap separately.

The emitted Coq definition imports `ZesuMachineMap.Machine`.
The source remains `ZesuSsz/Contracts/Machine.v`.
The updated Coq output round-trips to all 38 defaultMap fields.

An identical-ELF dry run reports zero rewrites.
Its instruction check passes.
The tool rejects an unsupported start-size change.

The instruction-word safeguard removes four false candidates from Generated/Level1.v.
The final local dry run reports 6,545 address rewrites across 1,208 files.
The Generated directory now contains 113 address rewrites.
Every other directory count stays unchanged.
The word regression reports three address rewrites and no encoded-word rewrite.

## Safeguard audit after the approved map port

The port branch rebased onto f0054a24.
The three existing port commits now are af651e73, 8dbba66b, and f5152832.
The pinned defaultMap stays unchanged.
The extracted zkvmMap is an address preview with the supplied Sail policy.
Phase 7 requires a reviewed target policy before trace generation.
The current configuration stays unchanged through CP5.

Ten tool regressions pass in 0.762 seconds.
Both map formats match all 38 pinned fields.
The map tool rejects an invalid output name and mismatched ELF addresses.
The relocation tool rejects unsupported start growth and inconsistent function offsets.
Word guards preserve decimal values, 64-bit values, and multiline definitions.
The extended word test checks seven address rewrites without changing its source.
The offset fixture checks six instructions and reports four rewrites.
The dump fixture reports 31 rewrites.
The original word fixture reports three rewrites.
Every fixture uses dry-run mode.

The initial worktree dry run reports 11,628 rewrites across 1,316 files.
Its check rejects only the synthetic TraceResume instruction at 0x10000.
Both runs exclude ZesuSsz/Contracts/Machine.v.
The final run also excludes ZesuSsz/Proofs/Tests/TraceResume.v.
The final run reports the same counts and no check errors.
The identical-ELF run reports zero rewrites and no errors.
No address rewrite runs in apply mode.
No binary rebuild, decoder trace generation, or proof edit occurs.
PR104 stays open at b67884e8e3142dda6b4d690cdf91bc5d225305fe.
The pinned ELF SHA256 is 3e13afeae5719e10c65a89ea1b8a9afdb60b360e7e18faa81c31a71a44dcd8fb.
The final port gate runs with CHECK_AGENT=port and AGENT_JOBS=16.

The f0054a24 check-fast gate passed in 359.925 seconds at 2,598,532 KiB peak RSS.
The port branch then rebased onto 3bfd25c1.
The repeated audit reports 11,639 rewrites across 1,318 files.
The final check has no errors with the same two exclusions.
The repeated identity check reports zero rewrites.
All ten tool regressions pass again in 0.698 seconds.

Safeguard commit: 2e04603b0aa6a1f210775c8753f7962c74ccd5ab.
The final check-fast gate passed in 0.585 seconds at 135,164 KiB peak RSS.
The outer gate record reports 3.009 seconds and 603,096 KiB peak RSS.
The build uses _build/agents/port, cache enabled, and 16 workers.
The branch contains rebased preparation commits 399bf0bd, a39510ae, and 95c7ea8f.
The worktree is clean.
No lemma changed, so Print Assumptions does not apply to this commit.
The bounded port assignment ends at this reviewable commit.

### Multiline tuple correction

Root found an encoded tuple word that changed across a line break.
The word guard now keeps a pending tuple value across blank lines.
Four dry-run cases check hexadecimal and decimal words with and without blank lines.
Each case preserves its source and reports four address rewrites.
The original ten tool regressions also pass in 0.640 seconds.
The port fast gate passes in 0.594 seconds at 136,344 KiB peak RSS.
The outer record reports 2.064 seconds at 602,576 KiB peak RSS.
No relocation runs in apply mode.
Multiline tuple fix commit: c4574d64.
The port worktree is clean.
