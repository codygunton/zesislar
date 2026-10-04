# Selected arithmetic sites

This report records static analysis of the selected b5483dd ELF.
This report makes no execution claim.

- The long-string addition is at `0x800d6a38`.
  The unsigned rejection comparison is `bltu` at `0x800d6a3c`.
- The long-list addition is at `0x800d6ad8`.
  The unsigned success comparison is `bgeu` at `0x800d6adc`.
- The legacy chain identifier uses shifts and OR at `0x80002ad4` through `0x80002ae4`.
  The result store is at `0x80002e38`.

Both length additions use arithmetic modulo 2^64.
The legacy chain identifier retains the low 64 bits of `(v_raw - 35) / 2`.
The retained cast sequence does not check discarded bits.
These statements describe instructions and do not prove a complete decoder path.

`sites.json` contains exact bytes and relocated object DWARF mappings.
The generator checks function sizes, relocation deltas, instruction shapes, and each selected instruction word.
The generator refuses a changed ELF hash or object hash.

Run `python3 tools/stock_zisk/static_sites/collect.py` from the repository root.
The manifest fragment uses the recorded generator directory in the parent worktree.
The integrating worker must bind the fragment and regenerate its artifact identity.
