# P0-E condition 5

MachineMap records each populated ELF load extent with an exclusive end address.
Each record gives the file-backed end and the read, write, and execute permission bits.
The generator uses the manifest-bound ELF segment table.
The map contains all four load segments, including the zero-filled writable extent.
The generator does not assign ELF permissions to gaps or the complete RAM window.

The legacy fork map has no populated section records.
The stock map retains its dynamic input registers and platform configuration.

Rocq-MCP compiled Machine.v with Coq 8.19.2+lsp.
The four extent tests and 11 configuration tests pass.
The generator check confirms that the stock record matches the manifest-bound inputs.
The evidence gate now runs the manifest tests, extent tests, and generator check.
