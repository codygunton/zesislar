# P0-E condition 4

The stock manifest binds the Sail snapshots, compiler, Coq plugin, project, slice commands, and input shim.
`build.py --check` checks the snapshot files against their SOURCE.json records.
The checker rejects a compiler or plugin identity that differs from either snapshot record.
Handwritten Rocq modules use version control and the Rocq gates.
The manifest no longer binds those modules.

The compiler and plugin copies came from the matching build in the spec worktree.
Their archive names contain their SHA-256 hashes.
Item E must document retrieval for a clean clone.

- `sail/rlp/SOURCE.json`: `d76ad3f88b3033bfa718ec1b64c5e690189f89dbc96b35f92939d6c8442ae498`.
- `sail/transactions/SOURCE.json`: `23730618d6da12ce0a439f6dafc24ae05ebe76ac41690c8feea7f435768966f2`.
- `sail/shim`: `e80d32b97ed05d80cb7b1a37755c95377f4ed4ffdcea062eaf24ce59e436c0c1`.
- `sail/compiler`: `517d6d68de8947926a0950d59de544350bf3ec289153e6ba63c6cfd5a664e16b`.

Artifact identity: `7b98aa248fb821f9508202849f909469d271e68d651e558ddbe5a3f18c461b5d`.

The 16 focused manifest tests pass.
The tests reject changed snapshots, a changed plugin, and disagreement with the compiler record.
