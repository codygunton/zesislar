# TF1 source junction

The caller conversion preserves the original 720-byte source ownership.
The source partition has byte lengths 608, 16, 64, and 32.
The 16-byte part becomes one two-word array.
The 64-byte part becomes one eight-word array.
The prefix and suffix remain in `tailFieldsSourceUntouched`.
That predicate is globally opaque.
The word view has four top-level conjuncts, including `True`.
The caller view has three top-level conjuncts.
The caller remainder excludes the source array.
The original caller statement stays unchanged.
The junction equivalence supports both entry conversion and exit reassembly.

MCP checked the partition proof with five recorded lines.
MCP checked the reassembly proof with five recorded lines.
MCP checked the caller equivalence with four recorded lines.
The compiled assumptions for the open, close, and caller equivalence are:

```
Closed under the global context
```

`rocq_verify` accepted the caller equivalence with `assumptions: []`.
No existing consumer imports this new module yet.
The existing shared-boundary consumer remains
`WriteSuccessExactSuffixHashesTailConnection.v`.
The retained dependency graph gives that consumer no further consumers.
The seven checkpoint assumption targets retain their source statements.
The root queues their compiled comparison and the full preview.

The first MCP preamble attempt returned `No node at point` with reason `crashed`.
The file-based MCP session succeeded.
No scratch fallback was necessary for this junction.
