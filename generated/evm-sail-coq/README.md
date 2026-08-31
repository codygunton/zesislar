# Pinned EVM-Sail Rocq extraction

These files come from `frisitano/evm-sail@d0e4aabdde52f9158d191dbc8add444abffd9a6a`.
EVM-Sail generated `evm_decoder.v` and `evm_decoder_types.v` with its pinned Sail compiler.
The decoder-only Sail project avoids unrelated EVM execution code and Rocq 9 syntax.
It retains `decode_stateless_input` and all required types and host operations.
The regeneration script qualifies the generated sibling import for the Dune theory.


The normal build uses this snapshot. The regeneration check must compare generated files
byte-for-byte with this directory.

The Coq 8 build compiles `evm_decoder_types.v` only.
It keeps `evm_decoder.v` as the reviewed Rocq 9 action source.
`DecoderModel` provides the explicit conditional boundary between these kernel versions.
