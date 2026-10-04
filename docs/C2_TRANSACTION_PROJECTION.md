# C2 transaction projection for review

The proposed relation compares the selected Zig transaction fields with the pinned Sail `TransactionFields` value. The relation in `ZesuSsz/Compliance/ProjectionTransaction.v` covers all five types. It does not prove binary agreement. C2 remains open.

The relation maps type, nonce, gas limit, value, `r`, and `s` to their corresponding Sail fields. It maps Zig `gas_price` to Sail `max_fee`. It maps `gas_priority_fee` to `max_priority_fee`; for types 0 and 1, Zig leaves this field absent while Sail copies `max_fee`. It maps Zig `to` to Sail `is_create` and `recipient`, including the empty destination. It compares input bytes, access-list entries and counts, blob hashes and counts, and authorization tuples through source-backed encoded views. It compares the supplied raw bytes and public key bytes with Sail’s input slices.

The legacy relation converts Sail’s raw `v` to Zig’s chain identifier and parity. It requires the selected Zig narrowing cast to fit in 64 bits. Typed transactions use Sail’s chain identifier and `v` directly. The relation omits Zig `sender` and `signing_hash`. A separate C4 contract must cover those values or prove that the final observation does not depend on them.

The Q12 Sail audit ran each encoded item through `rlp_decode_item`, then through both integer decoders. These are decoder results, not full transaction results:

| Encoded case | Sail `u256` | Sail `uint64` | C2 issue |
| --- | --- | --- | --- |
| Nine-byte nonce | Success | Reject | Zig clamps long nonces in the reported source cases. |
| Seventeen-byte fee | Success | Reject | Zig clamps long fees in the reported source cases. |
| Leading zero | Reject | Reject | Zig accepts reported noncanonical cases. |
| More than 32 bytes | Reject | Reject | Zig’s clamping helpers can accept such inputs. |
| Canonical zero | Success | Success | This vector shows no decoder difference. |
| Noncanonical zero | Reject | Reject | Zig behavior still needs the selected-case check. |

The proposed C2 domain must state successful-result agreement and rejection agreement separately. It must resolve trailing data, integer widths, leading zeroes, typed signature `v`, destination width, legacy `v`, blob limits, and authorization grammar. The domain must cover meaningful inputs of every transaction type. The six Sail vectors do not establish the Zig or ELF outcome.

C4 needs fixed host-operation premises for input byte and word reads, keccak results, scratch capacity, writes, truncation, and returned values. It must also state how the supplied public key and raw bytes enter Sail. A proof must justify omission of hash-derived fields from this projection; the omitted fields alone do not establish independence.
