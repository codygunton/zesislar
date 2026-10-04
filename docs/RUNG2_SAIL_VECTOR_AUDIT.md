# Rung-2 Sail parent-header execution vectors

The [fixture](../ZesuSsz/Evidence/parent_header_vectors.json) records three mainnet headers from [`eth_getBlockByNumber`](https://ethereum.github.io/execution-apis/api/methods/eth_getBlockByNumber/). Two public RPC endpoints agreed on each block hash. The generator checked each RLP encoding against that hash with Keccak-256. The [Rocq audit](../ZesuSsz/Compliance/ParentHeaderVectorAudit.v) ran `runRlpNodeCursor`, then `runParentHeaderFields` through `sailParentHeaderRun`.

| Block and header form | RLP fields | Node cursor | Field decoder | Base fee | Blob gas used | Excess blob gas |
| --- | ---: | --- | --- | ---: | ---: | ---: |
| 12,964,999, pre-merge and pre-London | 15 | Success `(3, 517)` | Success | absent | absent | absent |
| 12,965,000, London base fee | 16 | Success `(3, 543)` | Success | 1,000,000,000 | absent | absent |
| 19,430,001, withdrawals root and blob fields | 20 | Success `(3, 603)` | Success | 48,743,138,495 | 131,072 | 393,216 |
| 19,430,001 with the final RLP byte removed | incomplete | Reject `RlpDecode` | not called | not available | not available | not available |

The successful Sail values also set `have_parent` and `have_state` to true. The last header contains a withdrawals root at zero-based RLP field 16. `ParentHeaderFields` does not retain that root. The truncated header fails during `rlp_node_cursor`, so the composed run returns its rejection without calling `decode_parent_header_fields`. These runs do not prove a machine contract, a Zig comparison, or a complete input domain.
