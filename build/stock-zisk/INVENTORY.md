# Selected stock decoder inventory

Conditional static inventory. This report is not a machine-code proof.

| Function or proposed region | Instructions | Blocks | Branches | Loops | Calls |
|---|---:|---:|---:|---:|---:|
| rlp.decodeItem | 116 | 24 | 14 | 2 | 0 |
| rlp_decode.nextUint64 | 53 | 10 | 5 | 1 | 1 |
| rlp_decode.decodeParentHeader | 367 | 87 | 49 | 3 | 21 |
| rlp_decode.decodeTxFields | 2825 | 591 | 320 | 45 | 87 |
| rlp_decode.txAccessList | 323 | 53 | 28 | 1 | 12 |
| array_list.Aligned([32]u8,null).ensureTotalCapacity | 107 | 23 | 9 | 0 | 4 |
| array_list.Aligned([32]u8,null).toOwnedSlice | 121 | 27 | 12 | 0 | 6 |
| array_list.Aligned(input.AccessListEntry,null).toOwnedSlice | 138 | 27 | 12 | 0 | 6 |
| alt_fl_alloc.alloc | 186 | 55 | 34 | 0 | 0 |
| alt_fl_alloc.remap | 9 | 1 | 0 | 0 | 0 |
| alt_fl_alloc.free | 149 | 43 | 28 | 0 | 0 |
| memcpy | 3 | 1 | 0 | 0 | 0 |
| dispatch | 31 | 1 | 0 | 0 | 0 |
| type_0 | 405 | 80 | 45 | 7 | 11 |
| type_1 | 388 | 85 | 49 | 8 | 13 |
| type_2 | 415 | 91 | 54 | 9 | 14 |
| type_3 | 549 | 115 | 68 | 11 | 19 |
| type_4 | 941 | 210 | 104 | 10 | 30 |
| shared_tail | 96 | 9 | 0 | 0 | 0 |
| decodeSingleTx | 107 | 23 | 13 | 0 | 7 |

Branches count conditional branches. Loops count cyclic strongly connected components.
Calls include direct calls, resolved allocator calls, and external tail transfers.
Blocks end at calls and control transfers. Region proposals contain complete blocks.
The five dispatch entries come from table bytes after a checked mask and scale sequence.
The dispatch index requires the entry bound 0 through 4.
The inline caller contains two decoded guards that accept byte values 1 through 4.
Caller proofs must connect those guards and the legacy zero argument to the dispatch contract.
The allocator calls use the selected vtable under the recorded entry condition.
The inventory reads allocator targets from the actual vtable bytes.
The scan found no missing callee and no unresolved transfer inside the selected regions.
The only expected unmodeled operation is memcpy CSR 0x813.
The ELF symbol gives memcpy three instructions. Its following padding instruction lies outside that symbol.
The decodeSingleTx proposal adds five instructions to obtain complete blocks around its DWARF ranges.
The region proposals do not establish approved Level 1 boundaries.
The selected platform adapter is recorded. Selected-ELF trace generation is a separate checkpoint.
The entry smoke and return chains did not run.
