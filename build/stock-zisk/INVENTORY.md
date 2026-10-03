# Stock ZisK function inventory

Stock zesu `d8071c4`, ZisK `v1.2.0-alpha`, Zig `0.16.0`, ReleaseFast.

S = separate symbol. I = DWARF inline instance. N = no symbol or inline instance.
I/C/L = instructions / call sites / cyclic CFG components. Counts describe compiled code.
The JSON records addresses, sizes, call targets, loop edges, stack offsets, and memory notes.

| Function | State | I/C/L | Function | State | I/C/L |
|---|---|---:|---|---|---:|
| `ssz.decodeByteListList` | S | 104/1/1 | `arithmetic.byteSize` | I | 141/0/0 |
| `ssz.decodeWithdrawal` | I | 123/0/0 | `arithmetic.sdiv` | I | 69/1/0 |
| `ssz.decode` | I | 2941/18/5 | `arithmetic.smod` | I | 67/1/0 |
| `rlp_decode.decodeBlockHeader` | N | 0/0/0 | `arithmetic.signextend` | I | 112/0/0 |
| `rlp_decode.decodeParentHeader` | S | 367/21/3 | `bitwise.opAnd` | S | 41/0/0 |
| `rlp_decode.decodeWithdrawals` | N | 0/0/0 | `bitwise.opOr` | S | 41/0/0 |
| `rlp_decode.decodeTxList` | N | 0/0/0 | `bitwise.opXor` | S | 41/0/0 |
| `rlp_decode.decodeSingleTx` | S | 133/8/0 | `bitwise.opNot` | S | 34/0/0 |
| `rlp_decode.decodeTxFields` | S | 3287/91/45 | `bitwise.opByte` | S | 71/0/0 |
| `rlp.decodeItem` | S | 116/0/2 | `bitwise.opShl` | S | 75/0/0 |
| `arithmetic.opAdd` | S | 50/0/0 | `bitwise.opShr` | S | 75/0/0 |
| `arithmetic.opSub` | S | 51/0/0 | `bitwise.opClz` | S | 173/0/0 |
| `arithmetic.opMul` | S | 80/0/0 | `bitwise.opSar` | S | 129/0/0 |
| `arithmetic.opDiv` | S | 62/1/0 | `comparison.opLt` | S | 54/0/0 |
| `arithmetic.opSdiv` | S | 113/1/0 | `comparison.opGt` | S | 54/0/0 |
| `arithmetic.opMod` | S | 62/1/0 | `comparison.opSlt` | S | 56/0/0 |
| `arithmetic.opSmod` | S | 109/1/0 | `comparison.opSgt` | S | 56/0/0 |
| `arithmetic.opAddmod` | S | 728/3/13 | `comparison.opEq` | S | 45/0/0 |
| `arithmetic.opMulmod` | S | 736/3/4 | `comparison.opIsZero` | S | 34/0/0 |
| `arithmetic.opExp` | S | 340/0/1 | `gas_costs.coldAccountAccess` | I | 3/0/0 |
| `arithmetic.opSignextend` | S | 142/0/0 | `gas_costs.coldStorageAccess` | N | 0/0/0 |
| `arithmetic.addmod` | I | 664/3/13 | `gas_costs.costPerStateByte` | N | 0/0/0 |
| `arithmetic.mulmod` | I | 671/3/4 | `gas_costs.memoryExpansionCost` | N | 0/0/0 |
| `arithmetic.toLimbs` | I | 40/0/0 | `gas_costs.memoryCost` | N | 0/0/0 |
| `arithmetic.fromLimbs` | I | 15/0/0 | `gas_costs.toWordSize` | N | 0/0/0 |
| `arithmetic.div128by64` | I | 707/0/36 | `gas_costs.getSloadCost` | N | 0/0/0 |
| `arithmetic.limbLessThan` | I | 26/0/0 | `gas_costs.sstoreClearsRefund` | I | 1/0/0 |
| `arithmetic.mulFull` | I | 106/0/0 | `gas_costs.getSstoreCost` | I | 236/0/0 |
| `arithmetic.limbMod` | S | 598/2/11 | `gas_costs.getSstoreCostAmsterdam` | I | 80/0/0 |
| `arithmetic.limbDivMod` | S | 672/2/11 | `gas_costs.getCallGasCost` | I | 124/0/0 |
| `arithmetic.mod512by256` | N | 0/0/0 | `validation.calculateInitialGas` | I | 265/0/4 |
| `arithmetic.expMod256` | I | 123/0/1 | `validation.calculateInitialGasAmsterdam` | I | 190/0/2 |

Decoder memory includes input slices, heap output, and native stack frames.
EVM handlers use the heap-backed operand stack and gas state.
Arithmetic helpers use values and local arrays. Gas helpers inspect execution state.
DWARF inline ranges can overlap. Do not sum their counts as binary size.
An absent emitted instance does not establish that a function is unreachable.
This inventory does not establish execution correctness.
