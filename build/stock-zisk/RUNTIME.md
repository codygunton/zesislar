# Runtime statement and allocator inventory

This checkpoint states the memcpy contract and records allocator data.
It does not prove either runtime service.
C4 must approve the memcpy statement before a proof uses a runtime premise.

## Memcpy boundary

The selected `memcpy` entry is `0x800e06c0`.
Its bytes are `73a035813300c50067800000`.
The function contains the CSR marker, its following add, and the return.
The source implements the marker as a transpilation pattern.
It does not execute a conventional CSR register update.

| Item | Statement |
|---|---|
| Destination | `x10` |
| Source | `x11` |
| Length | `x12` |
| Return address | `x1` |
| Integer clobbers | None |
| Scratch effect | The service first stores the length at `0xa0400f00` as eight little-endian bytes. |
| Copy effect | The service samples the source after the scratch store. It writes those bytes to the destination. |
| Overlap | The service permits overlap through a temporary source buffer. |
| Empty or identical copy | The scratch store occurs. The copy does not access the source or destination. |
| Source domain | A complete populated readable section contains the source access. |
| Destination domain | A writable section contains the destination access. |
| Scalar input behavior | The special input word and zero fallback do not apply to the DMA source read. |
| Public observations | The service emits no public runtime event. RAM writes remain explicit memory effects. |
| Caller continuation | The return preserves `x1`. The return PC clears bit zero. The contract requires four-byte alignment of that PC. |

`Contracts/ZiskRuntime.v` expresses the scratch order and memory frame pointwise.
The effect permits the source or destination to overlap the scratch word.
It preserves every integer register.
The statement carries no axiom or admitted proof.
Its explicit permission predicates require later instantiation on the approved platform.
The caller must supply its logical continuation separately.

The pinned ZisK sources establish these facts:

- `ziskos/entrypoint/src/dma/memcpy.s:8-11` supplies the three-instruction wrapper.
- `transpilers/riscv/src/riscv2zisk_context.rs:1003-1048,2509-2537` supplies the scratch store and service dispatch.
- `core/src/operations/dma_memcpy.rs:15-23` reads the length and calls `Mem::memcpy`.
- `core/src/mem.rs:877-968` supplies the section checks and overlap behavior.
- `core/src/zisk_inst_builder.rs:185-192` suppresses writes to architectural register zero.

## Allocator data

`runtime-inventory.json` records four vtable slots and their actual function addresses.
The slots name `alloc`, `resize`, `remap`, and `free`.
The inventory records the state byte, 22 free-list words, and both heap-position words.
It checks the vtable against the ELF symbols.
It checks each initial heap word against its linker symbol.
The state byte and free-list words use ELF zero initialization.
These initial values do not establish allocator invariants at decoder entry.

The allocator proof must establish ownership, disjoint allocations, arithmetic bounds, and heap capacity.
The inventory labels its evidence as static analysis.
It makes no selected-ELF execution claim.

```sh
python3 tools/stock_zisk/runtime_inventory.py \
  --manifest build/stock-zisk/build-recipe.json \
  --out build/stock-zisk/runtime-inventory.json
```
