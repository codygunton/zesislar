# Q27 decodeItem block probe

This is diagnostic evidence, not a machine proof. The probe used the selected ELF lookup and the Q27 entry resources. It did not change the public contracts.

| Entry | First `zesu_block` residual | Class | Next observed goal after explicit continuation entry |
| --- | --- | --- | --- |
| `0x800d6a24` | `(conditional instr_pre) -∗ True -∗ "PC" ↦ᵣ RVal_Bits (Z_to_bv 64 2148362788) -∗ WPasm a800d6a24.a800d6a24` | Continuation handoff | `li_tactic (regcol_compute_hint (regcol_lookup (KindReg "rv_enable_pmp")) zesu_ram_sys_regs)` after three `zesu_liAStep` calls. |
| `0x800d6ac4` | `(conditional instr_pre) -∗ True -∗ "PC" ↦ᵣ RVal_Bits (Z_to_bv 64 2148362948) -∗ WPasm a800d6ac4.a800d6ac4` | Continuation handoff | The same `rv_enable_pmp` lookup after three `zesu_liAStep` calls. |
| `0x800d6a38` | `(conditional instr_pre) -∗ True -∗ "PC" ↦ᵣ RVal_Bits (Z_to_bv 64 2148362808) -∗ WPasm a800d6a38.a800d6a38` | Continuation handoff | The trace entered the `mstatus` field lookup. A direct `zesu_block` after the handoff timed out. |
| `0x800d6ad8` | `(conditional instr_pre) -∗ True -∗ "PC" ↦ᵣ RVal_Bits (Z_to_bv 64 2148362968) -∗ WPasm a800d6ad8.a800d6ad8` | Continuation handoff | The trace entered the `mstatus` expression and shape check. |

The entry resources remained `decodeItemByteFoldResources` with the original `i < n` and byte witness on the loop headers. The two length entries retained `decodeItemByteFoldResources` at `i = n`. The diagnostic continuation replaced each Q27 exit resource with `True`. The table abbreviates the conditional `instr_pre` expression in each goal. The omitted loop resources are the updated `decodeItemByteFoldResources` at `i + 1`, the loaded byte value, and the exit equality `i + 1 = n`. The omitted length resources are `decodeItemFoldCheckedResources` on both branches. Thus no result above proves a block edge or an I1 add/branch obligation.

The exact string-fold preservation probe reached `WPasm a800d6a24` with a 31,859-character selected lookup goal. A second `zesu_block` timed out and drove Rocq MCP above 16 GiB. I stopped that probe under the 6 GiB proof-module limit. Each diagnostic probe used fewer than ten tactic lines and no `iRename select`. No probe reached a byte load or the length-check branch.
