The switched rule proves low-bit mask equalities before general arithmetic unfolds them.
The rule supports arbitrary widths, integer offsets, and bitvector offsets.
The rule does not name a PC, a function, or a contract.

The frozen switch-off solver fails. The switch-on solver closes the identical equality.
All nine regression statements compile. MCP checks both frozen proofs and the regression module.
MCP verifies the frozen proofs and the regression module with no assumptions.
The largest measured owned MCP scope uses 1,277,427,712 bytes.
The check-fast gate passes in 151.561 seconds with six workers.
The gate records a peak child RSS of 2209904 KiB.
This checkpoint closes no machine instruction or block.

The announced source pointer contains mask127 without addition. It does not contain the announced six-line instance.
I sent this source discrepancy to the parent. I inspected the accepted error route without changing it.

The evidence file binds source hashes, frozen captures, archived logs, and measurements.
Evidence: evidence.json; SHA-256 c862d240714985775d72e8b743b554d968d2d9d1c743232c68349cb7eb72aafb.
Item window: 2026-10-05T05:49:34.261000+00:00 through 2026-10-05T06:13:50.122173+00:00.
The parent did not supply its metrics for this item.
The report binds the pre-commit base. The checkpoint message supplies the review commit.
METRICS: item=Q56-low-mask kind=rule commit=b76e744a00199607e0609926b42088b1e1b57146 child_min=24.264 parent_min=unavailable tokens_child=8761482 tokens_parent=unavailable gate_wall_s=151.561 gate_jobs=6 instr_closed=0 blocks_closed=0 rules_added=zesu_low_mask_if_enabled rules_reused=bv_wrap_bv_wrap,bv_wrap_add_idemp_r residual_classes=none hand_lines=0 rework=repair
