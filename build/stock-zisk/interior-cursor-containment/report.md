The guarded integer-address hook now accepts a proved interior cursor.
The hook proves no wrap and strict containment before it normalizes the address.
The hook keeps the original lookup continuation and owned array.
The existing switch uses #[export] Instance. A regression rejects activation through an imported test module.
The frozen off/on statements preserve the same fold bounds and LET0 alias. Off rejects the hook. On closes the selector.
MCP health, start, check, step_multi, final compilation, and statement verification pass. Six verified statements report assumptions [].
Nine test lemmas compile. Four new tests cover interior cursors, fold cursors, exclusive endpoints, and import isolation.
Both check-fast gates pass with six workers. Their total wall time is 234.092 seconds.
The maximum MCP scope peak is 1356931072 bytes. The first gate child RSS peak is 2224548 KiB.
No native block runs or closes. All existing fault, witness, and side-condition debts remain. No check-iris ran.
Logs and MCP evidence reside in the host archive. The archive index binds their hashes.
The checkpoint uses root b6c8185218aabbdf596afd52de16df6e50000d6b. Parent metrics remain pending.
Window: 2026-10-05T11:54:17.694Z to 2026-10-05T12:07:55.001923Z.
METRICS: item=InteriorCursorContainment kind=rule commit=b6c8185218aabbdf596afd52de16df6e50000d6b child_min=13.622 parent_min=unavailable tokens_child=5563277 tokens_parent=unavailable gate_wall_s=234.092 gate_jobs=6 instr_closed=0 blocks_closed=0 rules_added=none rules_reused=zesu_integer_array_address_if_enabled,find_mem_region_array residual_classes=medeleg-branch,handoff-witness,side-condition hand_lines=90 rework=repair
