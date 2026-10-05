The switched hook now exposes only local aliases needed for its mask shape.
The hook selects the unsigned left operand and its masked addition operand.
The hook unfolds those definitions in the goal. It does not unfold hypotheses or other definitions.
The switch remains unchanged. The rule names no PC, function, or contract.

The new regression preserves the audit's LET0 and LET2 definitions.
The frozen arms use the identical aliased statement. The off solver fails. The on solver closes without manual unfolding.
All ten regression statements compile.
Fresh owned MCP checks both arms and the regression module after root9b3214f6.
MCP health, start, check, step_multi, compile_file, and verify pass. Final verification reports assumptions [].
The peak owned MCP scope uses 1275523072 bytes.

The final root gate passes in 179.313 seconds with six workers.
The earlier gate passes in 149.580 seconds before the root announcement.
Both gates use 328.893 seconds total. The final gate records 2232828 KiB peak child RSS.
I merged the announced root after the healthy earlier gate finished. I did not run check-iris.
This checkpoint closes no machine instruction or block. The contract remains unchanged.

Evidence: evidence.json; SHA-256 0bd4e176762390131a1011be34b40c6e0a557e48a2d1f7a04fee85af722daf44.
Window: 2026-10-05T06:56:00.422000+00:00 through 2026-10-05T07:06:54.360460+00:00.
The parent did not supply its metrics. The report binds the pre-commit base; the checkpoint supplies the review commit.
METRICS: item=Q56-low-mask-alias kind=rule commit=d00a9f90d9d0fc5298b4f370cee7e53f76dfd521 child_min=10.899 parent_min=unavailable tokens_child=2572824 tokens_parent=unavailable gate_wall_s=328.893 gate_jobs=6 instr_closed=0 blocks_closed=0 rules_added=none rules_reused=zesu_low_mask_if_enabled,zesu_unsigned_low_mask_add_integer residual_classes=none hand_lines=0 rework=repair
