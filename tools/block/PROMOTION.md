# Native promotion

Use the named production theorem after its native closure passes review.
The production source must exist in the selected workspace.
The conditional adapter supplies the exact table boundary.

Run the command under the pinned opam environment:

```sh
opam exec --switch=/path/to/pinned/switch -- python3 tools/block/promote_table.py \
  --complete-native 0x800d6974 \
  --production-module ZesuSsz.Proofs.DecodeItem.Auto.Block800d6974 \
  --production-lemma ZesuSsz.Proofs.DecodeItem.Auto.Block800d6974.DesignedBoundary_800d6974 \
  --native-status-table /path/to/i67-e17-default-results.json \
  --output build/stock-zisk/native-promotion-6974.json
```

The command updates these files:

1. The slot adapter applies the named production theorem.
2. `PromotedBodies.v` exports the exact table slot.
3. The promoted signature fixture checks that slot.
4. The conditional compliance theorem removes only this native hypothesis.
5. The compliance fixtures check the remaining hypothesis family.
6. The native record removes only this field and updates its count.
7. The native record fixtures check the remaining fields.

The output report binds every source and the regenerated native status.
Historical I67 counts retain their measurement root and unavailable-group limits.
The command restores source files if status validation fails.

The command performs Rocq compilation and exact statement verification.
The report records the actual results.
The command does not turn an execution capture into a proof premise.
The native theorem retains its successor continuations and selected code.

The historical regression starts at `cp-p1-i60`.
It compares the adapter, promoted bodies, and slot fixture with `cp-p1-s50`.
It compares the compliance theorem and fixtures with `cp-p1-s53`.

The command now verifies the emitted sources before it reports success.
It calls `rocq_compile_file` for every changed module and regenerated fixture.
It calls `rocq_verify` for their exact statements and requires assumptions `[]`.
It retains each raw response and the owned transport identities.
The compiler retains private objects for subsequent module imports.

Use `--mcp-python` when the shell Python lacks the pinned MCP package.
Use `--verification-directory` to select a fresh evidence directory.
The existing guarded compiler controls admission.
Close other owned proof sessions before you run the command.

Use `--dry-run` to emit sources for review without verification.
The dry-run report sets `success` to `false` and `status` to `dry_run`.
A failed verification restores the previous source files and records the failure.
A successful report sets `success` to `true` and `status` to `verified`.
The final project gate remains required before a commit.

## Hand gate preparation

Complete MCP compilation and exact verification before this gate.
The gate launcher does not verify a native proof.
Record the measured size with explicit `--record-size` after the dispatched Hand size review.
The command rejects proofs above 80 physical lines from `Proof` through `Qed`.
It preserves the other baseline entries.
It removes session writer and probe settings from the gate environment.
Hand sessions still require their writer identity.

```sh
ai-coord watch --label hand-698c-check-fast -- python3 tools/block/prepare_hand_gate.py \
  --module ZesuSsz/Proofs/DecodeItem/Hand/Block800d698c.v \
  --agent spec-a --jobs 6 --record-size --check-fast
```
