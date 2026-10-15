# Phase 2 / Phase 3 launch checklist

This page authorizes no execution.
Orch owns the freeze and the launch release.
Infra C is the named runner for both phases.
`INPUTS.json` retains every pending or unmeasured value as null.

## Before either launch

- [ ] Orch seals `rules_frozen_commit` with the full `cp-av-rules-frozen` commit SHA.
- [ ] Orch records the R3 decision and releases the frozen rule set.
- [ ] Infra C checks HEAD, rule switches, source hashes, imports, artifacts, and the fresh output directory against that freeze.
- [ ] Infra C preserves the first-result identity and arms an exit watcher.
- [ ] Infra C records compiler CPU/RSS separately from admission, setup, and total elapsed time.

## Phase 2: free, 43 blocks

- [ ] Runner: **Infra C**, writer `worker2-c`.
- [ ] Input worktree: `/home/cody/zesislar/.worktrees/worker2-c-free-inputs-06acf`.
- [ ] Inspect the exact prepared [command598](COMMAND598.txt) and its bound report.
- [ ] Keep its preparation Root `06acf88081b14cdf19e09f7ac90d969a67cd3115` distinct from the pending freeze.
- [ ] Do not execute command598 unchanged after a different freeze.
- [ ] Infra C reseals the command and inputs on the released freeze before execution.
- [ ] Run all 43 blocks in first-native designed mode with the source-bound terminal descriptor.
- [ ] Run the approved completion probe for each non-closed block.
- [ ] Fill the existing `free-first-result/CHECKPOINT.json` record once.
- [ ] Retain each exact residual, complete goal groups, compiler measurements, proof evidence, and owned closure.
- [ ] Orch records `cp-av-holdout-free`; later changed-rule runs use separate training records.

The prepared command uses `--designed-successors`, `--first-native-run`, six jobs, and a 300-second discovery budget.
Its 32-GiB/4000-CPU settings are preparation data, not a new policy release.
The final command and output path remain null until Infra C reseals them.

## Phase 3d: nextUint64, call block first

- [ ] Start only after the Phase 2 result is recorded, whether pass or fail.
- [ ] Orch supplies the exact nextUint64 freeze and run identities.
- [ ] Do not inherit them from the free record.
- [ ] Infra B supplies the call-aware design/table and the exact compositional callee premise.
- [ ] Infra C seals a design containing only block `0x800d6274`.
- [ ] Run that block alone under the approved `ZESU_DIAGNOSTIC_PROBE=1` route.
- [ ] Retain `Typeclasses Opaque zesu_call` from `Automation/Calls.v`.
- [ ] Record time to callee `instr_pre 0x800d6960` and the first residual.
- [ ] Preserve return site `0x800d62b8` and the complete compositional exit resources.
- [ ] After the call-block record, run all 10 blocks with the frozen rules.
- [ ] Use `nextuint64-compile-evidence/RESULT.template.json` and `COMPILE.template.json` for the records.
- [ ] Leave the exact input worktree, launch command, call-only design, run identity, and freeze identity null until supplied.
- [ ] Record a needed call rule through Phase 1 comparisons and unit tests; label later call runs as training.

All record paths above are under `build/stock-zisk/automation-validation/`.
No new proof, native run, or alloc-source read occurred.
