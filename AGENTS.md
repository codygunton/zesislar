# Zesislar proof rules

These rules apply to all proof work in this repository.

## Proof objective

Prove each binary region against its Level 1 contract.
Use the contract boundary that the compliance theorem consumes.
Do not replace a contract proof with an instruction-body theorem.
Do not use execution evidence as a proof premise.

## Proof pattern

Prove machine code with Islaris and Lithium. Start every proof module with
`Require Import ZesuSsz.Automation.All.` Prove blocks with `zesu_block`.
During the frozen-list repair, only class-R baseline modules may replace that
import line with `Require Import ZesuSsz.Automation.AllLegacy.`
The hygiene checker forbids AllLegacy in every new proof module.
Only `Automation/AllLegacy.v` may restore the two measured pre-A1 tactic
overrides during this repair. New hook definitions stay in `Hooks.v`.
State entry and exit resources in `IslarisContractResources` and the
theorem with `IslarisContractCorrect`. State observable output through
`writeOutputEvents` with its payload. Export machine facts only through
`Export/Adequacy.v`.

Do not write an operational lemma per instruction. Do not write a template
generator. Do not transliterate an Iris invariant into an operational one.
Do not write a `//@spec:` for a load or store from an array. Do not split an
array in a proof script. Do not redefine a Lithium hook outside
`ZesuSsz/Automation/Hooks.v`. Do not use a wall-clock deadline (`timeout`, a timed `first` or `try`, a
time-limited solver call) in any tactic a production proof can reach; bound search by steps
or leave it unbounded, and reject symbolic terms before `vm_compute`. Do not use these names: `IslaInstructionSegment`,
`writeSuccessTraceAssumptions`, `zesu_ld_byte_array_at_spec`,
`zesu_lbu_byte_array_at_spec`, `zesu_ld_array_at_spec`,
`solve_zesu_ld_array_at`, `mem_mapsto_array_recombine_u64_read` outside
`Automation/`.

A proof that needs more than five `iRename select` or more than forty lines
per `instr_body` handoff has found a missing rule. Report the residual goal
to the lead and fix the rule in `Automation/`.

Termination is proved separately in Phase 5 of the active plan with the
verified executor in `Export/Executor.v`. Never prove termination by hand
for each instruction.

## File structure

Keep one small umbrella file for each Level 1 contract.
Put endpoint records and machine resources in `ZesuSsz/Contracts/`.
Put Lithium rules and tactics in `ZesuSsz/Automation/`.
Put snapshot and adequacy modules in `ZesuSsz/Export/`.
Put each endpoint proof under its directory in `ZesuSsz/Proofs/`.
Put the writeSuccess proof under `ZesuSsz/Proofs/WriteSuccess/`.
Put the main proof under `ZesuSsz/Proofs/Main/`.
Put compliance statements under `ZesuSsz/Compliance/`.
Put generators and checks under `ZesuSsz/Evidence/`.
Put generated Rocq files under `ZesuSsz/Generated/`.
Put generated trace semantics under `generated/isla-traces/`.

Split large proofs into modules with explicit Iris handoff contracts.
Put each reusable contract, block, branch, loop body, and composition proof
in a suitable module. The umbrella file imports these modules and exposes
the final theorem. Do not duplicate large specifications or shared memory
lemmas across modules. Move shared definitions to `ZesuSsz/Contracts/` only
after two proofs need the same definition.

## Build efficiency

Use all safe parallelism for independent build targets.
Use no more than 48 workers.
Measure one representative task before a large parallel build.
Calculate the worker limit from 70 percent of available memory and the measured peak task memory.
Use the smaller value of that limit and 48.
Use 48 workers when the dependency graph and the memory limit permit 48 workers.

Do not describe the machine as CPU-bound from one process measurement.
Check total CPU use, per-process CPU use, load, available memory, and swap use.
State that a proof is single-thread bound when one process uses one core and the machine remains idle.

Treat a proof module as too large when it takes more than 300 seconds or uses more than 6 GiB.
These limits follow section 6 of the active plan and override the retired 90-second limit.
Treat other modules as too large when they take more than 60 seconds or use more than 2 GiB.
Stop repeated work on that module.
Split it at sound proof-state boundaries before further full compilation.
If no sound split exists, report the exact dependency that prevents parallel work.

Compile independent modules together with Dune.
Keep the final composition proof small and sequential.
Do not expect `-j` to parallelize tactics inside one Rocq proof.
Do not stop a healthy sequential build to test a parallel split.
Run the split build beside the sequential build when memory permits this action.

Use build caches and focused targets during proof development.
Do not rerun an unchanged failed tactic or build.
Inspect the first residual goal before the next attempt.
Use a wait of at least 60 seconds for a silent long build.
Do useful independent work between build checks.
Use bounded output and `rtk` for logs, searches, status checks, tests, and builds.
Do not print generated traces or complete build logs unless the error requires that output.

## Build discipline

Never block a turn on a build. Use your own build directory
`_build/agents/<name>` with `--cache=enabled` and `-j32`. Test one lemma
with `tools/coqc_scratch.sh`, never by compiling a whole module. Run
`make check-fast` before every commit. Module limits are 300 seconds and
6 GiB for proofs. Module limits are 60 seconds and 2 GiB elsewhere.

## Proof workflow

1. Confirm the exact Level 1 entry, exit, outcome, frame, region, and bound.
2. Generate Islaris traces from the pinned binary.
3. Attempt the complete native contract with built-in Islaris automation.
4. Inspect all residual goals before new lemmas or automation.
5. Add only reusable invariants or tactics that the residual goals require.
6. Prove the exact Level 1 state-correctness assumption.
7. Verify the proof with `rocq-mcp` before the complete project gate.

Before a proof exceeds the module limits, define handoff contracts and split the proof.
Build all independent proof modules in one Dune command.
Record elapsed time, peak memory, worker count, and machine utilization at each performance checkpoint.

Stop and ask the user before changing the contract, proof boundary, or proof architecture.
Report instruction counts, branch counts, loops, residual goals, and any manual proof growth.
Treat rapid proof-size growth as an automation defect, not as routine proof work.

## Verification

Use `rocq-mcp` as the primary proof tool.
Call `rocq_health` before proof work.
Use `rocq_start`, `rocq_check`, and `rocq_step_multi` during proof development.
Use `rocq_compile_file` and `rocq_verify` for final proof verification.
Run focused trace and proof targets during development.
Run `make check-fast` before each commit.
Run `make check-iris` before each checkpoint.

## MCP discipline

Use a stable scratch file for interactive MCP sessions.
Keep `_build/default` linked to your private Dune artifacts.
Refresh required artifacts before you start a session.
Do not change a session's file while you use that session.
After an automatic restart, try one fresh file session.
Do not force a restart.

Include health, interactive checks, final compilation, and statement verification in every proof commit report.
The coordinator rejects a proof commit that lacks these results.
Report an exact MCP failure before you switch to a shell proof tool.
The coordinator approves and records each bounded fallback.
Continue independent preparation while the coordinator reviews that failure.
Shell commands can build dependencies and run project gates.

## Integration gates and rule threshold

During the frozen-list repair phase, a track commit needs green `make check-fast`
and a preview that adds no Iris failure before merge.
For a failing numbered class-T hypothesis, run `tools/pin_hypotheses.py`
through rocq-mcp before editing the proof line.
Test each compatible hypothesis with the next tactic, then select the
statement and rename it to a descriptive name.
Log the file, line, old name, and selected statement for every rewrite.
Send a non-unique candidate list to the region owner; leave no numbered
hypothesis in a repaired line.
If a commit touches `ZesuSsz/Automation/`, `InstrSpecs/`,
`ZesuSsz/Contracts/`, or `ZesuSsz/Export/`, the full Iris preview's
failure set must be a subset of the frozen list.
The same criterion applies to repair commits.
After the repair phase, do not merge an ordinary commit while the last full
`make check-iris` gate is red.
Only measured gate-repair commits can enter an isolated recovery preview then.
Run full `make check-iris` in the preview before merging a commit that touches
`ZesuSsz/Automation/`, `InstrSpecs/`, `ZesuSsz/Contracts/`, or `ZesuSsz/Export/`.
Keep the mandatory `make check-fast` check before each commit.
After the repair phase, only a full green Iris gate on Root releases ordinary merges.
During the approved frozen-list repair, a red full preview may proceed only
when its failing set is within the shrinking active list.
Any added failure stops integration and requires a user report.
After the repair phase, two consecutive red full Iris gates stop integration.
Report both failures to the user.

Auto adds a generic rule only when one manual step needs more than five lines
or at least two proof sites need the same step.
Generic rules must not name a machine address, an offset, or a contract predicate.
Otherwise, the region owner writes the manual step in its proof.
For each handwritten contract and proof file, `check_spec_shapes.py` ratchets
uninferable existentials, missing `LithiumUnfold` instances, disjunctive specs,
and frame parameters in closed specs.
