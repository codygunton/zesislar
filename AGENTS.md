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
State entry and exit resources in `IslarisContractResources` and the
theorem with `IslarisContractCorrect`. State observable output through
`writeOutputEvents` with its payload. Export machine facts only through
`Export/Adequacy.v`.

Do not write an operational lemma per instruction. Do not write a template
generator. Do not transliterate an Iris invariant into an operational one.
Do not write a `//@spec:` for a load or store from an array. Do not split an
array in a proof script. Do not redefine a Lithium hook outside
`ZesuSsz/Automation/Hooks.v`. Do not use these names: `IslaInstructionSegment`,
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
