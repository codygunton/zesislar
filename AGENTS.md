# Zesislar proof rules

These rules apply to all proof work in this repository.

## Proof objective

Prove each binary region against its Level 1 contract.
Use the contract boundary that the compliance theorem consumes.
Do not replace a contract proof with an instruction-body theorem.
Do not use execution evidence as a proof premise.

## Required proof pattern

Use Islaris and Iris for machine-state correctness.
State the entry resources, the allowed outcome, and the terminal resources in `IslarisContractResources`.
State the binary theorem with `IslarisContractSpec` and `IslarisContractCorrect`.
Start the proof with `iStartProof` and introduce the code and arguments with `iIntros`.
Use `liAStep` for instruction execution and `liShow` to inspect the remaining state.
Use standard Iris tactics, `bv_solve`, and small arithmetic steps to close the final resource entailment.
Connect the native proof to the Level 1 assumption with `nativeContractBridge`.

The proof must establish the final machine state through terminal `instr_pre` resources.
The proof must preserve all framed registers and memory that the contract requires.
The proof must state the outcome relation that the Level 1 contract requires.

Use a separate checked certificate for termination, region confinement, the exit PC, and the instruction bound.
Generate this certificate from the pinned ELF and its control-flow graph when the region is not small.
Do not weaken the contract to match one observed path.

## Scale requirements

Do not write one lemma for each instruction.
Do not write symbolic-map lemmas, cache lemmas, or a custom operational interpreter.
Do not copy generated instruction semantics into proof files.
Do not hand-write large `instr` conjunctions, PC transition tables, or path lists.
Extend the existing generators when Islaris needs these repetitive artifacts.

Use Islaris proof automation across straight-line blocks.
Use Iris branch reasoning for binary branches.
Supply a loop invariant for each loop.
Do not unroll a large loop to obtain a finite proof.
Keep generated artifacts separate from reviewed contract resources and proof scripts.

Before new automation, inspect `~/islaris` and `~/islaris-tutorial` for an existing idiom.
Prefer an upstream Islaris tactic or extension point over repository-specific proof machinery.
Do not fork Islaris unless the user approves that change.

## File structure

Keep one small umbrella file for each Level 1 contract.
Split large proofs into modules with explicit Iris handoff contracts.
Put each reusable contract, straight-line chunk, branch, loop body, and composition proof in a suitable module.
The umbrella file must import the modules and expose the final theorem.
Do not duplicate large specifications or shared memory lemmas across modules.
Use the structure in `ZesuSsz/Experiments/ZkvmExit.v`, `AllocatorGet.v`, and `WriteFailure.v`.
Move shared definitions to `ZesuSsz/Contracts/` only after two proofs need the same definition.
Put generated trace semantics under `generated/isla-traces/`.
Put generators and their checks under `ZesuSsz/Evidence/` or the applicable build directory.

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

Treat a proof module as too large when it takes more than 90 seconds or uses more than 4 GiB.
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

## Proof workflow

1. Confirm the exact Level 1 entry, exit, outcome, frame, region, and bound.
2. Generate Islaris traces from the pinned binary.
3. Attempt the complete native contract with built-in Islaris automation.
4. Inspect all residual goals before new lemmas or automation.
5. Add only reusable invariants or tactics that the residual goals require.
6. Generate and check the control-flow certificate.
7. Apply `nativeContractBridge` and prove the exact Level 1 assumption.
8. Verify the proof with `rocq-mcp` before the complete project gate.

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
Run `make check` before each proof commit or completion claim.
