# Zesislar proof rules

These rules apply to all proof work in this repository.

## Proof objective

Prove each binary region against its Level 1 contract.
Use the contract boundary that the compliance theorem consumes.
Do not replace a contract proof with an instruction-body theorem.
Do not use execution evidence as a proof premise.

## Contract shape

- State machine bounds on `bv_unsigned` of the register binder.
  Never state them through a `Z_to_bv` cast of a Z quantity. (F44)
- Keep the semantic link to the contract quantity as a separate pure conjunct. (F44)
- Use existential successor binders.
  Never fix a successor binder to a branch literal. (F43)
- Give each entry that fixes a computed quantity a registered introduction keyed by that entry. (F42)
- Define selected code as `instr_lookup_resources (selectedCodeLookup <its own map>)` only.
  Introduce callee code only through the table-level bridge. (F55, F57)
- Do not use Boolean path selectors in join entries. (E3)
- Give each predicate one unfold instance, owned by its function's hint umbrella. (`cp-av-umbrella-closure-audit`)
  Use the umbrella-closure audit and launch preflight as the mechanical checks.

- Put owned resources before pure meaning facts when those resources fix an existential witness in a continuation.
  Keep shared continuations and entries in the same order to prevent continuation-order wands.
- Derive each call specification from its compositional theorem, with the shape `machine_call` requires.

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
generator.
Generators may render declarations (entry statements, registrations, hint umbrellas) from design tables; they never render proof scripts. 'Do not write a template generator' refers to proof templates.
Do not transliterate an Iris invariant into an operational one.
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

Ordinary hint modules must remain globally exported through their function's hint umbrella.
Selected proofs may import scoped hints directly only through the explicit `SCOPED_HINT_IMPORTS` policy in `check_decode_item_hints.py`.

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

Measure timing and report it. A timing regression becomes an optimization item. Never reject a correct change for its performance.

Use all safe parallelism for independent build targets.
Use no more than 48 workers.
Measure one representative task before a large parallel build.
Calculate the worker limit from 70 percent of available memory and the measured peak task memory.
Use the smaller value of that limit and 48.
Use 48 workers when the dependency graph and the memory limit permit 48 workers.

Do not describe the machine as CPU-bound from one process measurement.
Check total CPU use, per-process CPU use, load, available memory, and swap use.
State that a proof is single-thread bound when one process uses one core and the machine remains idle.

The 300-second and 6 GiB figures are production goals for a finished proof module, not limits
on search. During development, first bound the problem: run a search or a proof to completion
with whatever memory and time it needs (the machine has 256 GiB; a 64 GiB cap and no CPU cap are
normal for a probe), record its peak memory, CPU, and residual goals, and optimize afterwards
from that measurement. A run that stops at a cap mid-search has measured nothing. Record each
raised cap on issue #10 as a probe. The guard defaults are 2400 CPU seconds and 16 GiB per gate module,
raised 2026-10-20 for native decodeItem proofs, issue #10.
These gate defaults do not apply to diagnostics. Never split a basic block, cut a proof, or weaken a
contract to fit a cap; bring a finished proof under the production goal by optimizing the rule
cost, as the Prologue went from 435 to 218 seconds.
Treat a non-proof module as over its production goal when it takes more than 60 seconds or uses
more than 2 GiB; measure it to completion first, then split it at sound proof-state boundaries.
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

Remove Lia, Nia, and Csdp caches from the compiler's actual working directory before each timing sample.
Decide cost changes from user-space instructions with identical compiler flags and measurement settings.

## Build discipline

Never block a turn on a build. Use your own build directory
`_build/agents/<name>` with `--cache=enabled` and `-j32`. Test one lemma
with `tools/coqc_scratch.sh`, never by compiling a whole module. Run
`make check-fast` before every pull request and merge; before an ordinary
commit on a work branch, run the focused targets that the change affects.
Correctness gates take no exclusive machine lock; only timing measurements
do. Production goals are 300 seconds and
6 GiB for proof modules, 60 seconds and 2 GiB elsewhere; they are goals for
finished modules, not caps on search.

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
Run `make check-fast` before each pull request and merge.
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

## Coordinator duties

These apply to the coordinating session only.

The coordinator is responsible for the workers never being blocked on it. Every dispatch names
the next items the worker takes when the current item ends, stalls, or needs a ruling, so a
pending ruling never empties a queue; those fallbacks are Phase 1 work, never later-phase work.
Before dispatching, anticipate the forks in the road (a comparison that shows no effect, a gate
that fails, a limit that stops an arm, a capture that lacks the expected stage, a root that
changes, a premise that turns out missing) and state in the dispatch how the worker proceeds on
each branch. A question that reaches the coordinator is a planning defect to fix in the next
dispatch, not only a question to answer. Rulings reserved for the user (contract, proof
boundary, architecture) are stated as such with the fallback the worker executes meanwhile.
Check for idle workers at every turn and refill queues before anything else.

Liveness is measured, not reported. At every turn, and on a timer when no mail arrives, the
coordinator checks the process list and the job logs: a child counts as working only when a
proof command (a native arm, an oracle replay, a scratch lemma, a module compile) started within
the last 30 minutes; a parent's "watched", "waits on", "prepares", or "queue nonempty" is not
evidence of work. The throughput that matters is proof commands started per child-hour; the
coordinator records it in `docs/ai/STATUS.md` each round and treats a round with none as an
incident. Waiting is not a state: a child blocked more than 15 minutes on a lock, gate, barrier,
verifier route, or another worker starts its next item and leaves the wait in the background.
Ceremony is capped: one certificate or audit per result, no audit of an audit, no preparation
item longer than 20 minutes without a proof command. A child idle at two consecutive checks gets
its item re-dispatched with the exact first command. Probes run in the background and occupy no
child. The coordinator never ends a turn with "nothing owed" while a child is idle.

## Integration gates and rule threshold

Land each release as a pull request that references its plan's tracking issue. The coordinator merges it after both gates pass.

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
Keep the mandatory `make check-fast` check before each pull request and merge.
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
