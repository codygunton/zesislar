# Termination: step budgets through the Islaris fork

Design note for Stage T of `docs/AGENT_ASSISTED_RLP_PLAN.md` (issue #347). The plan holds the tasks; this note holds the reasons.

## What was missing

Every theorem before Stage T is partial correctness: a proved function never faults and meets its contract if it returns, but may run forever. Islaris uses Iris's partial weakest precondition; `isla_adequacy` and `zesu_adequacy` state safety of a finite run.

ZisK caps a run at 2^36 steps (`MAX_NUM_STEPS`, `executor/src/executor.rs`). On the proving path a run cut off at the cap yields no proof: the Rust path panics, the assembly path returns an error because the end flag is never set. This is a source read of `/home/cody/zisk`; the verifier side is not in that checkout. So a missing termination proof costs liveness, not soundness.

## Findings that fixed the design

- Iris's step index cannot give an upper bound on steps: `state_interp_mono` lets it grow without a step. The count must be in the machine state.
- Islaris starts an instruction at one place only: the `LDone` branch of `SeqStep` in `theories/opsem.v`. Counting there counts instructions, the unit ZisK also counts.
- This repository reaches the fetch through one rule, `li_wp_next_instr`, and names code only through `instr` facts. So the charge can attach to the address: an `instr` fact means "uncharged", a new `instr_charged` fact means "each fetch costs one credit".
- A design with two proof modes (bounded and unbounded logic) would have made the frozen `ZesuSsz/Automation/` lemmas unusable in bounded proofs. Charging per address has one logic; all existing statements and proofs stay valid.

## The mechanism

- Machine state: `seq_charged`, a fixed set of addresses, and `seq_fetches`, the number of fetches of instructions at those addresses.
- Ghost state: `step_credits n`; the state interpretation holds `credits outstanding + seq_fetches = total`.
- Rules: the existing fetch rule, unchanged, for `instr`; `wp_next_instr_charged`, which consumes `step_credits 1`, for `instr_charged`. A block's precondition pays for the block's first instruction; a jump to a block specification pays nothing.
- Adequacy: `isla_budget_adequacy` concludes safety and `seq_fetches ≤ budget`. `fetches_bound_steps` turns a fetch bound into a step bound when all code is charged: the steps inside one instruction are at most the length of its Isla trace.
- In this repository: `step_budget z` over `Z`; a loop-free function's budget is the instruction count of its longest path plus its callees' budgets, computed by `tools/block/budgets.py`; a loop cut owns a potential given by one annotation row.

## Limits

- A charged function that calls an uncharged one has a bound on its own instructions only.
- Budgets of the allocator entries and `memcpy` are assumed, as their correctness is.
- A function may have an uncharged and a charged theorem; a composition uses one kind for all its callees.
