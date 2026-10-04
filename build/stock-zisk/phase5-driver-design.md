# Q11: executable instruction driver

This note proposes generic Phase-5 support. It changes no code, contract, or proof architecture.
The inspected Root revision is `71668237`.

## Current interface

`Export/Executor.v` executes one trace with `exec_instr`.
Its result contains registers, global state, labels, and conditions of type `list Prop`.
Its soundness theorem requires `ExecutorConditions` and returns an existential final local state.
`CompletedInstructionRun` composes completed instructions as a relation.
No executable function currently produces that relation for multiple instructions.

## Proposed API and behavior

Use an executable stop predicate and two natural-number budgets:

```text
exec_run instructionFuel stepFuel stop initialLocal initialGlobal -> RunResult
RunResult = status, finalLocal, finalGlobal, labels, conditions,
            completedInstructions, semanticSteps, remainingBudgets
status = ReachedExit | Exhausted | Trapped | Unsupported
```

The driver accepts only an instruction boundary with `seq_pc_reg = "PC"` and `seq_nb_state = false`.
A proved entry binding must connect its trace to the selected instruction table and PC.
The driver checks `stop` at entry and after each completed instruction.
The driver checks a trapped state before accepting a normal exit.

Factor the existing instruction computation into a helper that retains the local state returned by `exec_finish`.
The helper executes `exec_trace`, then executes `exec_finish` exactly once.
It must preserve the existing `exec_instr` result and soundness claim.
The driver carries the fetched successor trace into the next iteration.
It never reconstructs that trace from a CFG edge.

Carry registers and memory without changing their representation.
Keep `seq_instrs` unchanged throughout the run.
Append labels and conditions in execution order.
Preserve observable write snapshots and instruction-trap labels.
The existing executor rejects reads from unbacked memory.
Runtime services therefore need separate reviewed support.

Consume one instruction unit for each completed segment, including its Done step.
Count actual semantic steps inside the trace and its Done step.
Do not equate instructions, trace events, and semantic steps.
Exhaustion returns the last completed boundary and a completed prefix.
A failed instruction must not commit a partial result as a completed segment.

## Correctness obligations and dependencies

1. Prove helper equivalence, exact successor state, condition preservation, and table preservation.
2. Prove conditional run soundness into `CompletedInstructionRun`, then use `completed_run_nsteps`.
3. Prove instruction and semantic-step bounds for every returned completed prefix.
4. Prove sufficient budgets and valid conditions for every allowed initial contract state.
5. Prove loop measures, callee completion, allocator completion, and all approved exits through reusable summaries.
6. Connect the completed run and physical return to `Export/Adequacy.v`.

`list Prop` conditions are proof obligations, not executable acceptance checks.
The current first-successful branch selection supplies conditional soundness only.
Progress needs valid conditions for the selected branch or a separately proved executable selector.

`Export/DecodeItemTermination.v` requires `seq_nb_state = false` at return.
However, `exec_finish` traps when the return PC has no instruction-table entry.
The driver needs a real caller-trace binding at that PC to satisfy the current return statement.
An invented sentinel trace would change the semantic boundary.

The remaining dependencies are selected-ELF trace bindings, exact physical entry resources, condition discharge, and bounded block summaries.
Runtime termination needs a stated premise or a proof.
A safety premise alone does not prove termination.
Successful computation alone proves neither universal termination nor Level 1 compliance.
