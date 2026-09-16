# Push 3 exec progress

## Remaining work

Phase 5.1 needs the executor and its soundness theorem.
Phase 5.2 needs the decidable trace condition and determinism theorem.
The 45 pilot tests remain open.
Phase 5.3 starts after CP3.

## Plan deviations

- The completion relation uses `CompletedInstructionSegment`.
  The repository forbids the legacy relation name.
  The orchestrator approved this name on 2026-09-14.
- The fixed `exec_instr` signature omits the PC register name.
  The executor uses `"PC"`, as the pinned RISC-V model requires.
  The orchestrator approved this choice on 2026-09-14.
- New worktrees contain no ignored trace inputs.
  I copied unchanged traces from the integration worktree.
- The first MCP preamble session failed with `No node at point`.
  A project session with a local scratch file works.

## Checked work

The instruction prefix and completion relations use unchanged `seq_step`.
The completion theorem exports an Iris `nsteps` execution.
Scratch checks close prefix composition and completion lemmas.
The declaration rules close under the global context.
The witness selector reads register fields and memory.

## Phase 5.3 boundary

The user excludes the decoder region from all proof work.
The termination theorem will take the named hypothesis `decodeTerminates`.
That hypothesis connects decoder entry resources to decoder exit resources.
Phase 5.3 proves control termination for main and the five proved endpoints.
I will not generate or reason about decoder traces.

## Build checkpoint

The focused `Executor.vo` target passed in 5,813 ms.
Its peak RSS was 672,092 KiB.
The initial fast gate failed after 512,421 ms.
I stopped its unchanged `WriteSuccessHashesLoop.v` compiler after 308 seconds.
That compiler used 3,858,420 KiB RSS.
The reviewed hash-loop split must land before another fast gate.
I did not commit while the fast gate failed.

## Phase 5.2 clarification

The no-MMIO check depends on the boundary memory map.
The condition therefore takes the trace, registers, and global state.
It retains a trace check for symbolic pinning where useful.
The orchestrator approved this clarification on 2026-09-14.
The determinism conclusion stays unchanged.
No execution relation enters this condition.

## Phase 5.1 soundness

`exec_instr_sound` proves a completed instruction segment against unchanged `seq_step`.
Its conditions contain only register, memory, width, and arithmetic facts.
The focused target passed in 6,873 ms with 696,876 KiB peak RSS.
The reviewed hash-loop split landed at integration commit `5ce975c4`.
I rebased onto that commit.
The assigned fast gate passed in 1,817 ms with 660,104 KiB peak RSS.
The focused pilot target passed in 14,767 ms with 797,620 KiB peak RSS.
All 45 pilot checks and five memory/output checks closed.
Each pilot used `vm_compute` and `bv_solve`.
The longest measured `vm_compute` call took 0.001 seconds.
Phase 5.2 contains closed event-determinism and backed-memory reflection lemmas.
The complete pinning condition and segment-determinism theorem remain open.

## Phase 5.2 branch refinement

The original branch search accepted false register and memory conditions.
The orchestrator approved guards that reject these false conditions.
The executor retains its returned pure conditions and unchanged `seq_step` soundness.
The new regression puts an infeasible constant read before a feasible branch.
The regression closes by `vm_compute` and `bv_solve`.

The first guard used proof-producing equality and set decisions.
The first complete pilot attempt exceeded 6 GiB and stopped.
The Boolean equality replacement fixed the register pilot.
The MMIO store still exceeded 6 GiB because its set decision produced proof terms.
I stopped that representative at 9,841,064 KiB RSS.
I replaced the set decision with `forallb` over `map_to_list` and Boolean address comparisons.
The representative MMIO store then passed in 644 ms with 632,384 KiB peak RSS.
The compact guard target passed in 8,259 ms with 719,136 KiB peak RSS.
The complete 51-check pilot target passed in 13,922 ms with 808,052 KiB peak RSS.
Every comparison has a closed Boolean reflection lemma.
MCP verified the refined `exec_instr_sound` with no assumptions.

The planned pinning condition also checks branch exclusivity.
It checks pinned or unused declarations, backed reads, event guards, and at most one feasible branch.
The orchestrator approved this clarification.
Its complete reflection and segment determinism theorem remain open.

Commit `6e50cb6` contains the branch guards and counterexample.
A rebase onto `a5637e48` changed its SHA to `008f628b`.
The assigned fast gate passed in 227,054 ms with 2,705,620 KiB peak RSS.
The final pilot/counterexample target passed in 12,863 ms with 831,684 KiB peak RSS.
The final determinism statement waits for the user ruling on branch exclusivity.

## Unused-variable block

The base, value, expression, event, and trace checks have exact Boolean/Prop reflection.
Each check also proves substitution identity for every replacement value.
The scratch block passed in 1,252 ms with 614,100 KiB peak RSS.
MCP compiled the block and verified `trace_unused_substitution` with no assumptions.
The pilot regression distinguishes unused mstatus variable 2 from used PC variable 3.

Commit `3e2b903` contains the unused-variable block and two pilot checks.
Its assigned fast gate passed in 161,648 ms with 2,706,600 KiB peak RSS.
Its focused target passed in 17,644 ms with 829,812 KiB peak RSS.

## Positional read pinning

The original structured search could select an earlier duplicate field.
The orchestrator approved positional matching with equal field names.
`read_symbol_substitution` proves that the selected witness equals the replacement value.
`read_symbol_pins` consumes substitution equality and proves the same witness fact.
`read_accessor_substitution` proves that accessor reads commute with substitution.
The duplicate-field and different-name regressions close.
MCP compiled the read-symbol block and verified `read_symbol_pins` with no assumptions.
MCP also verified the changed executor soundness with no assumptions.

Commit `416c351` contains positional read pinning.
Its assigned fast gate passed in 525 ms with 134,888 KiB peak RSS.
Its focused target passed in 22,912 ms with 832,164 KiB peak RSS.

Commit `64e290b` contains concrete-pin substitution preservation.
A rebase onto `1d91f274` changed its SHA to `5de36aeb`.
Its assigned fast gate passed in 517 ms with 134,728 KiB peak RSS.
Its focused target passed in 15,266 ms with 832,316 KiB peak RSS.

## Pending register pins

`RegisterReadPin` locates a future register read before writes.
Its resource facts contain only register lookup, accessor, and symbolic value facts.
Substitution preserves a concrete pending pin.
Each sequential step either consumes the pin or preserves it.
Every completed prefix reaching `tnil` consumes the pin and fixes its value.
`register_read_pin_completed` lifts this fact to completed instruction segments.
MCP compiled the complete block and verified that theorem with no assumptions.
The scratch block passed in 2,753 ms with 660,644 KiB peak RSS.
The fixture crosses another declaration before the selected register read.
No execution relation enters the pending-pin predicate.

- Register-pin checkpoint remains uncommitted. Its assigned fast gate failed in `Proofs/WriteFailure/WriteFailure.v:61`: `write_failure_state_correct` was incomplete. The gate exited 1 after 219830 ms and used 2706048 KiB. Root received the exact shared dependency. No unchanged gate was repeated.
- Independent trace-length lemmas close: substitution preserves length; every nonterminal `trace_step` decreases length. Scratch exited 0 after 751 ms and used 636760 KiB. All printed assumptions are closed.
- Independent memory-pin propagation and its future-read mismatch regression close. Scratch exited 0 after 2503 ms and used 648780 KiB.
- Independent register-pin scanner returns a pure future-read witness. Its soundness, groundness, and completed-run forcing lemmas close. Scratch exited 0 after 751 ms and used 640800 KiB. The scanner has no execution premise.
- The generic instruction-prefix length bound closes. Scratch exited 0 after 1503 ms and used 647220 KiB. These independent blocks remain in ignored scratch files until the register-pin checkpoint commits.
- Register scanner Boolean/Prop reflection closes exactly. Scratch exited 0 after 1002 ms and used 640708 KiB. The pure Prop records register lookup, accessors, symbolic self-match, concrete witness, and groundness.
- Future backed-memory scanner soundness and completed-run forcing close. Scratch exited 0 after 2503 ms and used 659644 KiB. The address conversion lemma closes without arithmetic workarounds.
- Root stopped for the section 5.5 branch-exclusivity and pinned-heap rulings. Final Phase 5.2 remains held. The pending register-pin checkpoint also needs the shared WriteFailure dependency fixed before its assigned gate can pass. No new commit claims completion.

## Ruling 1 bounded review

I read the complete dispatch `DISPATCH_PUSH3_RULINGS_PORT_2026-09-14.md`.
The approved condition permits at most one feasible branch.
I will keep `exec_instr_sound` unchanged.

The reusable checker accepts these branch lists:

- The list contains zero or one branch.
- The list contains two branches with leading assertions `e` and `Unop Not e`.
- Both branches use the same expression `e`.

The checker applies recursively to every `tcases` node.
It accepts either assertion order.
It compares the expression structure and ignores only annotations if necessary.
Substitution preserves the complementary structure.
A completed branch must pass its leading assertion.
The complementary branch cannot pass from the same state.
The pure condition contains no execution relation.

The final combined Boolean checks pinning, backed reads, feasible event guards, and branch exclusivity.
Its Prop reflection will describe those exact checks.
The proposed final statement keeps the executor equality conclusion:

```coq
Theorem exec_instr_deterministic trace regs sigma labels theta' sigma' :
  executor_deterministicb trace regs sigma = true ->
  CompletedInstructionSegment
    (instruction_boundary trace regs) sigma labels theta' sigma' ->
  exists conditions,
    exec_instr trace regs sigma =
      Some (seq_regs theta', sigma', labels, conditions) /\
    ExecutorConditions conditions.
```

A bounded syntactic scan inspected the current integration artifacts.
It found 2481 `tcases` occurrences across 1337 unique instruction PCs.
Every occurrence has the complementary leading-assertion structure.
The candidate fallback count is zero instructions.
This count is preliminary because Root will regenerate matching traces.
The final report must count the regenerated artifacts in the proved scope.

The previous WriteFailure gate used stale ignored artifacts.
I will apply no proof workaround.
Root will supply matching traces and concrete decoder predicates.
I ran no heavy build during this review.
I stopped after the review so Root can schedule Main.

## Approved exclusivity implementation

I added the recursive syntactic checker to `Export/Determinism.v`.
The checker accepts zero or one branch.
The checker accepts two complementary leading assertions in either order.
The checker compares the complete expression structure with compact base-value comparisons.
Every annotation has the single constructor `Mk_annot`.
The Boolean/Prop reflection is exact.
Substitution preserves the complementary assertions and recursive condition.
The executor soundness code remains unchanged.

Three regressions close:

- Reversed complementary guards with nested negation are accepted.
- Two identical guards are rejected.
- Nested feasible alternatives without guards are rejected.

Scratch exited 0 after 1502 ms and used 656584 KiB.
MCP `rocq_start`, `rocq_check`, and `rocq_step_multi` proved the reflection.
MCP final compilation passed.
MCP `rocq_verify` returned `assumptions: []` for `trace_exclusive_reflect`.
Every added lemma prints `Closed under the global context`.
MCP final compilation placed its standalone artifact under `_build/default` because the tool lacks a build-directory argument.
The pending register-pin block and new checker remain uncommitted as Root instructed.
The final gate waits for the published machine map and matching traces.
The preliminary fallback count remains zero instructions.

## Abstract semantic exclusivity checkpoint

A completed branch passes its leading assertion.
The expression and its negation cannot both pass from the same state.
`branches_exclusive_completed_unique` proves that two completed branches from an accepted list have the same trace.
The result compares branch identities before any successor proof.
No per-instruction fallback proof was needed.

The complete abstract scratch exited 0 after 3505 ms and used 720064 KiB.
MCP final compilation passed.
MCP verification returned `assumptions: []` for `branches_exclusive_completed_unique`.
That verification used the direct-compilation fallback.
Every added semantic lemma prints `Closed under the global context`.
The semantic lemmas are in `Export/Determinism.v`.
The final gate and commit remain pending for Root's map publication.

### Abstract composition foundation

The generic step, completion, register scan, and memory scan lemmas compile together.
The focused Dune check exited 0 after 12301 ms and used 910720 KiB.
The declaration condition has an exact Boolean reflection theorem.
Its complete scratch exited 0 after 2503 ms and used 663896 KiB.
The branch guard lemmas compare a successful executor branch with a completed formal branch.
Their complete scratch exited 0 after 1753 ms and used 675696 KiB.
The final Done step yields the exact executor finish result and true conditions.
Its complete scratch exited 0 after 1502 ms and used 636440 KiB.
Every checked lemma prints `Closed under the global context`.
These blocks preserve the unchanged `seq_step` relation.
The final gate and commit remain pending for Root's map publication.

### Phase 5.2 abstract theorem complete; final gate pending

`exec_instr_deterministic` proves the approved Ruling 1 statement.
The theorem returns the exact completed result and true `ExecutorConditions`.
The Boolean condition has an exact Prop reflection theorem.
The condition contains no execution evidence.
The proof uses unchanged `seq_step` soundness.
The recursive syntactic check accepts zero branches, one branch, or complementary leading assertions.
No per-instruction proof occurs in the abstract composition.
The complete focused scratch exited 0 after 1502 ms and used 666776 KiB.
The focused Dune target `determinism-complete` exited 0 after 16305 ms and used 987924 KiB.
MCP final compilation passed.
MCP verification returned `assumptions: []` through its direct fallback.
`Print Assumptions exec_instr_deterministic` prints `Closed under the global context`.
MCP stores scratch artifacts in `_build/default` because its API has no build-directory argument.
Root holds the final gate and commit until the shared map and matching traces are published.
The regenerated proved-scope fallback count also waits for that publication.

### Pure termination resource draft

The ignored `TerminationResourcesScratch.v` defines physical register and memory checks.
The caller frame includes input slots, allocator slots, padding, and the saved return address.
The saved-register list uses the twelve agreed callee-saved registers.
The trace residual records the specification after a label prefix.
The append theorem composes trace residuals without execution premises.
The complete focused scratch exited 0 after 752 ms and used 615740 KiB.
Both helper lemmas print `Closed under the global context`.
Root received the proposed shared destination `Export/TerminationResources.v`.
The concrete physical decoder factory remains Root-owned.
The draft contains no decoder trace or proof.

### Pinning regressions

A compact fixture pins a Boolean declaration through a register read.
The fixture uses complementary branch assertions and selects PC 4.
The complete Boolean condition accepts the fixture.
The condition rejects the same fixture when the pinning register is absent.
All three regression lemmas print `Closed under the global context`.
Their focused scratch exited 0 after 1251 ms and used 639316 KiB.
The regressions are in `Proofs/Tests/Executor.v`.
Root approved the pure physical helpers for `Export/TerminationResources.v`.
Root will apply that shared module after the map gate.

### Final Phase 5.2 gate on the unified map

The exec branch rebased onto 3bfd25c1.
The worktree copied the unchanged unified trace mirror from integration.
The scoped inventory contains 133 regions and 1,023 trace instances.
The inventory contains 998 distinct instruction PCs and 20 tcases nodes.
The inventory contains no decoder instruction.
The final Boolean audit covers every instance and awaits stable compiled dependencies.
All 45 pilot proofs now time the complete vm_compute and bv_solve sequence.
The first scratch audits reached missing or changing dependencies during the gate.
The next scratch attempts wait until the gate completes.
The gate uses CHECK_AGENT=exec, AGENT_JOBS=16, and the shared cache.
Root found a multiline tuple gap in the port word guard.
The port correction follows this exec gate.
The existing pilot vo artifact predates this gate.
The final focused pilot compile must refresh it.

The complete scoped Boolean audit passes for all 1,023 instances.
The audit uses 133 regions with 998 distinct PCs and 20 tcases nodes.
The exclusivity fallback count is zero.
The scoped audit exits 0 after 3,256 ms at 1,060,016 KiB peak RSS.
The audit uses unique names for the 25 duplicated PCs.
The focused trace and pilot build exits 0 after 15,439 ms at 858,312 KiB peak RSS.
The full pilot scratch exits 0 after 14,516 ms at 856,444 KiB peak RSS.
All 45 pilot lemmas print Closed under the global context.
Each pilot proof uses vm_compute and bv_solve.
The slowest complete pilot proof takes 0.006 seconds.
The total time for the 45 pilot proofs is 0.051 seconds.
The fixture contains 66 Closed assumption reports.
The complete Determinism.v MCP compilation passes with 1,552 sentences.
The complete Executor.v test MCP compilation passes with 452 sentences.
MCP verifies the exact exported determinism statement with assumptions [].
Print Assumptions exec_instr_deterministic prints Closed under the global context.
Print Assumptions executor_deterministic_reflect prints Closed under the global context.

MCP ignores the nested Coq project during compilation.
The worker preserves the earlier _build/default directory inside the assigned build directory.
The worker links _build/default to _build/agents/exec/default for MCP path resolution.
This reversible setup keeps MCP artifacts in the assigned build directory.
No shared file changes.

The full fast gate exits 0 after 353,060 ms at 2,593,784 KiB peak RSS.
The outer gate record reports 374,118 ms with the same peak RSS.
Phase 5.3 still waits for CP3.
The decoder remains outside the proved scope.
The final composition will use the named decodeTerminates hypothesis.

Final Phase 5.2 commit: d83157e8e52ee664e7881f9b38c0615e9347bad5.
The final cached check-fast exits 0 after 524 ms at 138,220 KiB peak RSS.
The outer record reports 1,932 ms at 602,656 KiB peak RSS.
The exec worktree is clean.

The exported reflection statement is:
```coq
executor_deterministicb trace regs sigma = true <->
ExecutorDeterministic trace regs sigma.
```
The exported determinism statement is:
```coq
executor_deterministicb trace regs sigma = true ->
CompletedInstructionSegment (instruction_boundary trace regs) sigma labels theta' sigma' ->
exists conditions,
  exec_instr trace regs sigma = Some (seq_regs theta', sigma', labels, conditions) /\
  ExecutorConditions conditions.
```
The checker accepts zero branches or one branch.
For two branches, it requires complementary leading assertions on the same expression.
The checker accepts either assertion order and checks nested branches recursively.
The unchanged seq_step semantics supplies the completed segment.
The theorem introduces no trace replacement or execution premise into a contract.
All 20 branch instructions pass the syntactic checker.
The fallback count is zero.

## Physical decoder termination request (2026-09-14)

Root approved the prefix-indexed physical entry and exit shape.
The draft lives in the ignored exec scratch directory: `PhysicalDecodePredicatesRequest.v`.
The draft pins an explicit instruction table and preserves `traceResidual` exactly.
Root approved pairwise footprint separation to match the existing Iris resources.
The entry uses the complete 2976-byte caller window, heap, input, allocator metadata, and static memory.
The success exit separates dynamic object data from the preserved caller and input resources.
The failure exit preserves the heap footprint and nonzero two-byte status.
The draft derives new fixed addresses from `defaultMap` and `machinePc`.
The draft declares no axiom and imports no Main proof module.
Root will choose the pinned program and declare the named global `decodeTerminates` assumption.
Scoped code agreement remains separate and excludes decoder traces.
The focused dependency build runs before the final scratch audit.
Phase 5.3 final composition still waits for CP3.

The physical predicate scratch audit passes on integration `cc1e6d87`.
Command: `tools/coqc_scratch.sh _build/agents/exec/PhysicalDecodePredicatesRequest.v _build/agents/exec`.
Result: exit 0; 1.751 seconds; 1101600 KiB peak RSS.
MCP `rocq_compile_file` also passes in full mode.
`physicalMainDecodeEntry`, `physicalMainDecodeExit`, and `decodeTerminationHypothesis` each print `Closed under the global context`.
The request defines `decodeTerminationHypothesis program` without declaring an axiom.
The future global `decodeTerminates` assumption must use the chosen fixed program, not quantify over arbitrary programs.
Root received the exact scratch path and owns shared implementation.
The exec source tree remains clean.

## Phase 5.3 generic composition checkpoint

Commit: `98a28b24` — compose completed executor instruction runs.
The commit adds `CompletedInstructionRun` and three closed composition lemmas to `Export/Executor.v`.
`executor_nsteps_append` adds step counts and appends labels over unchanged `nsteps`.
`completed_run_append` adds instruction counts and appends completed runs.
`completed_run_nsteps` turns every completed run into a finite unchanged machine run.
All three lemmas print `Closed under the global context`.
MCP compiles the complete executor and verifies the exact run theorem with no assumptions.
Generic scratch: exit 0; 1.252 seconds; 641832 KiB peak RSS.
Fast gate: `make check-fast CHECK_AGENT=exec AGENT_JOBS=16`; exit 0; 22.467 seconds; 1148012 KiB peak RSS.
Gate wrapper: 25.546 seconds; 1148012 KiB peak RSS.
The exact shared request is `_build/agents/exec/CompletedRunThroughDecoderRequest.v` in the exec worktree.
Its scratch audit uses the reviewed local physical predicates and the committed executor run relation.
`completed_run_through_decoder` composes caller completion, explicit physical decoder termination, and continuation completion.
The theorem preserves the exact emitted prefix and prints `Closed under the global context`.
Final composition scratch: exit 0; 2.002 seconds; 1114364 KiB peak RSS.
MCP compiles that scratch in full mode.
No named global decoder assumption exists in this worker commit.
Root must fix the explicit program before it publishes that assumption.
The final `zesuTerminates` theorem still waits for CP3.

## Approved Phase 5.3 decoder-boundary deviation (2026-09-15)

**Before.** `decodeTerminationHypothesis program := ∀ decodeTail successExitTail initial prefix args theta sigma, physicalMainDecodeEntry program ... theta sigma → ∃ steps labels theta' sigma' outcome, nsteps steps ([theta], sigma) labels ([theta'], sigma') ∧ physicalMainDecodeExit program ... (prefix ++ labels) ... theta' sigma'`. `physicalMainDecodeEntry` required `seq_instrs sigma = program ∧ physicalInstructionBoundary (machinePc 0x2048) theta sigma`, including a decoder lookup.

**After.** `decodeTerminationHypothesis approvedProgram := ∀ program, approvedProgram ⊆ program → ∀ decodeTail successExitTail initial prefix args theta sigma, physicalMainDecodeEntry program ... theta sigma → ∃ steps labels theta' sigma' outcome, nsteps steps ([theta], sigma) labels ([theta'], sigma') ∧ physicalMainDecodeExit program ... (prefix ++ labels) ... theta' sigma'`. The entry now requires `seq_instrs sigma = program ∧ physicalDecoderEntryBoundary (machinePc 0x2048) theta`. This boundary retains `seq_pc_reg theta = "PC"`, `seq_nb_state theta = false`, and the fixed PC register. All remaining resources are unchanged.

**Reason.** The approved 998-address program intentionally omits decoder instructions. Decoder termination must run under an extending map without requiring a lookup from the approved map.

**Equivalence note.** Any former entry implies the new entry by dropping only its lookup conjunct. The exit predicate remains `physicalMainDecodeExit`. `main_to_decode_entry_state_correct` is unchanged. `zesuCompliance` is unchanged. The Phase 5 composition lemmas carry the named `decodeTerminates` and the map inclusion premise. CP5 must review this deviation.

Exec commit `7e75743a` implements this statement. MCP compiled `DecodeTermination.v`, `Termination.v`, and `DecoderComposition.v`. MCP verified `zesu_run_through_decode_termination` with assumptions `[]`. Every affected `Print Assumptions` line is `Closed under the global context`. Exec `check-fast` passed. A full `check-iris` preview is required before merge because this commit changes `Export/`.

## B4 Encoder.optionalU64 closed-call deviation (2026-09-16)

**Before.** The only closed helper was `zesuEncoderOptionalU64ExactPayloadCallSpec := zesuEncoderOptionalU64ExactSomeCallSpec ∨ zesuEncoderOptionalU64ExactNoneCallSpec`. Its branch specs hid the return through `zesu_c_call`. The framed lemmas required explicit caller parameters.

**After.** `zesuEncoderOptionalU64ExactCallSpec` existentially binds `pointer`, `sp`, `ret`, saved registers, `tag`, `bytes`, `tail`, and `outcome : option (bv 64)`. Exact resources fix these values by unification. The spec exposes the branch-specific events through `spec_trace` and ends in `instr_pre (bv_unsigned ret) (encoderOptionalU64ExactReturn pointer sp ret old_x8 bytes tail outcome) ∗ True`. `zesu_encoder_optional_u64_exact_call_correct` and `_pre` provide the closed body and persistent call spec.

**Reason.** B4 needs a closed helper that Lithium can apply without manual caller instantiation or a disjunctive spec.

**Equivalence note.** `encoder_optional_u64_exact_body_from_framed` derives the closed body from both existing framed branch lemmas. `encoder_optional_u64_exact_some_adapter_from_closed` and `_none_adapter_from_closed` derive the former framed entry shapes from the closed spec. The return-frame lemmas preserve each caller frame. Existing public statements remain unchanged.

Commits `bfee6c4e` and `717140eb` implement this deviation. MCP compile passed. MCP verification returned assumptions `[]`. All seven `Print Assumptions` lines are `Closed under the global context`. The focused target and mandatory Exec `check-fast` passed.

## B2 OptionalU64 closed-shape repair (2026-09-16)

**Before.** `zesuEncoderOptionalU64ExactCallSpec` existentially bound `tag : bv 8` and `outcome : option (bv 64)`. Pure lookup and branch facts fixed both values. The shape checker classified both values as `pure_only`.

**After.** `encoderOptionalU64Outcome bytes` computes the branch and decoded value from `bytes !! 8`. `encoderOptionalU64Valid pointer bytes` rejects a missing tag and keeps the nonzero-branch length and alignment facts. The closed specification now binds only values fixed directly by register, memory, or trace resources.

**Reason.** The B2 zero baseline requires every closed-spec existential to be fixed by resource unification. The byte array already determines the tag and outcome.

**Equivalence note.** A zero tag selects the unchanged `None` trace and return resources. A nonzero tag selects the unchanged encoded-value trace and `Some` return resources. Both adapters still derive the old framed entry shapes. The closed body still follows from the same framed branch lemmas.
