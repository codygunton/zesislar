# Agent-assisted proofs: finish `txAccessList`, add step budgets by forking Islaris

## Context

The agent-assisted plan (issue #347) proves `rlp_decode.txAccessList` and its three array-list callees and its agreement with Sail. Stage A (tooling) is done; two of four functions are proved. This revision keeps the remaining proof work and adds Stage T: termination, as a bound on executed instructions, built into the same block proofs. Every theorem today is partial correctness: Islaris uses Iris's partial weakest precondition and its adequacy theorem is safety of a finite run. The user wants one clean mechanism, obtained by extending the Islaris fork this project already uses.

Terms:
- **Charged address**: an instruction address whose every fetch consumes one step credit.
- **Step credit**: a ghost resource; `step_credits n` allows `n` fetches of charged instructions.
- **Budget**: the credits a function's entry owns; a count of instructions for loop-free code, a potential expression at a loop cut.
- **Region owner**: an Opus agent that runs one function's proof loop (render, bench, package, register, compose).

## State at re-entry (2026-11-24, `origin/main` at `07d59f3bd` or later)

- Merged: tooling (`tools/oblig/*`, `rocq-prover` agent in `.omp/agents/rocq-prover.md`, normaliser, drivers), statements for all four regions (reviewed, pinned; #362, #363), Sail agreement `txAccessListSailAgreement` (#378), rules #376 #379 #380 #384 #394, generator #368 #385 #387 #388 #389, `keysToOwnedSliceCompliance` (#395), `entriesToOwnedSliceCompliance` (#396). Soundness-gate `BASELINE` is `5c7e18792`.
- `keysEnsureCapacity` (B4): branch `aa/b4-ensure`, run dir `_build/agents/aa/keysEnsureCapacity/` with `HANDOFF.md`; 24 of 25 block cases certified; block `0164` waits on branch `aa/rules5` (commit `66c5bb7feb` or later: residual export keeps pieces of facts over 2,048 nodes); the composition file does not compile yet.
- `txAccessList` (B5): contract, candidate, meaning, call premises merged; no block rendered. Run dir `_build/agents/aa/txAccessList/` holds `hints/`, `round-1/derived/` (23 requests) and the closed Sail obligations.
- Drafts in the main checkout, untracked: `docs/AGENT_ASSISTED_RLP_STATUS.md`, `docs/AGENT_ASSISTED_RLP_TERMINATION.md`.
- Islaris is already a fork: `/home/cody/islaris`, remote `fork` = `github.com/codygunton/islaris`, branch `zesu-snapshot-labels` (head `b519aff`), with a local edit to `islaris.opam`. Its opam switch is `/home/cody/islaris/_opam`; the theory `isla` is installed in `_opam/lib/coq/user-contrib/isla`. `Makefile` of this repo selects it with `ISLARIS_REPO ?= $(HOME)/islaris` and `OPAM_SWITCH ?= $(ISLARIS_REPO)`.
- Facts read for Stage T (`/home/cody/islaris/theories`):
  - `lifting.v:72-78`: `isla_irisG`, `state_interp σ _ κs _ := state_ctx σ κs`, `num_laters_per_step _ := 0`.
  - `ghost_state.v:239-242`: `state_ctx σ κs := spec_ctx κs ∗ instr_ctx σ.(seq_instrs) ∗ mem_ctx σ.(seq_mem)`; `:105-120`: `instr_table`, `instr`, `instr_ctx`.
  - `opsem.v:441-444`: `seq_global_state := { seq_instrs; seq_mem }`; `:487-583`: one constructor `SeqStep`; the fetch is its `LDone` branch (`:564-572`), the only place a new instruction starts.
  - `lifting.v`: 21 uses of `wp_lift_step`, 22 of `inv_seq_step`; fetch lemmas `wp_next_instr` (`:352`), `wp_next_instr_extern` (`:378`), `wp_next_instr_pre` (`:416`); `instr_pre'_def` (`:123-133`).
  - `automation.v:683-693`: `instr_kind` (`IKInstr`, `IKPre`), `FindInstrKind`; `:1186`: `li_wp_next_instr`; `:1228`: the lemma that builds an `instr_pre` (name: unverified — confirm first).
  - `adequacy.v`: `isla_adequacy` builds `HeapG … κs Pκs …` and applies `wp_strong_adequacy`.
  - This repo calls the fetch only through `li_wp_next_instr` (`ZesuSsz/Automation/Hooks.v:2415`, `ZesuSsz/Automation2/Hooks.v:3446`). No file here uses `wp_lift_step`, `instr_intro`, `state_ctx`, or matches on `instr_kind` in Gallina. `seq_global_state` fields are used in 5 files of `ZesuSsz/Export/` and 1 of `ZesuSsz/Proofs/Tests/`. Selected code is `instr_lookup_resources` (`InstrSpecs/Lookup.v:6-9`).
- ZisK: on the proving path a run cut off at 2^36 steps yields no proof (source read of `/home/cody/zisk`, not executed). So Stage T proves liveness with a bound; partial correctness already protects soundness.

## Approach

Work runs in lanes: worktree `.worktrees/aa-<lane>`, branch `aa/<lane>` from `origin/main`, pull request with "Refs #347". Gates: `mkdir -p /home/cody/.cache/zesu-tmp/<lane> && TMPDIR=/home/cody/.cache/zesu-tmp/<lane> make check-fast CHECK_AGENT=aa-<lane>`; `make check-iris` as well when a lane touches `ZesuSsz/Automation2/`, `InstrSpecs/`, `ZesuSsz/Contracts/` or `ZesuSsz/Export/`. Long runs go through `tools/bg --heavy`. Never run `tools/cleanup_after_merge.sh` for a branch whose last path component names a run dir. Region owners have about 200 requests each; every one keeps `<run dir>/HANDOFF.md` current, and work is split between a goals agent (run-dir pipeline, residual modules, callers, certificates) and a composition agent (bridges, theorem, registry row) on disjoint files.

### Stage B remainder

**B4. Finish `keysEnsureCapacity`.**
1. Land `aa/rules5`: merge `origin/main`, add its large-fact-pieces fallback as the fourth `zesu_talt residual_pieces` alternative of `zesu_residual_lemma`, run `make check-iris` and `make check-fast`, open and merge the pull request.
2. On `aa/b4-ensure`: merge main, re-bench block `0164` with a 3,600 CPU-second cap, export, normalise (`_build/agents/aa/normalise/REPACKAGE.md`), package, run prover rounds, register, certify. All 25 cases must have a `CLOSURE.json`.
3. Composition: make `ZesuSsz/Compliance/KeysEnsureCapacityGeneratedComposition.v` compile by following `KeysToOwnedSliceGeneratedComposition.v` (block table composed the same way); prove the growth-path exit bridge; theorem `keysEnsureCapacityCompliance : KeysEnsureCapacityContractCorrect`; registry row `proved` with a sealed interface and a call specification in the shape of `ZesuSsz/Contracts/KeysToOwnedSliceCallSpec2.v` (argv0 list header pointer, argv1 allocator pointer, argv2 requested capacity, x10 the outcome code); the approved `spec_shape_baseline.json` row for `KeysEnsureCapacityCallSpec2.v`.

**B5. `txAccessList`.** One goals agent and one composition agent, lane `b5-tx`.
1. Annotation file `tools/block/functions/txAccessList.annotations.json`: call rows for the five `decodeItem` calls from the `derivable` proposals of `derive.py` (fill `arrays[input].caller_value` from the contract's input slice), call rows for the three array-list calls from their registry interfaces, call rows with opaque resources and returned registers for `alloc`, `remap`, `free` (copy the row forms of `keysToOwnedSlice.annotations.json`), a `memcpy` row with `returned_lengths`; loop-cut rows at `+0xc4`, `+0x18c`, `+0x2ec` (`+0x2ec` is not a natural loop head: list it in `loop_heads` by hand row); one `frame` row for the 576-byte frame's saved registers; `unreachable` rows where the contract's domain excludes a path.
2. Loop assertions are decisions of the region owner: each states the owned resources (input remainder, entries list, current keys list, allocator state, result struct) and the pure link to the candidate's partial result. Test each with `annotations.py test` on snapshots from `tools/oblig/exec/run.py --function txAccessList --remap never --at +0xc4,+0x18c,+0x2ec`.
3. Loop as for the array-list regions: `derive.py` rounds, `render_function.sh`, bank, `tools/bench/mkset.py`, `bench.py run --dump-leftover` with `SpatialExportOn`, `store.py sync`, `normalise.py run … --apply`, `package.py goals --defs --falsify`, `drive.py step`, prover rounds from the coordinator's kernel (`tools/oblig/drive_kernel.py`, ladder in `tools/oblig/routing.json`), `residual_loop.py register --function txAccessList`, re-derive so `CALLERS.json` carries the residual imports, rerun, `tools/closure_cert.py`. A goal the screen reports `false-on-real-state` is a finding against the entry that produced it and never goes to a prover. `drive.py step` gives a goal a prover task only when its screen is `true-on-<N>-states` (N >= 1) or the run dir's `UNSCREENED.json` lists it with a reason; it holds every other goal (`HELD` lines, `held: <verdict> <n>` counts) before any spending.
4. Composition: `ZesuSsz/Compliance/TxAccessListGeneratedComposition.v`, exit bridges per return slot, `TxAccessListCallSlice.v` for the `decodeItem` calls (model `ParentHeaderCallSlice.v`), theorem `txAccessListCompliance : TxAccessListContractCorrect`, using `txAccessListMeaningOfOutcome` (`ZesuSsz/Compliance/TxAccessListSailAgreementTheorem.v`) for the meaning conjunct; registry row `proved`.

**C1.** Append to `docs/AGENT_ASSISTED_RLP_STATUS.md` the `decodeTxFields` sizing from `_build/agents/aa/DERIVATIONS.md` and the per-block figures of the four regions (`report.py --function F`), and commit both status documents.

### Stage T: step budgets (fork of Islaris)

**Design, fixed.** Charging is per address, not per proof mode. The machine state carries a set of charged addresses and a counter of fetches of charged instructions. The state interpretation ties the counter to the credits outstanding. Fetching an uncharged instruction is the existing rule with its statement unchanged; fetching a charged one consumes `step_credits 1`. All existing statements and proofs of this repository stay valid (their code is uncharged). A function gets a bound by proving it with its code charged and a budget in its entry. The steps inside one instruction are not charged; they are bounded by the length of its Isla trace.

**T1. Second Islaris checkout and switch (lane `t1`; nothing in `/home/cody/islaris` changes).**
1. `git -C /home/cody/islaris worktree add /home/cody/islaris-budget -b zesu-step-budget zesu-snapshot-labels`; copy the uncommitted `islaris.opam` edit into it.
2. Switch: `opam switch export --switch=/home/cody/islaris /home/cody/islaris-budget/switch.export`, then `opam switch create /home/cody/islaris-budget --empty` and `opam switch import /home/cody/islaris-budget/switch.export --switch=/home/cody/islaris-budget` (unverified — confirm first that the export carries the pins of `coq-iris`, `coq-lithium`, `coq-stdpp*`, `isla-lang`; if not, pin them by the versions `opam list --switch=/home/cody/islaris` prints).
3. Build and install the unmodified theory there (`dune build -p islaris @install` then `dune install`, the way the original was installed: unverified — confirm from shell history or `_opam/.opam-switch/install`), then build this repository in worktree `.worktrees/aa-t1` with `make check-iris ISLARIS_REPO=/home/cody/islaris-budget`. It must pass before any change: this is the baseline.
4. If the switch cannot be reproduced: stop Stage T and report; do not install a modified `isla` into `/home/cody/islaris/_opam` while any region lane is running.

**T2. The fork (lane `t2`, in `/home/cody/islaris-budget`, branch `zesu-step-budget`).**
1. `theories/opsem.v`: `seq_global_state` gains `seq_charged : gset addr` and `seq_fetches : nat` (extend the `Settable` instance). In `SeqStep`, the `LDone` branch becomes: when `σ.(seq_instrs) !! pc = Some es'`, `σ' = if decide (pc ∈ σ.(seq_charged)) then σ <| seq_fetches := S σ.(seq_fetches) |> else σ`; when `None`, `σ' = σ`. No other branch changes.
2. `theories/ghost_state.v`:
   - `heapG` gains `heap_charged_inG :: inG Σ (agreeR (leibnizO (gset addr)))`, `heap_charged_name : gname`, `heap_budget_inG :: inG Σ (authR natUR)`, `heap_budget_name : gname`, `heap_budget_total : nat`.
   - `charged_set (S : gset addr) : iProp Σ := own heap_charged_name (to_agree S)` (persistent, timeless, sealed).
   - `step_credits (n : nat) : iProp Σ := own heap_budget_name (◯ n)` (timeless, sealed), with `step_credits_split : step_credits (n + m) ⊣⊢ step_credits n ∗ step_credits m` and `step_credits_0 : ⊢ |==> step_credits 0`.
   - `instr_table_raw i := own heap_instrs_name (to_instrtbl i)`; `instr_table i := instr_table_raw i ∗ charged_set ∅` (the existing name keeps its lemmas `instr_table_pers`, `instr_table_tl`, `instr_table_agree`, `instr_intro` with unchanged statements).
   - `instr_def a i := ∃ instrs b S, ⌜Z_to_bv_checked 64 a = Some b⌝ ∗ ⌜instrs !! b = i⌝ ∗ ⌜b ∉ S⌝ ∗ instr_table_raw instrs ∗ charged_set S`.
   - New `instr_charged a t := ∃ instrs b S, ⌜Z_to_bv_checked 64 a = Some b⌝ ∗ ⌜instrs !! b = Some t⌝ ∗ ⌜b ∈ S⌝ ∗ instr_table_raw instrs ∗ charged_set S` (persistent, timeless, sealed), with `instr_charged_addr_in_range`.
   - `instr_ctx intrs := instr_table_raw intrs`; `state_ctx σ κs := spec_ctx κs ∗ instr_ctx σ.(seq_instrs) ∗ mem_ctx σ.(seq_mem) ∗ charged_set σ.(seq_charged) ∗ budget_ctx σ.(seq_fetches)` with `budget_ctx f := ∃ m, own heap_budget_name (● m) ∗ ⌜m + f = heap_budget_total⌝`.
   - Lemmas: `instr_lookup`, `instr_lookup_unsigned` (statements unchanged), `instr_uncharged : charged_set S -∗ instr (bv_unsigned a) i -∗ ⌜a ∉ S⌝`, `instr_charged_lookup : instr_ctx instrs -∗ charged_set S -∗ instr_charged (bv_unsigned a) t -∗ ⌜instrs !! a = Some t ∧ a ∈ S⌝`, `budget_spend : budget_ctx f -∗ step_credits 1 ==∗ budget_ctx (S f)`, `budget_bound : budget_ctx f -∗ ⌜f ≤ heap_budget_total⌝`, `instr_table_split : instr_table_raw instrs -∗ charged_set S -∗ ([∗ map] a ↦ t ∈ filter (λ p, p.1 ∉ S) instrs, instr (bv_unsigned a) (Some t)) ∗ ([∗ map] a ↦ t ∈ filter (λ p, p.1 ∈ S) instrs, instr_charged (bv_unsigned a) t)`.
3. `theories/lifting.v`:
   - `isla_irisG`, `wp_asm_def` and every event lemma keep their statements. Each of the 21 step proofs takes the two new components of `state_ctx` in its introduction pattern and frames them back; `inv_seq_step` is extended so the `LDone` case exposes the `decide`.
   - `wp_next_instr` (statement unchanged): its proof uses `instr_uncharged` to pick the uncharged branch.
   - New `wp_next_instr_charged (PC : bv 64) ins : arch_pc_reg ↦ᵣ RVal_Bits PC -∗ instr_charged (bv_unsigned PC) ins -∗ step_credits 1 -∗ ▷ (arch_pc_reg ↦ᵣ RVal_Bits PC -∗ WPasm ins) -∗ WPasm tnil`.
   - `instr_pre'_def is_later a P := ▷?is_later (P -∗ (∃ ins, instr (bv_wrap 64 a) ins ∗ <the existing match>) ∨ (∃ t, instr_charged (bv_wrap 64 a) t ∗ step_credits 1 ∗ (arch_pc_reg ↦ᵣ RVal_Bits (Z_to_bv 64 a) -∗ WPasm t)))`.
   - `wp_next_instr_pre`, `instr_pre_wand`, `instr_pre_to_body`, `instr_pre_intro_Some`, `instr_pre_intro_None`: statements unchanged.
   - New `instr_pre_intro_charged l P t a : instr_charged a t -∗ (P -∗ step_credits 1 ∗ (arch_pc_reg ↦ᵣ RVal_Bits (Z_to_bv 64 a) -∗ WPasm t)) -∗ instr_pre' l a P`. Convention: whoever proves a block pays for its first instruction out of the block's precondition; a jump to an `instr_pre` pays nothing.
4. `theories/automation.v`:
   - `instr_kind` gains `IKCharged (t : isla_trace)`; `FindInstrKind` maps it to `instr_charged a t`; one `find_in_context` instance `(∃ t, instr_charged a t ∗ T (IKCharged t)) ⊢ find_in_context (FindInstrKind a l) T`.
   - `li_wp_next_instr` gains the case `IKCharged t => step_credits 1 ∗ (arch_pc_reg ↦ᵣ RVal_Bits newPC -∗ WPasm t)`; the lemma at `:1228` that builds an `instr_pre` gains the case that applies `instr_pre_intro_charged`, with goal `P -∗ step_credits 1 ∗ (… -∗ WPasm t)`.
5. `theories/adequacy.v`:
   - `islaPreG` and `islaΣ` gain the two new cameras. `isla_adequacy` keeps its statement; it allocates `charged_set ∅`, `● 0`, total `0`, and starts from `{| seq_instrs := instrs; seq_mem := mem; seq_charged := ∅; seq_fetches := 0 |}`.
   - New `isla_budget_adequacy Σ … instrs mem regs Pκs (charged : gset addr) (budget : nat) t2 σ2 κs n : Pκs [] → (∀ {HG : islaG Σ}, ⊢ instr_table_raw instrs -∗ charged_set charged -∗ step_credits budget -∗ backed_mem (dom mem) -∗ spec_trace Pκs -∗ ([∗ map] a↦b∈mem, bv_unsigned a ↦ₘ b) ={⊤}=∗ [∗ list] rs ∈ regs, ∀ (_ : threadG), ([∗ map] r↦v∈rs, r ↦ᵣ v) -∗ WPasm tnil) → nsteps n (initial_local_state <$> regs, {| seq_instrs := instrs; seq_mem := mem; seq_charged := charged; seq_fetches := 0 |}) κs (t2, σ2) → (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧ Pκs κs ∧ σ2.(seq_fetches) ≤ budget` (the bound comes from the final state interpretation through `budget_bound`).
   - New operational lemma, no Iris: `fetches_bound_steps`: for one thread, if `seq_charged = dom instrs` then `n ≤ (S σ2.(seq_fetches)) * S (max_trace_length instrs)` where `max_trace_length` is the maximum of `isla_trace_length` over the table, using that every `trace_step` strictly decreases `isla_trace_length` (`opsem.v:78`; prove `isla_trace_length (subst_trace v x t) = isla_trace_length t`). If this lemma is not closed within the lane, deliver the fetch bound alone and say so; nothing later depends on it.
6. Build the fork's `theories/` (both architectures) and its `examples/` that built before; commit on `zesu-step-budget`; push to remote `fork`; install into `/home/cody/islaris-budget/_opam`.
7. Stop and report, without changing course, if any existing lemma statement that this repository uses has to change, or if an event lemma statement has to change.

**T3. Compatibility gate (lane `t3`, worktree `.worktrees/aa-t3` from `origin/main`).** With `ISLARIS_REPO=/home/cody/islaris-budget`: adapt `ZesuSsz/Export/*.v` and the one test file to the two new `seq_global_state` fields (record literals get `seq_charged := ∅; seq_fetches := 0`; `zesu_adequacy` keeps its statement). No other source file may change. `make check-iris`, `make check-fast` and `make check-signatures` must pass with zero edits under `ZesuSsz/Automation/`, `ZesuSsz/Contracts/`, `ZesuSsz/Compliance/`, `ZesuSsz/Proofs/`, `ZesuSsz/Generated/`. Record user-space instruction counts for `nextUint64` block `0064` and `decodeParentHeader` block `0000` before and after. This lane's pull request stays open until T9 switches the default Islaris.

**T4. Budget layer in this repository (lane `t4`, on top of `t3`).**
1. `InstrSpecs/LookupCharged.v`: `instr_lookup_resources_charged (lookup : Z -> option isla_trace) : iProp Σ := □ ∀ address t, ⌜lookup address = Some t⌝ -∗ instr_charged address t`, persistent, with the `find_in_context` lemma that returns `IKCharged`, mirroring `InstrSpecs/Lookup.v:40-90`.
2. `ZesuSsz/Automation2/StepBudget.v`: `step_budget (z : Z) : iProp Σ := ⌜0 ≤ z⌝ ∗ step_credits (Z.to_nat z)` (sealed, unfold instance, timeless); lemmas `step_budget_spend : 1 ≤ z → step_budget z ⊢ step_credits 1 ∗ step_budget (z - 1)`, `step_budget_weaken : 0 ≤ z2 ≤ z1 → step_budget z1 ⊢ step_budget z2`, `step_budget_split : 0 ≤ z1 → 0 ≤ z2 → step_budget (z1 + z2) ⊣⊢ step_budget z1 ∗ step_budget z2`.
3. Lithium rules in `ZesuSsz/Automation2/` (hooks only in `Hooks.v`): a goal `step_credits 1 ∗ G` with `step_budget z` in the context continues with `G` and `step_budget (z - 1)`, side condition `1 ≤ z` (closed by computation when `z` is a literal, else by the linear solver; the difference of two literals is computed); a goal `step_budget z2 ∗ G` uses `step_budget_weaken` or `step_budget_split` on the context's budget; the selected-code lookup hooks (`ArrayLoadPriority`-style in `Automation2`) accept `instr_lookup_resources_charged`. Tests in `ZesuSsz/Proofs/Tests/StepBudget.v`: a three-instruction charged program closes with `step_budget 3` and fails with `step_budget 2`.
4. `ZesuSsz/Export/BudgetAdequacy.v`: `zesu_budget_adequacy`, the instance of `isla_budget_adequacy` in the shape of `zesu_adequacy`, plus one closed example (`ZesuSsz/Proofs/Tests/BudgetAdequacyExample.v`): a two-instruction charged program ending in a trap, with conclusion `σ2.(seq_fetches) ≤ 2`, and `Print Assumptions` closed.
5. `AGENTS.md`: new section *Step budgets*: "A function is charged when its selected code is `instr_lookup_resources_charged` and its contract entry owns `step_budget`. A budget of loop-free code is the count of instructions on its longest path plus its callees' budgets, emitted by `tools/block/budgets.py`; this count is not inference. A loop cut owns a potential given by a `potential` annotation row. Uncharged and charged theorems of one function may coexist; a composition uses one kind for all its callees."

**T5. Budgets in the generator (lane `t5`, on top of `t4`).**
1. New `tools/block/budgets.py`: from `build/stock-zisk/cfg.json` and the function's profile it computes, per block boundary, `B(b) = instructions(b) + max over successor edges`, where a call edge adds the callee's budget (registry field `budget` of the callee's row in `ZesuSsz/Contracts/proved_functions.json`: an integer, or a Coq `Z` expression over the call's argument registers) and a return edge adds 0; at a loop cut `B` is the cut's `potential` expression. A cycle with no `potential` row is refused with the cut's offset. Output `<run dir>/round-<n>/derived/BUDGETS.json`.
2. Annotation schema (`tools/oblig/annotations.py`): row kind `potential` at a `loop_cut`: `{"at": …, "potential": "<Coq Z expression over the cut's binders>"}`; profile key `charged: true`.
3. Rendering (`tools/block/render_fp301_entries.py`, `render_function_callers.py`): when the profile has `charged: true`, every entry statement gains the conjunct `step_budget (<B>)`, placed with the owned resources, and the block's code premise is the charged selected code. With `charged` absent the output is byte-identical to today (goldens: `nextUint64`, `decodeParentHeader`).
4. A back edge whose potential does not follow syntactically leaves a pure goal `potential_after + cost ≤ potential_before`; it goes through the normal goal pipeline.

**T6. Loop-free prototype: `keysEnsureCapacity`, charged (lane `t6`, after B4 is merged).**
1. Budgets of its callees, as new assumed premises in `ZesuSsz/Contracts/AltFlAllocBudgetPremises.v`: the existing `alloc`, `remap`, `free` and general `memcpy` call specifications with `step_budget K` added to the precondition, where `K` is the longest-path instruction count of each callee from `cfg.json` (`budgets.py --function <callee>`); the existing premises are untouched. Review them (the coordinator holds the user's delegation), pin them in `ZesuSsz/Evidence/SignatureGates.v`, add them to `approved_runtime_premises`, registry rows `assumed` with `budget`.
2. `ZesuSsz/Contracts/KeysEnsureCapacityBudgetContract.v`: the existing model with `step_budget (keysEnsureCapacityBudget)` in the entry resources (a literal from `budgets.py`) and selected code `keysEnsureCapacityChargedCode := instr_lookup_resources_charged …`; statement `KeysEnsureCapacityBudgetContractCorrect`. The uncharged contract and theorem stay.
3. Profile copy with `charged: true` in a separate generated tree (`tools/block/generated/keysensurecapacity_budget_fp301_callers`, proofs under `ZesuSsz/Proofs/KeysEnsureCapacityBudget/`); render; bench all cases with no model; registered residual lemmas of the uncharged proof are reused through their existing modules.
4. Composition by copying the uncharged composition with the budget conjunct threaded; theorem `keysEnsureCapacityBudgetCompliance`.
5. Measure and report: cases that close with no change beyond the budget, cases that need a prover, added user-space instructions per case, hand-edited lines in the composition.

**T7. Loop prototype: `decodeItem`, charged (lane `t7`).** `decodeItem` has 24 blocks, two loop cuts (`+0xc4`, `+0x164`), no callees, a generated proof (`decodeItemGeneratedCompliance`), and is a callee of `txAccessList`. Add `potential` rows: at each cut, `c * (bound - index) + d` over the cut's existing index and bound binders, with `c` the instruction count of the loop body and `d` the longest path after the loop (both from `budgets.py`); if a cut's design has no bound binder (the profile `tools/block/functions/decodeItem.json` has cursor and extent only), the potential uses `extent - cursor`. Contract `ZesuSsz/Contracts/DecodeItemBudgetContract.v` with budget `c_total * input length + d_total`; charged tree and theorem `decodeItemBudgetCompliance`; registry interface row for the charged call specification. The uncharged theorem and its callers stay.

**T8. Roll-out.** Charged variants, in this order, each by T6's recipe: `keysToOwnedSlice`, `entriesToOwnedSlice` (one shared bridge edit), then `txAccessList` with `potential` rows at its three cuts (lexicographic potential written as one `Z` expression: `c1 * remaining outer bytes + c2 * remaining entry bytes + c3 * remaining key bytes + d`) and budgets for its 12 calls from the registry. Final theorem `txAccessListBudgetCompliance`, and `txAccessListStepBound` in `ZesuSsz/Export/BudgetAdequacy.v`: from `zesu_budget_adequacy` with the charged set equal to the code of `txAccessList`, its three array-list callees and `decodeItem`, the number of fetches is at most the contract's budget.

**T9. Switch the default Islaris.** After T3 to T8 are merged-ready and no region lane is running: merge `zesu-step-budget` into the fork's `zesu-snapshot-labels`, install into `/home/cody/islaris/_opam`, merge the T3 to T8 pull requests in order, run `make check-iris`, `make check-fast`, `make check-signatures` on main, move `BASELINE` in `tools/soundness_gate.py` with the protected-file diff in the pull request, remove `/home/cody/islaris-budget`.

Order: B4 and B5 start at once and do not wait for Stage T. T1 starts at once. T2 follows T1; T3 follows T2; T4, T5 follow T3; T6 needs B4 merged; T7 needs T5; T8 needs T6, T7 and B5; T9 last. If B5 finishes before T5, `txAccessList` is proved uncharged first and its charged variant is a re-render and rerun.

### Targets added by Stage T

|Measure|Target|
|---|---|
|Statements of this repository changed by the fork|0|
|Edits under `ZesuSsz/Automation/`|0|
|Decisions for a loop-free function's budget|0|
|Decisions per loop cut|1 potential row|
|Cases of a charged variant that need a prover again|reported; expected only back-edge potential goals|
|Added cost per block|reported|

## Critical files and anchors

- `/home/cody/islaris/theories/opsem.v` — `seq_global_state` (441), `SeqStep` `LDone` branch (564): the only operational change.
- `/home/cody/islaris/theories/lifting.v` — `isla_irisG` (72), `instr_pre'_def` (123), `wp_next_instr` (352): where charging enters the logic.
- `/home/cody/islaris/theories/automation.v` — `instr_kind` (683), `li_wp_next_instr` (1186): the single automation entry this repository calls.
- `InstrSpecs/Lookup.v` — `instr_lookup_resources` (6) and its `find_in_context` lemmas: the form `LookupCharged.v` mirrors.
- `ZesuSsz/Compliance/KeysToOwnedSliceGeneratedComposition.v` — the composition every later region copies.

## Verification

- T1: `make check-iris ISLARIS_REPO=/home/cody/islaris-budget` passes on unmodified sources.
- T2: the fork builds; `Print Assumptions isla_budget_adequacy` is closed; a test in the fork proves a one-instruction charged program cannot be verified with `step_credits 0` (the fetch goal needs a credit) and can with `step_credits 1`.
- T3: all three gates pass with source changes only under `ZesuSsz/Export/` and the one test file; `git diff --stat origin/main -- ZesuSsz/Automation ZesuSsz/Contracts ZesuSsz/Compliance ZesuSsz/Proofs ZesuSsz/Generated` is empty.
- T4: `ZesuSsz/Proofs/Tests/StepBudget.v` (budget 3 closes, budget 2 does not) and `BudgetAdequacyExample.v` (`σ2.(seq_fetches) ≤ 2`, assumptions closed) compile; rocq-mcp `rocq_verify` on the example (route: drive the `rocq-mcp` stdio server from Python as `tools/pin_hypotheses.py` does, with `OCAMLPATH=<worktree>/_build/agents/<lane>/install/default/lib opam exec --switch=<switch> --`).
- T5: goldens unchanged for uncharged profiles; a fixture function with one loop and no `potential` row is refused with the cut's offset; with the row its entries carry the expression.
- T6, T7, T8: per function, every case has a `CLOSURE.json`, `render_open_blocks.py --check` reports 0 open, `Print Assumptions <F>BudgetCompliance` is closed, `make check-iris` and `make check-fast` pass, `check_relocatable.py` passes.
- End to end: `Print Assumptions txAccessListStepBound` is closed and its statement bounds `seq_fetches` by an expression in the input length.
- B4, B5: as in the regions already merged: certificates for every case, 0 open block obligations, `Print Assumptions` closed, both gates, registry check.

## Assumptions and contingencies

- **Islaris fork ownership.** The fork `codygunton/islaris` takes one more branch; if the user wants the change proposed upstream instead, T2's commits are already separable from the snapshot-label commits.
- **Relative bounds.** A charged function that calls an uncharged one gets a bound on its own instructions only. The plan avoids this by giving `decodeItem` a charged variant before `txAccessList`. `nextUint64` and `decodeParentHeader` stay uncharged in this plan.
- **Allocator and `memcpy` budgets are assumed**, as their correctness already is. If `alt_fl_alloc.free` or `alloc` is proved later, its budget is proved with it.
- **If T2 step 7 triggers** (a used statement must change): stop Stage T, keep Stage B, and report the statement and why; the fallback is the operational bound for loop-free functions only, which needs no fork.
- **If T3 fails on a frozen file:** report the file and error; do not edit `ZesuSsz/Automation/`; the user decides on the hygiene check's emergency override.
- **If T6 shows a budget conjunct breaks more than five cases of a region that closed uncharged:** stop the roll-out after T6 and report the stuck goals before T7.
- **Duplicate trees.** Charged variants live beside uncharged ones. If the user prefers a clean cutover for the four functions of this plan (no proved caller depends on them), T6 and T8 replace the uncharged trees instead; `decodeItem` keeps both because `nextUint64` and `decodeParentHeader` call its uncharged form.
- **ZisK.** The reliance "a run that does not end yields no proof" is added to `docs/TRUST.md` in C1's commit; it rests on a source read.
