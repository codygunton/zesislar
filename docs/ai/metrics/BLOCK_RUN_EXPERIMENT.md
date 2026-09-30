# Block-run experiment: one `zesu_block` run per basic block

Root 931f8386. Measurement only. Per-block CSVs (sorted by wall time): `ZesuSsz/Evidence/block-run/`. Runs 2026-09-28/29.

## Setup
- Blocks: the `Evidence/generate_zesu_cfg.py` rule gives 102 blocks (cut after calls) or 26 (no cut after calls).
- Entry: the merged lemma at the leader (87 of 102, 22 of 26). Premises inside the block are dropped; call premises stay.
- Arm A (bounded): the merged premise at each successor stays. Otherwise the successor gets an abstract
  `instr_pre SUCC BLK_STOP`: "reached" means the run stopped there with the inferred state.
  Arm B (free): successor premises are dropped too. "merged" arm: arm A with the module's own `zesu_block` (mostly AllLegacy).
- Automation: a copy of `zesu_run_pass_v2` (the same search list) that prints the PC after each step, so a killed
  run still gives k. Limits: A 600 s, B 1800 s, 8 GiB systemd fence per job, at most 56 coqc. CPU and RSS from `wait4`.
- All 25 A runs with no goal left were rechecked with `Qed`; all close under the global context.
- "partial": the entry state itself carries `instr_pre` at an address inside the block. The run closes at that
  in-state handoff, not at the block exit: 0x15930→0x1593c, 0x15940→0x1594c, 0x15950→0x1595c (the byte_lists jalr),
  0x15960→0x15968, 0x14d80→0x14e00.

## Arm tables (wall time in s: <10/10-30/30-60/60-120/120-300/cap, then the median)
| arm | wave | run | closed | partial | reached | stalled | cap/fence | wall histogram | median |
|---|---|---|---|---|---|---|---|---|---|
| A 102 | 1-4 | 68 | 20 | 4 | 4 | 40 | 0 | 21/40/6/0/1/0 | 12.9 |
| A 102 | 5-8 | 10 | 0 | 0 | 0 | 8 | 2 | 4/4/0/0/0/2 | 12.4 |
| A 102 | 9-16 | 3 | 0 | 0 | 0 | 2 | 1 | 0/2/0/0/0/1 | 25.1 |
| A 102 | 17+ | 6 | 0 | 1 | 0 | 3 | 2 | 1/2/1/0/0/2 | 31.0 |
| B 102 | 1-4 | 68 | 11 | 4 | – | 53 | 0 | 3/40/21/3/1/0 | 25.4 |
| B 102 | 5-8 | 10 | 0 | 0 | – | 8 | 2 | 0/7/1/0/0/2 | 24.4 |
| B 102 | 9-16 | 3 | 0 | 0 | – | 2 | 1 | 0/0/2/0/0/1 | 49.1 |
| B 102 | 17+ | 6 | 0 | 1 | – | 3 | 2 | 0/2/1/1/0/2 | 49.6 |
| A 26 | 1-16 | 10 | 2 | 0 | 0 | 8 | 0 | 1/9/0/0/0/0 | 16.4 |
| A 26 | 17+ | 12 | 0 | 0 | 0 | 7 | 5 | 0/4/2/1/0/5 | 72.7 |
| B 26 | 1-16 | 10 | 0 | 0 | – | 10 | 0 | 1/7/2/0/0/0 | 20.8 |
| B 26 | 17+ | 12 | 0 | 0 | – | 7 | 5 | 0/6/0/1/1/4 | 71.2 |
- The cap/fence runs are the same 5 blocks in every arm: 4 memcpy call blocks (0x14d30, 0x151dc, 0x15590, 0x15694)
  and the 96-instruction loop 0x15754 (the 8 GiB fence, or the cap).
- A 102: 24 blocks need no cut (closed or reached); 63 need a cut; 15 have no entry state.
- A 102, instructions traversed k: 1: 9, 2: 22, 3: 29, 4: 12, 5-8: 11, 9-16: 1, 17+: 3.
  k/n: <.25: 4, .25-.5: 2, .5-.75: 17, .75-<1: 33, =1: 31. Peak RSS median 1.4 GiB, max 7.8 GiB (0x15754).
- B traversal (distinct PCs per free run): median 2, max 30. 20 runs cross into a later block
  (0x14e28 runs through 5 header chunks). B reaches 3 of the 15 no-entry leaders (0x1511c, 0x1513c, 0x15194).
- Merged-automation arm: same result as v2 on 83 of 87 blocks; median wall 33 s against 13 s.
  v1 on the 5 v2 timeouts is no better: 4 hit the cap and 1 the fence.

## Stall classes and cuts (A 102, v2; leader→cut at the stall PC)
- call, unknown (20): 9 on `∃ x, Index.lookup ADDR = Some x` (0x15cb0 ×6, 0x10190 ×3); 8 on
  `FindStructRegMapsTo "mstatus"` or `FindRegMapsTo "x1"`; 3 on an `∃ (sp, ra)` reg_col frame match.
  0x150fc→0x15100 0x15108→0x15110 0x15128→0x15130 0x15148→0x1514c 0x1515c→0x15178 0x1519c→0x151ac 0x151c4→0x151c8
  0x153c0→0x153c8 0x15564→0x1556c 0x15574→0x1557c 0x155a4→0x155b4 0x155e4→0x155f4 0x155fc→0x1560c 0x15620→0x15624
  0x1562c→0x1563c 0x15644→0x15654 0x156a8→0x156ac 0x15974→0x15978 0x15980→0x15988 0x159a0→0x159a8
- call, C1 (13): 0x150f0→0x150f4 0x15200→0x15208 0x15210→0x15214 0x155bc→0x155c4 0x155cc→0x155d0 0x155d8→0x155dc
  0x156b4→0x156b8 0x156c0→0x156c8 0x156d0→0x156d4 0x156e8→0x156ec 0x156f4→0x156f8 0x15700→0x15714 0x1571c→0x15724
- call, C6 (6): 0x158e0→0x158e8 0x158f0→0x158f8 0x15900→0x15908 0x15910→0x15918 0x15920→0x15928 0x15994→0x15998
- call, C2 (2): 0x159b0→0x159b4 0x159c8→0x159d0. Call, timeout (4, memcpy): 0x14d30→0x14d78 (k 19/20)
  0x151dc→0x151f8 (8/9) 0x15590→0x1559c (4/5) 0x15694→0x156a0 (4/5).
- call, partial (4 at an in-state handoff): 0x15930→0x1593c 0x15940→0x1594c 0x15950→0x1595c 0x14d80→0x14e00.
- branch or jump (5, unknown): loop tails stop on `(count - 1)%bv ≠ 0%bv` at 0x153a8→0x153b0, 0x15558→0x15560 and
  0x15614→0x1561c; a withdrawal payload existential at 0x1568c→0x15690; 0x15190→0x15190 at the jump.
- array load (5): C4 0x153d4→0x153d8 0x15668→0x15668 0x15678→0x15678; C2 0x15228→0x15238; 0x15754→0x157cc (fence).
- pure or other (4): C4 0x159d8→0x15a10; C2 0x14f08→0x14f18 0x1521c→0x15224; 0x15960→0x15968 (partial).
- Kinds: call 49 of 63 cuts, branch or jump 5, array load 5, other 4.

## Call stall anatomy (6 representatives; merged lines = hand lines of the leader lemma)
| block | class | residual (head) | what is missing | merged lines, same step? |
|---|---|---|---|---|
| 0x155cc | C1 | `∃ x : spec, ⌜scons_snap (SWriteMem …) …⌝` | callee pre, trace conjunct: the output-event witness | 8; yes: poses `encoder_int_exact_framed_correct` with explicit args |
| 0x156f4 | C1 | `∃ (spec, regs, sp…), reg_col … ∗ spec_trace x.1 ∗ …Frame` | callee pre, existential witnesses | 62; yes: `liARun` then `iExists (tail, 0x15700, sp, …)` |
| 0x158e0 | C6 | `∃ (sp, v), … ∗ instr_pre 0x158f4 (…)` | callee pre frame plus return continuation | 14; yes: `zesu_run_until`, then `iExists (frame, …)` |
| 0x15920 | C6 | the same shape, return 0x15934 | callee pre frame plus return continuation | 14; yes: the same pattern |
| 0x155a4 | unknown | `∃ x : isla_trace, Index.lookup 89264 = Some x` | callee spec not found (no premise for 0x15cb0) | 9; yes: poses `encoder_u256_exact_correct` |
| 0x15980 | unknown | `find_in_context (FindStructRegMapsTo "mstatus" "bits")` | other: jalr trace reads mstatus, which the frame does not expose | 19; no: the lines build the ∀-stack return continuation |
- Call blocks whose merged proof has more than 20 hand lines at the call: 25 of 79. Top 5: 0x1594c (181), 0x1595c (177),
  0x1593c (161), 0x1597c (154), 0x1599c (154).
  - 0x1597c: the same shape as 0x15980 (mstatus). 0x1599c: the same shape as C6 (an `∃` frame match).
  - 0x1593c, 0x1594c and 0x1595c: a different shape. From the merged state at the jalr, a v2 run times out at 600 s
    with no step. All three modules load `zesuEncoderBooleanCallSpec`'s instance (see Import sensitivity).

## Where the time goes
- Closed runs, Ltac profile (the 6 slowest, cutoff 1%): tactic time is 0.7-27 s of a 3-30 s wall. Load and goal
  printing take the rest; Qed is not in the probe (the separate Qed check takes 4-26 s). Each figure is the share
  of the group's top tactic, and the groups overlap: Lithium step (`zesu_liAStep`) 57-70%, zesu_finish 6-21%,
  unfold/simplify 5-9%, bv_solve 0-8.5% (8.5% only in 0x14d80).
- Capped runs: the Coq `timeout` discards the Ltac profile, so the source is perf (49 Hz, 30-40 s windows).

| block | where | perf top symbols | group |
|---|---|---|---|
| 0x14d30 | k 19/20, auipc before memcpy | Conversion.eqappr 10.7%, CClosure.mk_clos 10.5%, Conversion.pure_rec 6.2% | kernel conversion |
| 0x151dc | k 8/9, same | CClosure.mk_clos 11.0%, Conversion.eqappr 9.4%, pure_rec 7.0% | kernel conversion |
| 0x15590 | k 4/5, same | CClosure.mk_clos 11.4%, Conversion.eqappr 9.3%, pure_rec 7.3% | kernel conversion |
| 0x15694 | k 4/5, same | CClosure.mk_clos 10.8%, Conversion.eqappr 9.7%, pure_rec 7.0% | kernel conversion |
| 0x15754 | k 31/96, loop body `lbu`; fence or cap | CArray.loop 18.6%, caml_c_call 15.6%, Micromega Polynomial.* 27% | lia (zesu_finish solvers) |
- None of the capped runs is in bv_solve. The largest symbolic register value at a kill is not observable (no goal printed).

## Import sensitivity
- One declaration changes a 13 s block (0x14e28) into a run of more than 600 s:
  `Global Instance : LithiumUnfold (@zesuEncoderBooleanCallSpec) := I.` (`WriteSuccessEncoderBooleanCall.v:32`).
- Bisect: `Interfaces`, then each of its 174 deps (all slow), then one dep's dependency-ordered closure
  (prefix 7 fast, prefix 8 slow). Inline: the Definition alone 9 s; with the instance, over 90 s.
- Likely mechanism (inferred from perf, not traced): at the write_output call, the `LithiumUnfold` search tries this
  instance against `zesuWriteOutputCallSpec`. Both are `zesu_call 16 …`, so conversion unfolds and compares both bodies.
- Count: it is the only global `LithiumUnfold` on a `zesu_call` spec (of 1,446 LithiumUnfold instances).
  627 of 1,253 proof modules load it transitively; none loads 2 such instances. 12 of the 87 A probes load it.
  A generated segment that imports `Interfaces` for its call premises loads it.
## LithiumUnfold removal test (scratch worktree; no tracked proof file changed)
- The global instance cannot simply go: `WriteSuccessEncoderBooleanCall.v:42` and `WriteSuccessEncoderOptionalU64SomeBooleanCall.v:45`
  then fail ("side condition"). Variant that keeps all 117 built targets green: `#[local] Instance` in those 2 modules.
- A probes (local variant, cap 600): 0x14e28 closes (5 s). Of the 12 probes that load the instance, 10 give the same result,
  1.1-5× faster (the with-instance runs ran under a higher load). 0x14e88 and 0x14ed4 reached `BLK_STOP` with the instance
  and stall without it (they used it).
- The 4 memcpy blocks (cap 1800) still time out at the same auipc: a separate cause.
- 30 merged modules that load it (the slowest in the orch gate trace; 6 replaced because a dependency runs out of memory at the
  6 GiB dune fence), one fresh coqc each: 29 pairs compile in both arms (1 failed with the instance). CPU sum 5,808 s with,
  5,930 s without. Ratio without/with: min 0.70, p25 0.98, median 1.02, p75 1.07, max 1.31. No speedup.

## No entry (15): no merged lemma at the leader, and no inferred state
0x14e14 0x14e94 0x14ea0 0x14eac 0x14eb8 0x14ec8 0x14ee4 0x14efc 0x14f00 0x1511c 0x1513c 0x15194 0x1573c 0x158d4 0x159bc.
At a call block, `BLK_STOP` is reached at the call site before the return, so it is not the state at the leader.

## 2 h reruns of the capped blocks
All 4 memcpy blocks hit the 7,200 s cap (7,166 CPU s each; peak 2.8 GiB) with no step past the auipc before the call
(0x14d78, 0x151f8, 0x1559c, 0x156a0). 0x15754 hits the 8 GiB fence at 447 s (k 31/96).

## memcpy stall (0x14d30, 0x151dc, 0x15590, 0x15694; probe copies only, no tracked change)
- Reproduction: 0x15590 (5 instructions), arm A, the `zesu_run_pass_v2` copy. The run hangs over 300 s at the auipc 0x1559c.
  Wrapping each search step in `timeout 30` exposes the goal: after the jalr, prove `zesuMemcpyCallSpec` from the caller context.
- Callee-spec form, same state and tactic:
  - generic `□ instr_pre 0x101d4 zesuMemcpyCallSpec`: hangs over 300 s, with or without the `Interfaces` import;
  - the merged proof's specialized `memcpyWholePublic base start bytes src …`: closes in 4 s;
  - no call premise: steps into memcpy at once.
- Entry-state bisect (generic spec): removing the source array `base ↦ₘ∗ bytes`, the destination `↦ₘ?`, or the pure
  facts, or making the source array exact at `src`: all still hang. The hang does not depend on the resources.
- Automation bisect on the exposed goal (each alternative alone, 40 s): 22 of 24 return at once. `zesu_liAStep` and
  `liUnfoldLate` time out. Both reach `li_do_unfold`. There the typeclass query `LithiumUnfold (@zesuMemcpyCallSpec)`
  takes over 60 s, and `iEval (unfold zesuMemcpyCallSpec)` takes 1 ms.
  `Set Typeclasses Debug` prints only the query line in 20 s: the first candidate's unification never returns.
- Mechanism: `Class LithiumUnfold {A} (x : A)` has no Hint Mode, and its 1,446 instances name transparent constants,
  so every instance is a candidate. Unifying `zesuMemcpyCallSpec` with another candidate unfolds both into
  `zesu_call …` bodies (about 30 register conjuncts each) and compares them. Perf: about 45% of CPU in
  `Conversion.eqappr`, `CClosure.mk_clos`. This is the same class of problem as the Boolean-instance import sensitivity.
- The removal that fixes it: `Global Typeclasses Opaque zesu_call.` (or `…Opaque zesuMemcpyCallSpec.`) in the probe. The query takes 0 s.
  - 0x15590 ends in 5 s; 0x14d30, 0x151dc and 0x15694 end in 6-23 s. All 4 then stall at the call on a real mismatch:
    the generic `zesu_call` pre wants `reg_col [x5 x6 x7 x28-x31]`, which the caller does not own.
  - The Boolean case 0x14e28 with `Interfaces` imported closes in 6 s (over 300 s without the fix).
  - `Global Hint Mode LithiumUnfold - !` does not help (still over 60 s).
- Proposed fix (not implemented, and not tested on the full gate): add `Global Typeclasses Opaque zesu_call zesu_call_ret.`
  to `Automation/Calls.v`, so the `LithiumUnfold` search cannot unfold call-spec bodies. The register mismatch above
  remains a separate contract question.
