# Block-automation rebuild, proved out on decodeParentHeader

This file is the maintained copy of the plan (tracking issue #316). The coordinator updates the
"Status" and "Amendments" sections at every merge, gate result and plan change; the sections from
"Context" on are the approved plan text, edited only where an amendment says so. Detailed
coordinator notes: `_build/agents/rebuild/STATE.md`.

## Status (updated 2026-11-22T10:40Z; main `084364765`)

**The prove-out's end state is reached and on main (#345):**
`Theorem parentHeaderCompliance : ParentHeaderContractCorrect`, with no open-block premise, no
exit-meaning premise and no callee premise; `Print Assumptions`: Closed under the global
context (also `nextUint64Compliance`). All 98 decodeParentHeader blocks close in one run at the
final rules and are certified; the open-block records of decodeParentHeader and nextUint64 are
empty; `Contracts/proved_functions.json`: decodeItem, nextUint64, decodeParentHeader `proved`.

Merged: #317 (0.3), #318 (1.4), #319 to #323 (1.1a to 1.1e), #324 (1.2), #325 (1.3), #327
(1.5), #328, #329, #335 (rule batches 1 to 3), #326 (2.2), #330 (2.1 contracts), #331 (M2),
#332 (1.6), #333, #337 (cost), #334 (`join_guard_form`), #336, #339 (rules), #340 (exit design
A), #341 (certificates), #342 (composition cost), #343 (meaning, error side), #344 (tools for
unseen functions), #345 (blocks, meaning success side, final theorem), #346 (generic generator
repairs, tools only; the three developed renders byte-identical). #338 closed, superseded.

**Final verification (plan section "Verification") on main `52e154ff9`, whose tree equals the
gated head `ef39bca51`:**

|Item|Result|
|---|---|
|1. `make check-fast`, `make check-iris`|0, 0 (gate cycle `gates-fin`)|
|1. `make check-signatures`|0 (at `ef39bca51`)|
|1. `tools/soundness_gate.py`|NOT RUN: waits for the user's decision on its baseline (below)|
|2. `Print Assumptions parentHeaderCompliance`, `nextUint64Compliance`|Closed under the global context, twice (coordinator's own rocq-mcp check)|
|2. `grep -c parentHeaderOpen_`, `nextUint64Open_`|0, 0|
|3. `make check-support-freshness`|0|
|4. candidate vectors (`ParentHeaderCandidateVectors.v` builds in check-iris); emulation driver|36 results, rc 0|
|5. PH-ALL|98 of 98 (the layout has 98 blocks since exit design A; the plan text says 90)|
|5. NU-ALL, BENCH-v1, decodeItem sweep, free, berlinGasCalc|10 of 10; 16 of 16; 24 of 24 at +0.21%; 39 of 39; 9 of 9|
|7. hygiene with `EDGE-PROOF`, its tests|0; OK|

One gate line needed a rerun: the first sweep run marked decodeItem 6b08 open through a harness
race (the caller had compiled; the memory-accounting code read a control group that was already
gone); the rerun is 24 of 24.

**Open:** (1) the soundness gate's baseline (user decision, below); (2) optimisation items,
none blocking: the meaning data's cost (loop blocks +87% to +118%, field return sites +52% to
58%, error-edge blocks +37%: fold and walk facts re-proved by the generic linear search), the
heavy slots `0514_slot0..4` and `0274_slot2..6` (440 to 1,900 CPU-s, 6 to 9.6 GiB against the
goal of 300 s and 6 GiB), nextUint64 0000; (3) Phase 3 (amendment 15): the repaired generator
is on main (#346; it also fixes the harness race above); held-out results below; whether to
run a second repair round (the renderer crash on empty or refuted boundaries, indexed access
into arrays, an instance exposing a contract's ranges and links to the prover, a domain
convention for pointers) and a third batch is the user's decision.

**Held-out measurement on main's rules (2026-11-21; zero new rules, zero new function data;
`_build/agents/rebuild/heldout/RESULT.md`):**

|Function|Callers|Closed 2026-11-12|Closed now|Not closed now|
|---|---|---|---|---|
|berlinGasCalc (partly seen: its 9 closed blocks are a gate, two blocks were memory tests)|38|7|25|13 open|
|hpDecode (clean reserve, counts only)|10|1|3|7 open|
|resumeCall (clean reserve, counts only)|13 of 20 blocks render|2|2|4 open, 7 over the CPU cap; 7 callers cannot be rendered|

Reading: the rules transfer to a function of similar shape; on the two untouched functions the
count is 5 of 23. The mechanical classes of what is left point at the generator and at
statement size (a needed fact hidden; entries the generator refuses; blocks over their cap), not
at one missing rule, but nobody has read those goals. Scalable automation is NOT yet shown.
hpDecode and resumeCall stay untouched for a final measurement.

**Three diagnostic held-out sets (2026-11-21, user request; chosen to look different; leaf
functions of other modules; failures read and classified, nothing fixed;
`_build/agents/rebuild/heldout2/SELECTION.md`, `A/`, `B/`, `C/RESULT.md`):**

|Set|Blocks|Closed|Over cap or killed|Open|Refused at render or caller not rendered|
|---|---|---|---|---|---|
|A: Rust byte-packing and limb compare (`kzg`, `utils::lt`, `fr`)|29|5|4|4|16|
|B: memory loops (`mem.eql`, `mem.rotate`)|34|6|0|5|23|
|C: compare chains into one join of 19 or 21 edges (two `hash_map` eql)|43|0|43|0|0|
|Total|106|11|47|9|39|

Causes found, by owner. Generator code: nested loops refused (all of `mem.rotate`); a loop
cursor covers one byte, so a word load at a cursor is unreadable; the forward pass forks every
load on the memory region when the contract allows the data in several regions and runs out of
its path budget (sets A and C; set C rendered only after its contract was narrowed to RAM); a
join drops a fact (two triggers; the family of contingency C5); the guard fact of a wide join
is a disjunction that repeats every earlier equality (73 to 92 KB; every block that must prove
it reaches 16 GiB: untested inference, no goal was printed). Statement size: blocks of 100 and
114 instructions and blocks whose successor entry has 62 to 133 binders reach their caps.
Rules: equality of two argument registers; right shift of a non-literal; a load from a
read-only constant at a numeric address (inferred). Instruction support: none (all 619 new
instructions traced). Tools: the selected-code binder and `mkset.py` refuse Rust symbol names
and two symbols with the same last component. Per function the hand-written data was one
contract of 79 to 143 lines (and loop designs for set B); setup took 40 to 70 minutes per set
once the traces existed. No set exercises calls.

**Second held-out batch (amendment 15), BASELINE on main's unrepaired generator (2026-11-22;
17 untested functions, 255 blocks; `_build/agents/rebuild/heldout3/SELECTION.md`,
`i/` to `v/RESULT.md`):**

|Group|Functions|Blocks|Closed|Reach the prover|Refused at render or caller not rendered|
|---|---|---|---|---|---|
|i: single loops|`getIndex`, `blockHashDbFn`, `getOrPutAssumeCapacityAdapted`|47|0|0|47|
|ii: nested loops, joins in loops|`mergeInPlace`, `mem.rotate` (48-byte elements), `updResolveRefExIndexed`|85|0|1 (open)|84|
|iii: branchy code, several returns|`opJumpi`, `opSlt`, `scratch_arena.remap`|34|0|0|34|
|iv: arithmetic, very long blocks|`opExp`, `opSignextend`, `opSar`, two Rust byte conversions|49|0|0|49|
|v: functions with calls|`isCold`, `isAddressColdFn`, `makePushFn`|40|0|0|40|
|Total||255|0|1|254|

Every cause is owned by generator code; all 2,584 new instructions traced. Recurring stops:
(1) NEW and the most widespread (observed in 11 of the 17 functions): a pointer LOADED FROM OWNED MEMORY
(a struct field, a context cell) is not linked to the region it points to, although the
contract states the link; every access through it is an unknown read (repair lane `gen/ptr`).
(2) The region fork and path limit (repaired on `gen/fwd`); in two single-block Rust functions
the forward pass itself runs out of 16 GiB. (3) Loops: no computed design, nesting (repaired on
`gen/loop`); new variants: several inner loops in sequence inside one outer loop, and a loop
register that is an index masked by the capacity, not a pointer cursor. (4) Return packages for
functions with several returns (in work on `gen/all`). (5) NEW, calls: a call specification
cannot describe callee memory at a negative offset or behind a stored pointer; a callee output
of variable length is refused (no lane yet). One fixed-size memcpy call site passed the forward
pass. Hand data per function: one contract of 117 to 254 lines, 10 to 30 minutes each. The
measurement on the repaired generator reuses the same setup unchanged.

**Second batch on the REPAIRED generator (`gen/all` f6b6c111d: factored join guards, forward
merge with a per-block budget, natural loops with inferred designs, generalised return
packages, link following, tools fixes; the three developed functions render byte-identically;
setups unchanged, natural domains, nothing fixed; `heldout3/<group>/r/RESULT.md`):**

|Group|Blocks|Entries rendered: baseline -> repaired|Reach the prover|Closed|
|---|---|---|---|---|
|i: single loops|47|4 -> 3|0 -> 0|0 -> 0|
|ii: nested loops|85|8 -> 14|1 -> 4|0 -> 2|
|iii: branchy code|34|2 -> 5 (one function's render ran out of 24 GiB)|0 -> 1|0 -> 1|
|iv: arithmetic, long blocks|49|0 -> 2|0 -> 0|0 -> 0|
|v: calls|40|0 -> 0 (one render stopped at the 30-minute cap)|0 -> 0|0 -> 0|
|Total|255|14 -> 24|1 -> 5|0 -> 3|

Reading: every baseline first stop is gone in every group (links followed, nested loops found,
designs inferred, return packages generalised, no path limit in the prologues), and the
generator then stops a few instructions later. What stops it now, all generator code unless
noted: (a) in all five groups, the FREE-INPUT and ZERO arms of a load: with data allowed
anywhere in the readable range a load really can return device input or 0, so these arms are
genuine alternatives that no merge removes (contract data: whether callers guarantee valid
memory is a domain question); (b) indexed access into an array of symbolic length or through
a masked or ranged index (stack top `data + 32*len - k`, hash probe `key & (cap-1)`, a loop
index without a range, a bitset index into a stack copy): the generator places only
`base + closed offset` and strided cursors; (c) links it does not follow: 32-bit words,
conditional (null-or-address) pointers, fields inside a folded resource definition, and the
entry formatter cannot render a word cell; (d) an inner loop whose cursor is the outer loop's
variable; a second entry edge into a loop head from the zero arm; (e) call specifications
(callee memory at a negative offset: now confirmed at a reached call site); (f) cost: forward
passes of 20 to 24 GiB and `FORWARD.json` of 2 to 8 GB where stopped paths keep full states,
single blocks of 157 and 413 instructions that no boundary merge helps, a 247 KB join guard
whose contradiction checks take 150 s each; (g) one crash in the entry renderer. First
prover-side finding: an inferred loop-head entry asks for the saved-register frame as one
array while the block holds cells. The three closed blocks are short straight-line ones; no
block with a never-used mnemonic reached the prover, so the rule library is still untested on
this code.

**Diagnostic column: the same run with ONE contract change (the pointers the code reads through
are stated to lie in RAM; coordinator's addition, labelled, does not replace the table above;
`heldout3/<group>/d/RESULT.md`):**

|Group|Blocks|Entries: natural -> RAM|Reach the prover|Closed|
|---|---|---|---|---|
|i: single loops|47|3 -> 3|0 -> 1|0 -> 0|
|ii: nested loops|85|14 -> 8|4 -> 2|2 -> 1|
|iii: branchy code|34|5 -> 7|1 -> 2|1 -> 0|
|iv: arithmetic, long blocks|49|2 -> 12|0 -> 4|0 -> 0|
|v: calls|40|0 -> 18|0 -> 4|0 -> 0|
|Total|255|24 -> 48|5 -> 13|3 -> 1|

Reading: the clause removes stop (a) everywhere it applies and with it most of cost (f): forward
passes go from minutes and 6 to 24 GiB to seconds, a join from 142 alternatives and 245 KB to 5
and 27 KB, the two single-block Rust functions render. Behind it: (1) the entry renderer
CRASHES on a boundary with no alternatives or whose alternatives are all refuted (two code
sites); that one bug hides 81 blocks in three functions and is why two counts go DOWN;
(2) stop (b), indexed access, is confirmed as the next generator stop in groups i, ii, iii, iv
and v, and the RAM bound does not reach a computed address, so impossible arms survive there;
(3) for the first time blocks reach the prover in every group; of the 13, one closes; the open
ones end on: a loaded pointer or a store through one with the pointer's range and link only
inside the sealed domain fact (the held-out contracts have no instance exposing ranges and
links as plain facts, which every developed function has: contract data; 4 blocks); a missing
range clause (1); the first call step on unseen code: callee domain needs a caller-level lemma
and the frame after the call is spelled two ways (1); lookup and word-spelling goals of the
classes decodeParentHeader had (2); entry statements that spell a frame as one array or a
stored word as byte cells against what the block holds (2); two single blocks of 157 and 413
instructions killed at 1,200 CPU-s with successor packages of 86 and 212 KB (statement size).
No block with a mnemonic the developed functions never used has reached the prover yet.

On main:

- decodeParentHeader is in its final layout of 98 blocks (exit design A, amendment 11); **79 are
  certified**;
- `parentHeaderGeneratedCompliance : ParentHeaderOpenBlocks -> ParentHeaderExitMeanings ->
  ParentHeaderContractCorrect`, closed under the global context, with no callee premise;
- nextUint64 fully proved (`nextUint64Compliance`, no premise);
- the candidate agrees with Sail outside the registered known bugs
  (`candidateParentHeader_sail`, no premise);
- decodeItem rendered by the one generator driver; its sweep total is about 44,200 G
  instructions (51,100 G at the Automation gate).

**Automation gate (end of Phase 1) on `7cc359d1a`:** static 0; check-iris 0; decodeItem sweep 24
of 24 at -0.05%; check-fast 0; BENCH-v1 14 of 16 (the two open are decodeParentHeader 0000 and a
return slot); free 39 of 39; berlinGasCalc 9 of 9; PH-ALL 58 of 90, exactly the 58 certified;
NU-ALL 9 of 10. Acceptance lists: 1.1 holds; 1.3 holds (at least 8 of 10); 1.5 holds (0300 87
CPU-s, 0040 85, the eleven call blocks 195 to 470, measured under load); 1.6 holds except the
soundness gate, which waits for the user's baseline decision (a run with a scratch baseline
passed every stage). Three findings, each with a PR or lane: nextUint64 0000 was killed at the
2,400 CPU-s limit under load (it needs 11,200 G instructions; #333 brings it to 5,126 G);
berlinGasCalc's closed set costs 2.3 times more since step 1.6 (the boolean half of the join
guard fact; #334 adds the profile key that removes it); the return slots 2 and 4 reach the
16 GiB limit (fix on `rb/perf`, in batch 3). Reports: `_build/agents/rebuild/gate-phase1/`,
`gates-p1/`.

Since the gate, each after its gates: #333 and #337 (generic cost fixes: nextUint64 0000 at 0.46
of its instructions, decodeParentHeader 039c at 0.56; decodeItem sweep -3.43% and -4.58%); #334
(generator key; berlinGasCalc's closed set back to its earlier cost: 8,651 G instructions against
19,752 G); #335 (rule batch 3: 68 of 90 certified); #336 (0570, 04b0 close); #339 (0000, 0068
close); #340 (exit design A; full cycle on `89596cc59`: static 0, check-iris 0 in 38 min, sweep
24 of 24 at +0.01%, check-fast 0 with check-signatures, BENCH-v1 15 of 16, free 39 of 39,
berlinGasCalc 9 of 9). Lanes running: certificates for the four blocks; the return blocks
(`rb/retb`); the seal step and word spellings (`rb/word`, replaces the held #338); M1 stacked on
exit design A (`rb/m1s`). Open for the user: the soundness gate's baseline (see below).

| Step | State | Where |
|---|---|---|
| 0.1 tracking issue | done | #316 |
| 0.2 preserve prototypes | done | `~/zesislar-archive/research-2026-11-19.tar.zst` |
| 0.3 land `ew/exit-witness` | **merged** as `113146e09` with five guard commits. Gates on `285be8eab`: static 0, check-iris 0 (33 min), decodeItem sweep 24 of 24 at +1.93% instructions, check-fast 0, free 39 of 39, berlinGasCalc 9 of 9, BENCH-v1 9 of 15 (same nine as the base) | PR #317; `_build/agents/rebuild/gates-ew2/` |
| 0.4 first bank | done; the bank of main is the kept bank of the latest gate run (`ff43d1f84`, same tree as main `8d76074ce`); base bench run `_build/agents/bench/v1-ff43d1f84-12b`, base sweep tag `rb-12b` | `_build/agents/rebuild/recipe-main.json` |
| 1.1a to 1.1e rule library | **merged** (#319 to #323, main `bb899bec4`) after one full gate cycle on the top `5b25e48be`: static 0, check-iris 0 (32 min), decodeItem sweep 24 of 24 at -6.44% instructions, check-fast 0, free 39 of 39, berlinGasCalc 9 of 9, BENCH-v1 11 of 16 against 9 (decodeParentHeader 00ec and nextUint64 00a4 are new) | `_build/agents/rebuild/gates-11/` |
| 1.4 budgets and triage | **merged** as `d56b50a4b` (static 0, check-fast 0, tools tests pass); BENCH-v1 now caps `0514_slot0` at 1,200 CPU-s | PR #318 |
| 1.2 generator and history library | **merged** as `8d76074ce` (#324) after a full gate cycle on `ff43d1f84`: static 0, check-iris 0, decodeItem sweep 24 of 24 at -0.06%, check-fast 0, free 39 of 39, berlinGasCalc 9 of 9, BENCH-v1 11 of 16 (same set as before). Measured on sealed entries before the merge: decodeParentHeader 0300 77 CPU-s, 0040 69, call blocks 00ec to 0448 close at 133 to 321 with no growth in call number. Left open: 7 edge files over 60 CPU-s (shape of the loop-class history; optimization item) | `_build/agents/rebuild/gates-12b/`, `1.2f/HANDOFF.md`, `1.2s/DESIGN.md` |
| 1.3 switch nextUint64 | **merged** as `8544287f5` (#325): static 0, check-iris 0 (10 min), check-fast 0. 5 of 10 blocks close on the sealed entries; the rest is step 2.2 | `_build/agents/rebuild/notes/1.3-HANDOFF.md` |
| 1.5 switch decodeParentHeader | **merged** as `455eaf43b` (#327): static 0, check-iris 0 (11 min), check-fast 0. 37 of 90 blocks closed and certified (7 before), none of the 7 lost; anchors: 0300 63 CPU-s, 0040 65, call blocks 150 to 326 flat in call number. 53 open, triaged: over cap 15, call 13, spatial existential 12, lookup 9, word order 2, fault 1, witness 1 | `_build/agents/rebuild/notes/1.5-HANDOFF.md`, `1.5-blocks.md` |
| 1.6 decodeItem on the new path | **merged** as `7cc359d1a` (#332): static 0, check-iris 0 (32 min), check-fast 0, decodeItem sweep 24 of 24 at -0.20%. One driver run renders decodeItem (50 files, 24 callers); the legacy generator path and the old producers are removed; the committed entries keep their text except one join entry; compliance theorem assumptions equal to before. Renders of the other two functions byte-identical under the merged generator | `_build/agents/rebuild/gates-16/`, `gates-16g/`; `notes/1.6-HANDOFF.md` |
| 2.1 contract PR | **merged** as `50da8ef9a` (#330): static 0, check-iris 0 (45 min), check-fast 0 with check-signatures. Domain with `headerFits`, candidate function pinned to the emulated binary, ten known-bug classes with boolean triggers and computed witnesses for every row of the divergence tables, meaning "exact candidate result, then Sail agrees or a registered trigger fires". `parentHeaderError80` constrains only the two bytes the error exit writes | `_build/agents/rebuild/gates-21/`; `2.4m2/DIVERGENCES.md` |
| 2.2 nextUint64 | **done.** #326 merged as `d9251d18d` (ten blocks certified, open-block record empty); #330 removed the last premise: `nextUint64Compliance : NextUint64ContractCorrect`, assumptions closed under the global context; registry row `proved` | `_build/agents/rebuild/gates-22d/`, `gates-21/` |
| 2.3 decodeParentHeader blocks | **75 of 98 certified on main** (final layout, #340). Closing with main's rules, certificates in work: 0000, 0068, 0570, 04b0 (-> 79). Open: the seven return slots `0274_slot0..6`, 0270, 03bc, `0514_slot0..4` (lane `rb/retb`: unsealed request for the error tag, stored word cells against byte-array requests, a frame-order goal, large result-byte terms in slots 2 to 6); 048c, `0510_slot0`, `0510_slot1` (close with the guarded seal step) and 046c, 04f8 (one history goal each: the same word in two spellings) on `rb/word`, which replaces the held #338 (that PR's rules stopped 0570 and 04b0 from closing). Exit side on main: eight end bridges in their own modules (29 to 533 s), composition about 19 minutes (optimization item) | `rb/cert4`, `rb/retb`, `rb/word`; `_build/agents/rebuild/gates-ea/`; lane notes under `_build/agents/rebuild/notes/` |
| 2.4 meaning | **M2 merged** (#331). **M1**: pure side and generator side on `rb/m1g` (walk and reach invariants, terminals; error joins carry the candidate-error fact; per-edge obligations as generated declarations, all proved by one tactic; loop fold facts carried to the blocks before the return; success terminal over an explicit byte list). Now being stacked on exit design A (`rb/m1s`): merge, re-render, edge obligations of the 98-block layout, one reusable lemma from "the result is the candidate's" to the contract meaning (case split on the triggers, then `candidateParentHeader_sail`), and the two error exits' meaning premises discharged. Next leg: fold facts into the success return packages and the six success exits; then `ParentHeaderExitMeanings` is empty | `rb/m1s`, `rb/m1g`; `_build/agents/rebuild/notes/m1g-HANDOFF.md`, `notes/m1g-DESIGN.md`, `notes/M1-LOOP_FACTS.md` |

Measured by the gate cycle on the merged rules (against the base before step 1.1): every BENCH-v1
block the base closes still closes; decodeParentHeader 00ec and nextUint64 00a4 close for the first
time; the decodeItem sweep is 6.44% cheaper; nextUint64 closes 7 of 10 unchanged callers.

Open decisions for the user:
1. The soundness gate's baseline. `tools/soundness_gate.py` stops before building, on main too:
   its fixed baseline (`0140e6874`) predates three lines main added to
   `ZesuSsz/Evidence/SignatureGates.v` (the None-constant contract change of 2026-11-13), and the
   approved 2.1 PR changes that file again. Moving the baseline is a reviewed trust decision;
   proposed: one move after 2.1 merges. The 1.6 integration lane reports the protected-file diff
   and a diagnostic run with a scratch baseline.
2. Optional: raise the account's memory cap (152 GiB live) with
   `sudo systemctl set-property user-1000.slice MemoryMax=240G`.

Settled: `parentHeaderError80` constrains only the length and bytes 72 and 73, the two bytes the
error exit writes; the statement is true for the binary.

## Amendments

1. **2026-11-19, step 0.3: the exit-witness branch was not a sound base.** `make check-iris` at
   `b88218565` failed on nine production decodeItem callers and one rule test. Three rules of that
   branch matched shapes they must not take; five guard commits fix them (head `285be8eab`). The
   lane measured 24 of 24 decodeItem callers closing, +2.0% instructions against main; four callers
   are 16 to 21% dearer through the mask-witness rule (optimization item).
2. **2026-11-19, gates (user-approved): gates run by what a PR changes, not all five on every PR.**
   See "Which gates a PR needs" under Operating rules. The steps 1.1a to 1.1e get ONE full cycle on
   the top of the stack and merge together. `0514_slot0` in BENCH-v1 is capped at 1,200 CPU-s once
   step 1.4's per-member cap is on main (it cannot close before step 2.3 and took 60 of the 63
   minutes of a BENCH-v1 run). Within a cycle the order is static, check-iris, decodeItem sweep,
   check-fast, BENCH-v1, with the closed sets alongside.
3. **2026-11-19, ordering.** Lanes were started as soon as their inputs existed, not at the phase
   boundaries of this plan: 1.4 and 1.2 before 0.4; the 2.1 drafts, the 2.2 meaning module and M2
   before the automation gate. Nothing merges out of order.
4. **2026-11-19, step 1.1 acceptance.** Met on the stack: closed set kept, 00ec closes, nextUint64 7
   of 10. Not met and recorded as optimization items: 0300 runs at 0.84 of base instructions (the
   prototype itself measures 0.80 on this base; the plan's 290 CPU-s came from an older base);
   nextUint64 00b8 peaks at 3.05 GiB against 3 (it runs further than before and ends on an ordinary
   goal of step 2.2). Wiring deviations: the call step is its own alternative in
   `zesu_run_pass_v1` (no hook: the hygiene check refuses the redefinition); `liImpl` poses ranges
   only when the introduced premise is a registered domain; the block tail is a declared-default
   project hook with an explicit hygiene allowlist.
5. **2026-11-19, step 1.2: sealed-entry shape redesigned from measurements.** Item 1.2-7 as written
   (a visible group at joins holding every regex-visible fact) made blocks slower than the
   prototypes (0300 reached the 1,200 CPU-s cap). New shape: visible facts are derived (domain,
   lengths, the latest call's record, guards, window and named register equations; loop-design
   facts); a join hides everything it drops in one history group; return sites state the call's
   slice window (contingency C3, now part of the design); edges derive and reveal successor facts
   from the source history. Measured on a bank with all rules and the history library: 0300 70
   CPU-s, 0040 68, 026c 23. Call blocks on the new entries are being measured.
6. **2026-11-19, step 1.6: the "empty diff" expectation does not hold.** decodeItem's committed
   entries come from four producers reading frozen sources; the new driver cannot reproduce them
   yet (six driver changes listed in `DECODEITEM_1_6.md`), and with every fact visible each entry
   still gains a history binder. Options are brought to the user when Phase 1 reaches 1.6; the
   plan's contingency (leave decodeItem on the legacy path by changing 1.6 only) stays available.
7. **2026-11-19, step 2.1-2.4 findings.** The drafted triggers do not cover every divergence
   between the binary and Sail (amendment to the 2.1-4 table pending the user's decision). M2 is
   split into a Sail-model premise (proved) and a trigger-coverage premise (open).
8. **2026-11-20, rocq-mcp (user instruction).** Lanes use rocq-mcp, the primary proof tool of
   `AGENTS.md`, for every lemma, tactic, test, contract proof and bridge they write or repair
   (`rocq_health`, `rocq_start`, `rocq_check`, `rocq_step_multi`, `rocq_compile_file`, `rocq_verify`,
   `rocq_assumptions`), and report those results. The harness had no rocq-mcp server connected; the
   coordinator now passes two bridge tools (`rocq_mcp`, `rocq_mcp_tools`) to every Rocq task, one
   server per worktree (`_build/agents/rebuild/rocq_bridge.py`, usage in
   `_build/agents/rebuild/ROCQ_MCP.md`), and `.omp/mcp.json` registers the server for the harness
   itself (active after `/mcp reload` or in a new session). Measured block runs (CPU-s, peak memory,
   caps) stay on `run_coqc.sh` and `bench.py`. This replaces the sentence "Development probes use
   the research runner" where it excluded rocq-mcp.
9. **2026-11-20, step 2.2: a caller's exit meaning may use its callee's meaning link (provisional,
   to be confirmed by the user).** `decodeItemCallMeaningLink` is tagged `exit_composition_only`, and
   the hygiene check refused it everywhere outside decodeItem's own interface modules, so no caller
   could prove its exit meaning from its callee's. New registry field `exit_meaning_modules` per
   caller in `Contracts/proved_functions.json` lists the modules that may use the
   `exit_composition_only` links of the callees named in the row (nextUint64:
   `Contracts/NextUint64ExitMeaning.v`, callee decodeItem). Everything else stays refused: the
   link in an unlisted module, any other sealed callee name, a link of a function not in the row,
   and a listed module with `Ltac`, hints, proof-mode sentences or an automation umbrella import.
   Step 2.4 (M1) needs the same for decodeParentHeader.
10. **2026-11-20, step 1.3 acceptance.** 5 of 10 nextUint64 blocks close on the sealed entries, not
   the planned 8: the other five are step 2.2 work (three rule gaps, two contract lemmas). The bench
   set gives 0000, 0070 and 00a4 explicit caps above the formula.
11. **2026-11-20, user rulings.** (1) Exit design A: decodeParentHeader's exit blocks end at
   generated machine-return entries (one return package per slot of the duplicated return block;
   the memcpy tail join's package for the tail calls), and end bridges in the composition prove
   the unchanged contract continuation from them; the meaning of each exit kind is an explicit
   premise of the composition theorem until step 2.4 discharges it. Section 2.3's rows for the
   memcpy tail calls and the return slots change accordingly: no frame-fold lemma and no
   exit-witness step at the blocks. (2) Amendment 9 is confirmed. (3) Step 1.6 is done in full
   now. (4) The 2.1 drafts are approved as drafted. (5) The trigger set of `DIVERGENCES.md` is
   approved: `ParentHeaderSkippedFieldShape`, `RlpUintNonCanonical` and
   `ParentHeaderBlobGasUnaligned` widened; `ParentHeaderUndecodedFieldRejected` and
   `ParentHeaderUintOver8` narrowed; new classes `ParentHeaderExcessBlobGasAboveLimit` and
   `ParentHeaderTrailingItemMalformed`. This replaces the trigger table of step 2.1-4.
12. **2026-11-20, resources (user).** This project is the only consumer of the machine. The cap
   of 6 lanes is lifted; lanes started ahead of their inputs' merges on stable commits: M1 (walk
   invariant and step lemmas) and M2 (trigger coverage) on the approved contract branch, block
   00b0 on the exit-design branch, the return-slot memory profile on batch 2. Gate cycles may
   overlap. The account's memory cap is still enforced by the system at 152 GiB (not the 200 GiB
   `AGENTS.md` names); raising it needs root.
13. **2026-11-20, step 2.4 M1: how the error exits get their meaning.** Plan item 1.2-7 said error
   joins take a per-edge reason fact. Chosen form (coordinator, from the M1 lane's proposal): every
   edge into an error join (0088, 00a8, 0408, 026c, 0270, the tail join 00b0) carries one fact
   without edge binders, `candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError`,
   derived from the edge's source history; the join keeps it, join-to-join edges pass it on, and
   the error exit's meaning follows from it and the stored tag bytes. Each edge's derivation is an
   obligation the generator renders as a declaration (`<src>_<join>_CandidateError`), proved in a
   hand-written module by one tactic and used by the rendered edge instance (rule F42). The
   M1 lane's 36 edge lemmas are sound but were written by an uncommitted template over copied
   binder lists; they are replaced by this form before anything merges. The loop classes of the
   three inline integer fields gain a fold invariant (`notes/M1-LOOP_FACTS.md`). No reviewed
   statement changes. M1 uses a second invariant the plan did not name, `candidateWalkReach`
   (the walk stands at field k or the candidate already rejects), so an error edge needs no facts
   about earlier fields.
14. **2026-11-21, step 2.4 M1: the success exits carry the walk, they do not rebuild it.** The
   plan's M1 proves each exit from the exit's history as a chain of step lemmas. Measured on the
   success return packages: the histories hold the call records but not the guards that decide
   whether the walk went on (the status of each skipped call, the "something left" checks, the
   list bit and the 8-byte bound of the inline integers): the call-return entries drop them, as
   they dropped the fold facts; and one join merges paths that stop at different fields. The
   chain at the exit therefore needs facts no exit holds. Chosen form (coordinator, extending
   amendment 13): the walk invariant itself (`candidateWalkReachValues`: the candidate rejects,
   or the walk stands at field k with these values) is a design fact of each return site and
   join on the success path; each edge proves ONE step from its source's fact, its own guards
   and its call record, as a generated obligation declaration proved by a one-line use of the
   step lemmas (rule F42); the success return packages then hold the final walk fact and their
   `_ExitMeaning` fields follow from the terminal lemmas, `parentHeaderSuccessBytes` and
   `parentHeaderMeaningOfCandidate`. No reviewed statement changes. Proved so far without this
   data: slots 1 and 4 end to end from two explicit hypotheses (the third fold fact and "the walk
   accepts with three values"), which this design supplies. As built (first segment, `rb/m1x`):
   the carried fact is a definite state (`parentHeaderWalkAt`: the walk state plus "something
   left"), not the "rejects or stands" form, because that form can step without using a guard
   and would leave "rejects or accepts" at the exit; the only holders are the return sites of
   the field calls. Measured on the nine skipped fields: nine obligations, each one line by one
   tactic; all 30 blocks of the segment still close; +0.85% instructions in total, one block
   +5.1% (a premise class that grows with the call number; being narrowed).
15. **2026-11-22, generator repair and a second held-out batch (user decision).** The held-out
   measurements (Status) show the generator, not the rule library, stops most blocks of unseen
   functions. Added to the plan as Phase 3, in parallel with the end of Phase 2:
   (a) generic generator repairs, one lane per area, on branches `gen/*`: joins (the quadratic
   guard fact of wide joins; joins that drop a linking fact), the forward pass (the fork of every
   load on the memory region and the global path budget; return packages for functions with
   several returns), loops (nesting, cursor width, computing the structural part of a loop
   design), tools (Rust symbol names, bench set lookup, interface inputs, leftover export, triage
   classes). A repair is generator code or a generic default with unit tests; it needs no
   per-function data on a new function, and the renders of the three developed functions stay
   byte-identical (old behaviour pinned in their profiles where a default changes).
   (b) The repairs are NOT judged by making the held-out sets A, B, C close; those sets serve as
   reproductions of each stop at render level only. They are judged by a second batch of
   untested functions (14 to 18 in five groups: loops of several kinds, nested loops, wide joins
   and dispatch, long arithmetic blocks, functions with calls and larger frames), selected and
   traced now (`heldout/sets3-base`, `_build/agents/rebuild/heldout3/`), rendered and run once
   the repairs exist. Reading protocol as for sets A to C (failures read and classified by owner,
   nothing fixed during the measurement). hpDecode and resumeCall stay unread.
   (c) Merging: each `gen/*` branch is a tools-only PR (static, check-fast, tools tests, and the
   three developed renders checked byte-identical) after the decodeParentHeader integration
   branch has merged.

## Context

Ask: build the block-proof automation that four measurement rounds derisked, then prove it out on
`rlp_decode.decodeParentHeader`. End state:

1. The rules and the generator changes are on `main` through the gates of `AGENTS.md`.
2. `ParentHeaderContractCorrect` is proved with no open-block premise and no callee premise. That
   needs every decodeParentHeader block closed, its callee `rlp_decode.nextUint64` proved
   (10 blocks, composition, meaning), and the decodeParentHeader meaning proved modulo registered
   known bugs.

User decisions already taken (2026-11-19): narrow the decodeParentHeader precondition with the
outer `headerFits`; register the binary-against-Sail divergences as `KnownBug` classes, drafted
here and reviewed by the user; allow generator-rendered proof scripts for history-edge lemmas only
(amend `AGENTS.md`); move decodeItem to the same generator mode.

Evidence behind every number below: `/home/cody/zesislar/docs/AUTOMATION_MEASUREMENT_ROUND_2026-11-18.md`
(sections 1 to 7). Read it before starting. Prototype sources are under
`/home/cody/zesislar/_build/agents/researcher/` (called `R/` below); each lane dir has `RESULT.md`.

## Operating rules

These bind the coordinator that executes this plan.

- **Paths.** The main checkout `/home/cody/zesislar` sits on an old commit (`f770a317e`); never build
  there. Every lane works in its own worktree `.worktrees/rb-<lane>` on branch `rb/<lane>`, created
  from current `origin/main`. Coordinator files go to `_build/agents/rebuild/`.
- **State.** Keep `_build/agents/rebuild/STATE.md`: one row per step of this plan (step id, branch,
  PR, status, last measurement path). Update it at every merge and every lane report. Append one
  line per merge to `docs/ai/STATUS.md` (existing convention).
- **Agents.** Proof, rule and generator work: agent type `task` (Opus 5.5). Running gate scripts,
  bench runs, re-renders, tabulation: agent type `sonic` (Haiku 5.5), with the exact commands in the
  brief. At most 6 lanes at once. Every brief states: lane dir, question, acceptance, request
  budget (at most 120), "write `HANDOFF.md` at 100 requests", the limits below, and "for every
  addition name its owner: generator data, generic rule, contract fact".
- **Probe runs** (development only): `R/run_coqc.sh <abs file.v> [mem_gib=6] [cpu_s=600]` and
  `R/run_seq.sh`, with `RESEARCH_RECIPE=<recipe.json of the lane's bank>`. Limits per run: 8 GiB,
  1,200 CPU-s; 3 concurrent per lane; the runner itself caps the total at 12 and keeps 25 GiB of
  account headroom. Non-coqc tools that can grow: `R/run_scoped.sh <mem_gib ≤ 24> <cmd…>`.
  A cap is a result; at most 3 full runs of one statement without a change (`AGENTS.md`).
- **Banks.** A bank is the kept build of one commit: `python3 tools/bench/bench.py run --set <set>
  --head <sha> --run-dir <dir> --keep-bank` (the bank path is in `<dir>/RUN.json`, key `bank`).
  Make its recipe with:
  ```sh
  python3 - <<'EOF'   # args: a measure.json of that run, the bank worktree, the output recipe
  import json,sys; m,w,o=sys.argv[1:4]; d=json.load(open(m)); c=[x for x in d['command'][:-1] if x!='-time']
  i=len(c)-1-c[::-1].index('-o'); c=c[:i]+c[i+2:]
  json.dump({'cmd':c,'cwd':d['cwd'],'env':d['environment'],'bank_worktree':w},open(o,'w'),indent=1)
  EOF
  ```
  Hold each bank in use with a named background service whose cwd is the bank's `default/`
  directory (`exec tail -f /dev/null`); the janitor removes unused detached bench worktrees after
  6 hours.
- **Budgets per block.** CPU cap `min(1200, 120 + 45 × instructions)`; explicit 2,400 for the blocks
  listed in step 1.4. A block over its cap is class `OVER`: its next action is the stepping-only
  probe (step 1.4), never a tactic optimization. Tactic optimization is allowed only on blocks that
  already close.
- **The five gates** (run from the PR's worktree at its exact head with
  `_build/agents/rebuild/gates.sh WORKTREE BRANCH SHA TAG`; `GATES=` selects a subset). Which of
  them a PR needs is in the table after the list:
  1. static: `python3 ZesuSsz/Evidence/check_proof_hygiene.py && python3
     ZesuSsz/Evidence/check_release_imports.py --umbrella ZesuSsz.Automation2.All && python3
     ZesuSsz/Evidence/check_spec_shapes.py && python3 tools/block/check_proved_functions.py &&
     (cd tools && python3 -m unittest test_import_invariance)`;
  2. `make check-iris CHECK_AGENT=rb-iris-<tag>` and `make check-fast CHECK_AGENT=rb-fast-<tag>`
     with `TMPDIR=/home/cody/.cache/orch-checkfast-tmp` and
     `PATH=/home/cody/.local/bin:/home/cody/islaris/_opam/bin:/usr/local/bin:/usr/bin:/bin`,
     `OCAMLPATH` unset, one heavy build at a time;
  3. decodeItem sweep: `tools/sweep_decodeitem/bank.sh rb-<tag> _build/agents/rb-<tag>` then
     `tools/sweep_decodeitem/sweep.sh rb-<tag> _build/agents/rb-<tag>/bank
     tools/block/generated/fp301_callers`; pass = 24 of 24, total `instructions:u` reported by
     `tools/sweep_decodeitem/sweeptable.py` against the previous main sweep;
  4. closed sets: `/home/cody/zesislar/_build/agents/heldout-render/closedcol.sh <sha> rb<tag>
     <branch>`; pass = free 39 of 39 and berlinGasCalc 9 of 9;
  5. `python3 tools/bench/bench.py run --set BENCH-v1 --head <sha> --run-dir
     _build/agents/bench/v1-<sha>-<tag>` and `bench.py report <run> --base <previous main run>`;
     pass = no block closed in the base is lost.
- **Which gates a PR needs** (amendment 2; replaces "all five on every PR that touches
  `Automation2/`, `Contracts/`, `InstrSpecs/` or `Export/`"). `AGENTS.md` itself requires
  `check-fast` before every merge and a full `check-iris` before merging a change to
  `Automation/`, `Automation2/`, `InstrSpecs/`, `Contracts/` or `Export/`. The decodeItem sweep's
  24-of-24 verdict duplicates `check-iris` (same callers); the sweep, BENCH-v1 and the closed sets
  are needed only when rules change: for cost numbers, and for proofs that are not on main.

  | PR changes | Gates |
  |---|---|
  | rules (`Automation2/`, `InstrSpecs/`) | full cycle: static, check-iris, sweep, check-fast, BENCH-v1, closed sets |
  | tools only | static, check-fast, the tools tests it touches |
  | profiles, generated entries, callers, certificates | static, check-iris, check-fast, the function's bench set (NU-ALL, PH-ALL) |
  | decodeItem entries or composition (step 1.6) | static, check-iris, check-fast, decodeItem sweep, soundness gate |
  | contracts, compliance proofs | static, check-iris, check-fast; plus `check-signatures` when a reviewed statement changes |

  Full cycles therefore run for: step 0.3; the 1.1 stack (once, on `rbs/1.1e`); each batch of new
  generic rules in Phase 2 (batched, not per rule); the final verification. Risk accepted with the
  stack: intermediate commits of 1.1a to 1.1e are not individually proven by `check-iris`; if the
  top fails, the per-step bank measurements of the lanes locate the step.
- **PRs.** One PR per step id below, each referencing the tracking issue of step 0.1; merge after
  its gates; then `tools/cleanup_after_merge.sh <branch>`. Rebase open lanes on main after each
  merge. `ZesuSsz/Automation2/Hooks.v` and `Finish.v` are edited by several steps: the coordinator
  merges those PRs strictly in the order of this plan and the later lane resolves conflicts. The
  five PRs of 1.1a to 1.1e are opened as a stack and merged together, in order, after the one cycle
  on the top of the stack.
- **Rule form** (`AGENTS.md`): a generic rule names no machine address, offset or contract
  predicate; anything function-specific is a contract lemma or a typeclass instance in
  `ZesuSsz/Contracts/`. Every new rule gets a test file in `ZesuSsz/Proofs/Tests/` that fails
  without it, and every new guard a test in which both branches fire. No `Ltac … ::=` of a Lithium
  or isla hook outside `ZesuSsz/Automation2/Hooks.v`. Project tactics that a later module must
  extend use the existing two-step pattern of `Automation2/LiaHook.v` (`Ltac zesu_lia := lia.`)
  and `Hooks.v` (`Ltac zesu_lia ::= …`): declare a default hook tactic in the early module and
  redefine it once in the later Automation2 module.
- **Stop and ask the user** only for: review gate 2.1; a contract statement found false (not a
  generated entry: those are generator defects); the contingency of step 2.4.

## Approach

### Phase 0. Base

**0.1 Tracking issue.** `gh issue create --title "Block-automation rebuild and decodeParentHeader
prove-out" --body-file` this plan's Context. Every commit carries `(ref #<n>)`.

**0.2 Preserve the prototypes.** Write `R/KEEP.json` = `["."]`. Archive the sources:
`tar --zstd -cf ~/zesislar-archive/research-2026-11-19.tar.zst --exclude='*.vo*' --exclude='*.glob'
--exclude='*.log' -C /home/cody/zesislar/_build/agents researcher`.

**0.3 Land the measured rule base.** All measurements ran on `origin/main` (`f949c6ec3`) plus the
branch `origin/ew/exit-witness` (head `b88218565`, 6 commits, pushed, clean). Open a PR for that
branch unchanged, run all five gates, merge. Its BENCH-v1 result must match
`/home/cody/zesislar/_build/agents/bench/v1-ew2a` (9 of 15 closed; 0514_slot0 not run there) or
better; that run becomes the base for every later `bench.py report --base`.
`origin/orch/call-window` is not merged (see contingency C3).

**0.4 First bank.** Bench run of BENCH-v1 at the new main with `--keep-bank`; make its recipe
`_build/agents/rebuild/recipe-main.json`; start its keeper service.

### Phase 1. Build the automation

Lanes 1.1a to 1.1e, 1.2 and 1.4 start in parallel after 0.4. Merge order: 1.1a, 1.1b, 1.1c, 1.1d,
1.1e, 1.4, 1.2, 1.3, 1.5, 1.6.

#### 1.1 Rule library (ports of measured prototypes into `ZesuSsz/Automation2/`)

Port the tactic and lemma text from the named prototype file, renaming the lane prefixes (`wf_`,
`cs_`, `le_`, `sp_`, `at_`, `ls_`) to `zesu_`, deleting `idtac "@@…"` markers, and replacing each
prototype `Ltac X ::= …` override by the wiring in the last column. Prototype paths are under `R/`.

| Step | Rule | Prototype source | Destination and wiring |
|---|---|---|---|
| 1.1a-1 | Linked-facts closer refuses `div`/`mod` by a non-numeral; a `Z.pow` of two numerals counts as a numeral | `regress3/lib/PreludeXC.v`, override of `LinearFirstLia.zesu_lia_linked_facts` and its `probe_numeral` | Edit `Automation2/LinearFirstLia.v`, `zesu_lia_linked_facts` (line 292), in place |
| 1.1a-2 | `unLET` clears unused local definitions first | `regress3/lib/PreludeXC.v`, overrides of `isla.base.unLET` and `Hooks.zesu_unlet_preserving_witness_metadata` | Edit `Automation2/Hooks.v` (`zesu_unlet_preserving_witness_metadata`, line 16; the `unLET` redefinition goes in `Hooks.v` only) |
| 1.1a-3 | Goal-shape guards, set A | `regress3/lib/PreludeXC.v`, overrides of `Hooks.zesu_liAStep`, `Finish.zesu_run_pass_v1`, `Finish.zesu_finish_v1`, `Hooks.zesu_mapping_registered_goal`, `Hooks.zesu_source_witnesses_if_enabled`, `Hooks.zesu_pure_fact_hints_if_enabled`; the guard table is `dispatch/RESULT.md` | New `Automation2/GoalShape.v` holds the guard tactics; replace the six tactic bodies in `Hooks.v` (2479 and the three named) and `Finish.v` (1230, 400) by the guarded bodies. Do not reorder alternatives. Do not port guard set B |
| 1.1b-1 | Domain ranges as plain facts when a domain fact enters the context | `all-together/hooks_sp.v` (`liImpl`), `all-together/lib/src/p70_stackproj_nu.v`, `p13_contract_ranges.v`, `stack-proj/fix_prelude.v.in` (fix F1) | New `Automation2/DomainRanges.v`: `Class ZesuDomainRanges (domain ranges : Prop) := zesu_domain_ranges : domain -> ranges.` and `Ltac zesu_pose_domain_ranges` (for each context hypothesis `H : domain` with an instance, `pose proof (zesu_domain_ranges H)` once, split its conjunctions). Edit `Hooks.v` `liImpl` (line 1280): call it after `normalize_and_simpl_impl false`. Instances: `Contracts/NextUint64DomainRanges.v` (exists; add the instance), new `Contracts/ParentHeaderDomainRanges.v` with the lemmas `parentHeaderStackRange` (`2684354560 + 400 + 112 <= bv_unsigned (parentHeaderStackPointer args) < 3221225472`), `bv_unsigned (parentHeaderStackPointer args) mod 16 = 0`, the result-pointer and input-pointer ranges, and `parentHeaderInputSmall` (`length (parentHeaderInputBytes args) < 2^64 - 9`), each proved from `parentHeaderArgsWellFormed` (sources: `call-slice/lib/contract_ph_v7.v`, `call-depth/lib/TSp.v` lines 561 to 589) |
| 1.1b-2 | Type range for non-variable `bv_unsigned` atoms (fix FA) | `all-together/hooks_sp.v` (`bv_saturate_unsigned`, `zesu_bv_linear_cast_range`) | `Hooks.v`: redefine `stdpp.bitvector.definitions.bv_saturate_unsigned`; edit `Automation2/BvLinear.v` `zesu_bv_linear_cast_range` (line 651) |
| 1.1c | Call-site step for a callee that takes an input slice and an output slot: derive the window, lend with explicit witnesses, prove the callee domain once and keep it, state the callee stack pointer as `root - k`, restore under an existential; early restore; callee-frame side goals in a cleared context | `all-together/lib/src/p10_call_generic.v` (398 lines, latest), `p12_hook_nu.v`, `call-depth/lib/hook_early_restore.v`, `call-slice/lib/hook_ph_v7.v` | New `Automation2/CallSlice.v`. The prototype names decodeItem's interface 22 times; replace every such name by a field of `Class ZesuCallSliceInterface (domain : A -> Prop) (meaning : A -> O -> Prop)` whose fields are the four interface lemmas the prototype applies and a caller class `ZesuCallSliceCaller` whose field is the caller-level domain lemma. Instances: new `Contracts/DecodeItemCallSlice.v` (callee side, from `ZesuSsz/Interfaces/DecodeItem.v`), `Contracts/ParentHeaderCallSlice.v` (from `call-slice/lib/contract_ph_v7.v`), `Contracts/NextUint64CallSlice.v` (from `all-together/lib/src/p11_contract_nu.v`). Wiring: in `Automation2/InteriorByteSlice.v` add `Ltac zesu_call_slice_hook := fail.` and change `zesu_lend_interior_byte_slice` (line 422) to `first [zesu_call_slice_hook | <existing body>]` (the existing lend step stays last: without it 4 rule tests regress); `CallSlice.v` redefines the hook to `first [zesu_call_slice | zesu_call_restore]`. Early restore: add alternative `zesu_talt c_early_restore (…)` as the first alternative of `Finish.zesu_run_pass_v1`, guarded on `envs_entails _ (bi_exist _)` and on the restore wand being in the context. Frame side goals (`mod 16 = 0`, lower bound, upper bound of the callee frame): closed inside the step by `clear` to the range facts of 1.1b-1 then `zesu_lia` |
| 1.1d-1 | One spelling of a little-endian word read from a byte list (class V) | `all-together/lib/src/p40_index_literal.v` | Edit `Automation2/WrappedWord.v`: `zesu_wrapped_index_literal` (158), `zesu_wrapped_index_step` (197) |
| 1.1d-2 | Store or load whose pointer is an integer root under `Z_to_bv` (class B); never on the stack root | `all-together/lib/src/p50_store_lookup.v` (keep its stack-root guard) | Edit `Automation2/StoreMemoryLookup.v`, `zesu_store_memory_lookup` (517) |
| 1.1d-3 | Frame join: cells and pieces presented as the one byte array the successor asks for | `all-together/lib/src/p55_frame_join.v` | Edit `StoreMemoryLookup.v`, `zesu_join_frame_byte_array` (486) |
| 1.1e-1 | Loop exit: `length` view for `bv 8` against `byte`, exit witnesses, guard view | `all-together/lib/src/p30_loop_exit.v`, `loop-seal/lib/LoopView.v` | New `Automation2/LoopExit.v`. First check whether `zesu_finish_element_alias` (landed in 0.3, test `Proofs/Tests/FinishElementAlias.v`) already closes the `length` goal of nextUint64 00a4; if it does, do not port the `length` view |
| 1.1e-2 | Block tail: window normal form, order-fact `lia`, cursor index, loop entry, exit witnesses, edge-premise closers | `all-together/lib/src/p60_tail.v`, `p61_edge_closers.v` (not `p62_meaning.v`: step 2.2) | New `Automation2/BlockTail.v` with `Ltac zesu_block_tail_one`. Edit `Finish.v` line 1452: `Ltac zesu_block2 := zesu_block_base; try zesu_finish_residual_cascade; try zesu_block_tail_one.` Generated callers keep `Proof. zesu_block2. Qed.` |

Tests to add (one file each in `ZesuSsz/Proofs/Tests/`): `LinkedFactsNumeralGuard.v` (the
berlinGasCalc 3f00 context from `R/mem-cap/` is refused; a goal with `mod 2 ^ 64` still closes),
`UnletUnused.v`, `GoalShapeGuards.v` (each guard: one goal where the alternative runs, one where it
is skipped), `DomainRanges.v`, `TypeRangeNonVariable.v` (the equation
`bv_unsigned (sp + c) = bv_unsigned sp - k` with `sp` a record projection: `R/stack-proj/` holds
the minimal goals), `CallSlice.v` (the mocks `R/call-slice/lib/Mock5.v`, `Mock6m.v`, `Mock7.v`,
`Mock8.v`), `WordFormIndex.v`, `StoreIntegerRoot.v`, `FrameJoinArray.v`, `LoopExit.v`,
`BlockTail.v`. Register every new module in `Automation2/All.v` with `Require Export`, placed after
the modules it imports.

Acceptance of 1.1 (on the bank of main after 1.1e, callers and entries unchanged):
- all five gates pass on each PR;
- BENCH-v1: every block closed in the base still closes, plus decodeParentHeader 00ec;
  decodeParentHeader 0300 at most 330 CPU-s (measured 290 against 477 plain);
- berlinGasCalc 3f00, 3edc and nextUint64 00b8 end on an ordinary goal below 3 GiB (measured 1.6
  to 2.4 GiB; they reach 8 GiB unchanged);
- nextUint64: 7 of 10 generated callers close with `zesu_block2. Qed.` unchanged
  (0044, 004c, 0058, 0070, 0090, 009c, 00a4; measured with the prototype prelude).

#### 1.2 Generator: hidden history, per-slot frames, edges

Work in `tools/block/`. No in-tree equivalent exists for any new file named here.

**1.2-1 Merge the four prototype copies.** Base = the bank tree of the prototypes
(`git -C .worktrees/bench-8832f880fd show HEAD:tools/block/<file>`). For each file below produce
the merged text with `git merge-file -p` using `R/generator/tree/tools/block/<file>` as the common
base of the three later copies, in the order loop-seal, join-facts, all-together, then apply the
result to current main:

| File | Copies that change it |
|---|---|
| `entry_hist.py` (new, 356 lines) | generator; loop-seal (+46); join-facts (+7, same region as loop-seal lines 58 to 78: keep both edits) |
| `render_edges.py` (new, 380 lines) | generator; loop-seal (+51) |
| `render_fp301_entries.py` | generator (80 changed lines) |
| `render_fp301_statements.py` | generator (24); loop-seal (31) |
| `join_generalize.py` | join-facts (66: `ghost_group`, stash in `drop_unheld_binders`, `join_ghost_groups`); all-together (57: `_renamed_paths`, `edge_guard_disjunction`). The regions do not overlap |
| `call_boundary.py`, `forward_resources.py` | join-facts (30; 12) |
| `functions/nextUint64.json`, `functions/decodeParentHeader.json` | loop-seal, join-facts, all-together: take the union of every added key and list entry |
| `fixtures/*loop-heads.json` | regenerate with `loop_design.py`, do not merge |

**1.2-2 Mode by profile, not by environment.** In `entry_hist.py` replace the readers of
`ZESU_ENTRY_HIST` and `ZESU_FRAME_SLOTS` by profile keys read through
`function_profiles.load_profile`: `"entry_hist": "wrap"` and `"frame_slots": true|false`. Only the
`wrap` shape is kept; delete the `opaque` and `modtype` branches. A profile without `entry_hist`
renders the legacy shape until step 1.6 removes that path.

**1.2-3 History library.** New `ZesuSsz/Automation2/Hist.v` from `R/loop-seal/lib/Hist.v` (104
lines: `zesu_hist` as a stdpp `seal`, `zesu_hist_intro`, `zesu_hist_elim`, `Class ZesuHistEdge`,
`zesu_hist_step`, `zesu_hist_view`, `zesu_loop_first_pass_intro_sealed`). Add:
- `Definition zesu_join_history (P : Prop) : Prop := P.` In `join_generalize.py` replace the
  comment marker `GHOST_HISTORY_MARK` by wrapping the group as `⌜zesu_join_history (∃ …, …)⌝`, and
  in `entry_hist.classify` treat a fact whose head is `zesu_join_history` as hidden. (The comment
  marker is stripped by the renderer, so the group was rendered visible.)
- `Class ZesuHistReveal (pre : Prop) (fact : Prop) := zesu_hist_reveal : zesu_hist pre -> fact.`
  and `Ltac zesu_hist_reveal_step`: on a goal `⌜F⌝ ∗ _` with a `zesu_hist` hypothesis and an
  instance for `F`, introduce `F`. Used by 1.2-5 for loop exits.
Emitted entries import `ZesuSsz.Automation2.Hist` (the prototype emits `ZesuSsz.Hist.Hist`: change
the literal in `entry_hist.py`). Wiring of the steps: add `zesu_talt h_hist_edge (zesu_hist_step)`
and `zesu_talt h_hist_reveal (zesu_hist_reveal_step)` as alternatives of `Finish.zesu_run_pass_v1`
immediately before `c_early_restore` of 1.1c (prototype: `R/all-together/hooks_diag.v`, which used
the diagnostics hook; do not use that hook).

**1.2-4 Visible facts.** `entry_hist.classify` keeps visible: facts that mention no entry binder;
`List.length` facts on live binders; for loop classes the loop-design facts, every fact on a
loop-varying binder, and the loop design's `visible` list; every fact matching a profile
`hist_visible` regex (its binders stay live). Profile values to commit:
- nextUint64: `["decodeItemCallDomain", "decodeItemCallMeaning", "zesu_named_eq", "<> \\(0%Z\\)",
  "zesu_byte_window_fold", "orb \\(negb \\(bool_decide", "8%Z < bv_unsigned",
  "bv_signed \\(BV 128%N 8%Z\\) >= bv_signed \\(bv_zero_extend 128%N"]`;
- decodeParentHeader: the list in `R/join-facts/tree/tools/block/functions/decodeParentHeader.json`
  united with `R/loop-seal/tree/…/decodeParentHeader.json`;
- then replace the call-fact regexes by derivation: for a block that ends in a call, or is the
  return site of one, the visible set is the function-domain facts, the lengths of live outcome
  arrays, the record of the last call (`…CallDomain`/`…CallMeaning` of the newest `call<k>`), and
  the named equations of the pointer and length registers passed to the call, read from
  `JOINS.json` `calls[]` (`kept`, `replaced`). Keep the regexes only for facts this derivation does
  not cover, and list those in the PR body.

**1.2-5 Edges.** `render_edges.py` writes, per source block, `Edges<case>.v` in the function's
generated directory, and an umbrella `Edges.v` that `Require Export`s them (one file of 140
instances costs 419 CPU-s; per-block files compile in parallel). Each instance carries its rendered
proof. Extend `rocq_edge`:
- premises of an edge may be facts *visible* at the source block, not only hidden ones (loop entry
  of decodeParentHeader 032c needs three guard facts that are visible there);
- for a loop-exit edge, every fact visible at the successor and hidden in the loop class is emitted
  as a `ZesuHistReveal` instance from the loop class history;
- a loop back edge is the identity instance on the shared class history.
`render_function_callers.py` adds `Require Import <generated module>.Edges<case>.` before the last
`Require Import ZesuSsz.Automation2.All.` of each caller and keeps its check that the proof is
exactly `Proof.\n  zesu_block2.\nQed.\n` (line 209).

**1.2-6 Rule text and checks for rendered edge proofs.**
- `AGENTS.md` line 49: after "they never render proof scripts." insert: "Exception:
  `tools/block/render_edges.py` renders the proofs of `ZesuHistEdge` and `ZesuHistReveal`
  instances in `ZesuSsz/Generated/<Function>/FP301/Edges*.v`. Those proofs use only the sentence
  forms listed in `EDGE_SENTENCES` of that script; the hygiene check enforces the list."
- In `render_edges.py` define `EDGE_SENTENCES`, the list of regexes for every sentence form the
  renderer emits (`rewrite /ZesuHistEdge => …`, `apply zesu_hist_elim in …`, `unfold … in …`,
  `destruct … as …`, `iIntros`, `iDestruct`, `iPureIntro`, `apply zesu_hist_intro`, `exists …`,
  `split; [exact …|]`, `split; [by vm_compute|]`, `exact …`, `Qed`), and assert every emitted
  sentence matches one.
- `ZesuSsz/Evidence/check_proof_hygiene.py`: new rule `EDGE-PROOF`: a file matching
  `ZesuSsz/Generated/*/FP301/Edges*.v` may contain proofs, each sentence must match
  `EDGE_SENTENCES`, and `Admitted`, `Axiom`, `Ltac` are refused. Add cases to
  `ZesuSsz/Evidence/test_check_proof_hygiene.py`.
- `render_fp301_entries.py` line 592 (entries hold no `Proof|Qed|Admitted|Axiom|Ltac`) stays.
- The contradiction guard (`boundary_guards.py` `alternative_facts`) keeps running on the unsealed
  text (the prototype already passes it the unsealed definitions).

**1.2-7 Join changes.** Keep from the merge of 1.2-1: a join whose edges share a history binds the
dropped ghost binders and their facts under one hidden `zesu_join_history` fact; a join keeps the
disjunction of its incoming edges' own guards (`edge_guard_disjunction`); error joins take a
per-edge reason fact from profile `join_designs`; a store that covers a whole packaged array is
written as the stored bytes. Add: `drop_unheld_binders` never drops a binder mentioned by a fact
that matches `hist_visible` when every incoming edge holds that binder; such facts stay outside the
ghost group. (This keeps the last call's cursor equation visible after a join; blocks 02e4, 0348,
03e8 fail on exactly that.) Also fix the return-site entry after a call: build it from the call
block's own entry, not from another call's return entry (`call_boundary.py`; the join-facts copy
has the change).

**1.2-8 Driver.** New `tools/block/render_function.sh FUNCTION INPUTS RUNDIR`: port of
`R/generator/pipe.sh` (forward pass, loop heads, entries, callers, edges), each heavy step under
`tools/guarded_tool.sh`, paths relative to the worktree, `--coqc-args` from the bank's
`coqc_recipe.json`. Inputs: nextUint64 `/home/cody/zesislar/_build/agents/blackbox/inputs-nu`;
decodeParentHeader `R/generator/inputs-ph`; decodeItem: build with
`tools/block/functions/entry_interface_inputs.py --function decodeItem` (unverified — confirm the
flags against `/home/cody/zesislar/_build/agents/callwindow/pipeline.sh` first).

**1.2-9 Tests and certificates.** Regenerate the byte-pinned fixtures
(`tools/block/fixtures/fp301-generation.json`, `fp301-loop-successors.json`) from the new render;
update `test_fp301_generation.py` and `test_loop_heads.py` (5 assertions fail on the sealed
render); `test_join_binders.py` gains cases for the ghost group and the kept visible binder.
`tools/closure_cert.py` `record_problems` (line 350): hash the caller's entry modules and edge
module as well as the caller, so a re-render invalidates old certificates.

The PR of 1.2 changes no generated file (no profile has `entry_hist` yet). Gates: static,
`check-fast`, the `tools/block` tests run explicitly (`python3 -m unittest discover -s tools/block`).

#### 1.3 Switch nextUint64 to the new shape

Profile `functions/nextUint64.json`: `"entry_hist": "wrap", "frame_slots": true`. Re-render with
1.2-8; commit `ZesuSsz/Generated/NextUint64/FP301/` and `tools/block/generated/nextuint64_fp301_callers/`.
New bench set `tools/bench/sets/NU-ALL.json` (the 10 callers, caps per 1.4). Acceptance: at least 8
of 10 close with `zesu_block2. Qed.` on this one entry set (0044, 004c, 0058, 0064, 0070, 0090,
009c, 00a4 each closed in some measured configuration; 0064 needs `edge_guard_disjunction`, 00a4
the loop class of 1.2). For every block still open record the residual in the PR body; 0000 and
00b8 are finished in step 2.2.

#### 1.4 Budgets and triage

- `tools/bench/bench.py`: a set member may carry `"cpu_seconds"`; `compile_caller` (line 378) uses
  `member.get('cpu_seconds', caps['cpu_seconds'])`. Test in `tools/bench/test_bench.py`.
- New `tools/bench/mkset.py FUNCTION CALLERS_DIR`: writes a set with every caller of the function
  and `cpu_seconds = min(1200, 120 + 45 × instructions)` (instructions from
  `build/stock-zisk/cfg.json`; a caller without a successor premise counts to the `ret`/`jr`).
  Members listed here get 2,400 and `claim_gib` 24: decodeParentHeader 0000, 0088, 0094, 00a8, 0270,
  0408, 04ec and every `0514_slot*`.
- New `tools/bench/triage.py RUN`: reads `bench_report`'s leftovers (its `goal_class` already
  labels exported goals) and `tools/bench/triage_classes.json`, and prints one row per open block:
  class, owner, next action. Initial classes (regex on the leftover goal head → id, owner):

  | Id | Leftover | Owner | Next action |
  |---|---|---|---|
  | `OVER` | cap reached, no goal | coordinator | stepping-only probe; shrink the statement before any tactic work |
  | `WITNESS` | conclusion is an equation between two binders, or an `∃` whose body is pure | generator | binder map of the edge; never a prover |
  | `CALL` | spatial `∃` over two byte lists at a call | rule 1.1c | check the visible call facts of 1.2-4 |
  | `LOOKUP` | `find_in_context (FindMemMapsTo …)` | rule 1.1d-2, 1.1d-3 | print the address and the resources |
  | `FAULT` | `find_in_context (FindRegMapsTo "mcause")` | generator | a needed fact is hidden: add it to the visible list |
  | `HIST` | goal mentions `zesu_hist` | generator | missing edge or reveal instance |
  | `WORD` | equation between `take`/`drop` and `nth`/`bv_concat` spellings | rule 1.1d-1 | |
  | `PURE` | closed pure arithmetic goal under 4 KB | model tier | falsity check on concrete values first; then a `sonic` agent with the goal and exact lemma names; then a `task` agent |
  | `MEANING` | goal mentions a sealed meaning predicate | contract lemma | step 2.2 or 2.4 |
- New `tools/block/probe_mirror.py` from `R/survey/gen_mirror.py` (133 lines): writes the
  stepping-only variant of a caller (entry structure and registrations kept, history facts
  deleted, successors state no pure fact). Diagnostic only; its output is never committed.

#### 1.5 Switch decodeParentHeader to the new shape and take the first triage

Profile `"entry_hist": "wrap", "frame_slots": true`. Re-render; commit generated entries, edges,
callers. `tools/bench/mkset.py` → `tools/bench/sets/PH-ALL.json` (90 callers). Run it, then
`triage.py`. Re-certify the 7 closed blocks (0040, 0054, 0060, 00a0, 01e4, 026c, 0300: certificates
in `tools/block/closures/decodeparentheader_fp301_callers/<case>/CLOSURE.json`, copy rules in
`ZesuSsz/Proofs/DecodeParentHeader/FP301/dune`) with `tools/closure_cert.py` against the new entries
and re-render `ZesuSsz/Compliance/ParentHeaderBlockObligations.v` (`make check-support-freshness`
must pass).
Update `parentHeader_start_bridge` (`Compliance/ParentHeaderGeneratedComposition.v` line 128): it
opens entry 0000 with a fixed binder list; open the new shape (live binders, then
`zesu_hist_intro`).

Acceptance (measured anchors): 0300 at most 120 CPU-s (71 to 97 measured), 0040 at most 100;
00ec, 0118, 0144, 0170, 019c, 01c8, 01f4, 0220, 0244, 041c, 0448 close, each at most 500 CPU-s with
no growth by call number; the 31 blocks that closed in the stepping-only survey close; the whole
`Edges.v` umbrella compiles.

#### 1.6 decodeItem on the same generator path; remove the legacy path

Profile `functions/decodeItem.json`: `"entry_hist": "wrap", "frame_slots": false,
"hist_visible": [".*"]` (every fact visible: the residual lemmas in `ZesuSsz/Residuals/Block*.v`
and the witness hints in `ZesuSsz/Compliance/DecodeItem*Witness*.v` match path facts in the
context). Re-render. Expected: `git diff --stat ZesuSsz/Generated/DecodeItem
tools/block/generated/fp301_callers` is empty or limited to edge imports. If the entries differ,
fix `Compliance/DecodeItemGeneratedComposition.v` (lines 236 to 262 open `fp_machineReturn` and
`Pilot0000` with fixed binder lists). Then delete the legacy branch of `entry_hist.py` and
`render_fp301_entries.py` and make `entry_hist` a required profile key
(`grep -rn "entry_hist" tools/block` must show no "missing key" default). The berlinGasCalc overlay
branch `bench/bg-overlay-v1` gets the same three profile keys with `[".*"]` at its next rebase.
Acceptance: decodeItem sweep 24 of 24; `make check-iris` and `tools/soundness_gate.py` pass (the
production decodeItem theorem consumes these entries). If the sweep total rises more than 10%,
record an optimization item in `docs/ai/PROJECTS.md` and proceed (`AGENTS.md`: a correct change is
not rejected for its performance).

**Automation gate (end of Phase 1).** All five gates on main; the acceptance lists of 1.1, 1.3,
1.5 and 1.6 hold on one bank; `bench.py report` of NU-ALL and PH-ALL with `triage.py` output saved
under `_build/agents/rebuild/gate-phase1/`.

### Phase 2. Prove out on decodeParentHeader

Lanes 2.1, 2.2 and 2.3 start together after the automation gate; 2.4 after 2.1 is merged.

#### 2.1 Contract PR (user review gate)

One PR, not merged before the user approves its definitions.

**2.1-1 Outer header fits.** `ZesuSsz/Contracts/ParentHeaderContract.v`,
`parentHeaderArgsWellFormed` (line 104): add the conjunct
`headerFits (parentHeaderInputBytes args)` (`headerFits`: `Contracts/RlpDecodeItem.v` line 58).
Mirror it in `ZesuSsz/Evidence/SignatureGates.v`, `ReviewedParentHeaderArgsWellFormed` (line 291).
`docs/TRUST.md` lines 25 to 26: replace "`headerFits` remains a caller lemma, not a public domain.
Rung 2 does not narrow its domain." by a statement that the decodeParentHeader domain requires the
outer header to fit, why (the code does not check the first item's payload against the input; an
outer wrap sends later calls outside the input), and that this input class is outside the theorem.
New lemma in `Contracts/ParentHeaderCallSlice.v`:
`parentHeaderOuterPayloadBound`: from `parentHeaderArgsWellFormed args` and the first call's
`decodeItemCallMeaning` with a success result, `bv_unsigned (word8 after) < 2^64 - 9` (the fact
block 0068 lacks).

**2.1-2 nextUint64's code.** `ZesuSsz/Contracts/NextUint64Contract.v`: the contract's code becomes
`nextUint64SelectedCode ∗ decodeItemSelectedCode` (own map plus callee map, the shape of
`parentHeaderContractCode`). Update `Interfaces/NextUint64Correct.v` `nextUint64CallSpec2_correct`
(line 12) and `Compliance/ParentHeaderGeneratedComposition.v` `parentHeader_nextUint64_boxed`
(line 42) to pass both; callsites: `grep -rn "nextUint64CallSpec2_correct\|NextUint64ContractCorrect" ZesuSsz`.

**2.1-3 Candidate function.** New `ZesuSsz/Contracts/Candidates/ParentHeaderCandidate.v`:
```coq
Inductive ParentHeaderCandidate :=
| candidateHeaderError
| candidateHeaderSuccess (header : ParentHeaderValue).
Definition candidateParentHeader (bytes : list byte) : ParentHeaderCandidate.
Definition parentHeaderCandidateResult (bytes result : list byte) : Prop :=
  match candidateParentHeader bytes with
  | candidateHeaderSuccess header => parentHeaderResult80 result header
  | candidateHeaderError => parentHeaderError80 result
  end.
```
`candidateParentHeader` follows the code, reusing `candidateDecodeItem` and the schedule
`parentHeaderFieldSchedule` (`Candidates/ParentHeaderDomain.v`): outer item must be a list with a
non-empty payload inside the input, else error; skipped fields advance by the item's consumed
length whatever its shape; a `RequiredUint64` field with nothing left is an error; an integer
field is an error when its item is a list or its payload exceeds 8 bytes, else the big-endian fold
of the payload (`nextUint64ByteFold`, `Contracts/ParentHeader.v` line 68), with no canonical-form
check; optional fields are absent when nothing is left; bytes after the outer item are ignored.
Pin it to the binary by `Example`s proved with `vm_compute`: for W1 to W6 of
`R/return-tail/sem/Counter.v` and the 24 vectors of `ZesuSsz/Evidence/PARENT_HEADER_VECTORS.json`,
`candidateParentHeader` equals the result the pinned ELF returned under emulation
(`R/exec-check/runs.json`; generate the file `ZesuSsz/Evidence/ParentHeaderCandidateVectors.v` from
it with a script committed beside it).

**2.1-4 Known bugs.** `ZesuSsz/Compliance/KnownBugs.v`: constructors and `knownBugs` list become
`RlpLongLengthWrap` (existing), `ParentHeaderMissingRequiredField`, `ParentHeaderTrailingBytes`,
`ParentHeaderSkippedFieldShape`, `ParentHeaderBlobGasUnaligned`, `RlpUintNonCanonical`,
`ParentHeaderUintOver8`, `ParentHeaderUndecodedFieldRejected`. New
`Contracts/ParentHeaderBugTriggers.v`:
`parentHeaderBugTrigger : KnownBug -> list byte -> bool`, drafts:

| Constructor | Draft trigger on the input bytes | Witness |
|---|---|---|
| `RlpLongLengthWrap` | boolean form of `nestedWrapOccurs` (prove the reflection lemma) | existing |
| `ParentHeaderMissingRequiredField` | `parentHeaderRequiredScan bytes = RequiredMissing` (existing predicate) | `[0xc0]` |
| `ParentHeaderTrailingBytes` | the outer item's header plus payload length is less than `length bytes` | W3 |
| `ParentHeaderSkippedFieldShape` | some reached skipped field's item is one Sail rejects for that field (first draft: the item is a list) | W1 |
| `ParentHeaderBlobGasUnaligned` | the candidate succeeds with blob gas used `Some n` and `n mod 2^17 <> 0` | W2 |
| `RlpUintNonCanonical` | some reached integer field's payload starts with a zero byte | W6, `82 00 01`, `00` |
| `ParentHeaderUintOver8` | a reached integer field that Sail decodes wider than 64 bits has a payload longer than 8 bytes | W4 |
| `ParentHeaderUndecodedFieldRejected` | the candidate rejects at gas limit, gas used or timestamp (fields 9 to 11, which Sail does not decode) | W5 |

For each: an `Example` that the witness triggers it and no other class. The drafts are refined in
step 2.4; a refined trigger goes back to the user.

**2.1-5 Meaning.** `ZesuSsz/Contracts/ParentHeaderRung2.v`: replace
`parentHeaderNestedBugApplies`, `parentHeaderSuccessAgreement`, `parentHeaderRejectionAgreement`
and the body of `ParentHeaderMeaningModuloKnownBugs` by
```coq
Definition parentHeaderSailAgrees (bytes : list byte) : Prop :=
  match candidateParentHeader bytes with
  | candidateHeaderSuccess header => ParentHeaderSuccess bytes (parentHeaderSailNode bytes) header
  | candidateHeaderError => ParentHeaderRejects bytes (parentHeaderSailNode bytes)
  end.
Definition ParentHeaderMeaningModuloKnownBugs (args : ParentHeaderCall) (result : list byte) : Prop :=
  parentHeaderDomain args /\
  parentHeaderCandidateResult args.(headerInputBytes) result /\
  (parentHeaderSailAgrees args.(headerInputBytes) \/
   exists bug, List.In bug knownBugs /\ parentHeaderBugTrigger bug args.(headerInputBytes) = true).
```
(the shape of `DecodeMeaningModuloKnownBugs`: exact result, then Sail or a registered bug).
Callsites: `grep -rn "parentHeaderSuccessAgreement\|parentHeaderRejectionAgreement\|parentHeaderNestedBugApplies" ZesuSsz docs`;
update `Evidence/SignatureGates.v` and the `docs/TRUST.md` known-bugs paragraph. README line 98
("one known bug") lists the classes.

Gates: all five plus `make check-signatures`. Review packet for the user: the diff of the four
contract files, the trigger table with witnesses, and `R/exec-check/RESULT.md`.

#### 2.2 nextUint64, the callee

**Blocks.** From the triage of NU-ALL after 1.3, finish the open blocks:
- 0000 (prologue, call to decodeItem): three goals were left. (a) Two equations
  `bv_concat 64 (…) = Z_to_bv 64 (little_endian_to_bv 8 [explicit list])`: new generic rule in
  `Automation2/WrappedWord.v`, a word assembled from eight bytes equals the little-endian value of
  the explicit list of those bytes, by computation on the list spine; test
  `Proofs/Tests/WordExplicitList.v`. (b) The restore not applied at the successor existential: the
  early restore of 1.1c; if it does not fire, print the context at that goal and fix its guard.
  Cap 2,400 CPU-s.
- 00b8: run its pure side goals in a context cleared to order facts (the `zesu_lia` selection of
  1.1e-2), and add the step equating the stored slice with `nextUint64SliceImage`; the residual is
  in `R/all-together/RESULT.md`.
- 009c: the payload-window facts at the loop entry must be visible (profile `hist_visible`), then
  the loop-entry closer of 1.1e-2.
- 0058: a closer for the branch disjunction in `Prop` form (`_ \/ _` from
  `edge_guard_disjunction`): `destruct` on the disjunction when the goal is the matching
  `bool_decide` fact.
- Meaning conjunct of the return join 0070: contract lemmas `nextUint64MeaningError` and
  `nextUint64MeaningSuccess` in new `Contracts/NextUint64MeaningFacts.v` from
  `R/all-together/lib/Meaning.v` and `R/all-together/lib/src/p62_meaning.v`, registered as residual
  lemmas the way `ZesuSsz/Residuals/Block800d6960.v` registers decodeItem's (unverified — read that
  file and copy its registration form); profile `join_designs` `+0xb8` keeps the fold-result fact
  (`R/all-together/tree/tools/block/functions/nextUint64.json`).
Record each closed block: certificate from `tools/closure_cert.py` at
`tools/block/closures/nextuint64_fp301_callers/<case>/CLOSURE.json`, and a copy rule for its caller
in a new `ZesuSsz/Proofs/NextUint64/FP301/dune` (same form as
`ZesuSsz/Proofs/DecodeParentHeader/FP301/dune`).

**Composition.** New `ZesuSsz/Compliance/NextUint64BlockObligations.v` rendered by
`tools/block/render_open_blocks.py --function nextUint64 --callers
tools/block/generated/nextuint64_fp301_callers/CALLERS.json --stem NextUint64 --closed-dir
ZesuSsz/Proofs/NextUint64/FP301 --output ZesuSsz/Compliance/NextUint64BlockObligations.v` (add the
same call with `--check` to `check-support-freshness` in the `Makefile`, after the decodeParentHeader
one). New `ZesuSsz/Compliance/NextUint64GeneratedComposition.v` from `R/compose/NuComposition.v`:
block table, slot tactic, start bridge (16 binders) and end bridge (29 binders; three stack pieces
joined into 96 bytes), both rewritten for the sealed entry shape; the boxed decodeItem call spec
comes from `decodeItemCallSpec2_correct` (`Interfaces/DecodeItemCorrect.v` line 10), the way
`parentHeader_decodeItem_boxed` does it. Theorem
`nextUint64GeneratedCompliance : NextUint64OpenBlocks -> NextUint64ContractCorrect`.

**Meaning.** New `ZesuSsz/Compliance/NextUint64Meaning.v` from `R/compose/mean/NuMeaning.v` (244
lines; reuse `Compliance/NextUint64FoldFacts.v`). Close its two open lemmas:
`nu_candidate_bounds` (a long-header bound; the prototype is `Admitted` because a solver call fails:
state the bound through `candidateDecodeItemSuccessBounds` and prove it with library `lia` on the
unfolded candidate) and `nu_shift_or_step` (`(a << 8) | b = 256 * a + b` for `b < 256` and
`a < 2^56`: by `bv_eq` and `Z.lor` disjointness). No `Admitted` may remain.

Acceptance: `NextUint64OpenBlocks` has no field; `Theorem nextUint64Compliance :
NextUint64ContractCorrect` with `Print Assumptions` printing `Closed under the global context`.

#### 2.3 decodeParentHeader blocks

Loop: `bench.py run --set PH-ALL` on current main → `triage.py` → one lane per class, largest
class first → PR → repeat. A lane's brief names the class, its blocks, the prototype below, and the
acceptance "these blocks close with `zesu_block2. Qed.` on the committed entries". Known classes:

| Blocks | What is known | Work |
|---|---|---|
| 0068 (second call) | needs `parentHeaderOuterPayloadBound` (2.1-1), then one named equation between two spellings of a word | after 2.1; rule 1.1d-1 |
| 02e4, 0348, 03e8 (calls after a join) | one goal each: the call window; the join dropped the cursor equation | 1.2-7; if still open see C3 |
| 032c, 0334, 02d0, 039c (loops) | loop entry needs `i := 0` and the payload-in-input lemma (`R/loop-edge/lem/`); exit needs the reveal instances of 1.2-5 | generator data: index witness `0` on the entry edge in `render_edges.py`; contract lemma `parentHeaderPayloadInInput` in `Contracts/ParentHeaderCallSlice.v` |
| 0000 (frame setup, first call) | closes with per-slot frame and hand additions (`R/call-first/S4F.v`, 508 to 564 CPU-s); with ranges and type ranges one spatial goal is left, cells against the 72-byte array | every entry states cells (1.2, `frame_slots`), so no packing; keep the callee domain as a hypothesis (1.1c). If the wrong zero-size region is still chosen see C2 |
| 0498 and the two other calls to nextUint64 | prototype on a pruned statement: `R/call-first/N5.v` | instances of the 1.1c classes for nextUint64 as callee in new `Contracts/NextUint64CalleeSlice.v`; generic extension of `CallSlice.v`: the slice words are requested as two 64-bit cells where the context holds byte arrays (present them through 1.1d-3) |
| 04a8 and two more (load from `nextResultBytes`) | `FindMemMapsTo` 8 bytes inside the result array | rule 1.1d-2; print the address and array before any change |
| 03bc, 04b0, 0570, 05a4, `0514_slot2` (stores) | rule 1.1d-2 | |
| 0088, 0094, 00a8, 0270, 0408, 04ec (memcpy tail calls) | 0094 closed with hand lemmas (`R/return-tail/lib/Gen0094.v`, `JoinM94.v`, `RtLemmas*.v`) | contract fact `parentHeaderMemcpyDomain` from `parentHeaderArgsWellFormed` in `Contracts/ParentHeaderMemcpyService.v`; generic frame-fold lemma per frame layout in `Automation2/FramePacking.v`, the piece list being generator data; the return-address rule in `Automation2/IntegerReturn.v` must accept a `bv 64` return-address field (it matches only `Z_to_bv 64 returnAddress`) |
| `0514_slot0` to `slot4` (return) | machine part proved in two halves, 1,074 CPU-s, 5.8 GiB (`R/return-tail/lib/S0Epi.v`) | run whole under the gate limits (2,400 CPU-s, 16 GiB); never split the block. The meaning conjunct is step 2.4 |
| the rest | `triage.py` | by class |

Generator data the return and error exits need (do with the first re-render of this step): name
the three stored words (gas limit, gas used, timestamp: `machine_x20_1`, `machine_x21_1`,
`machine_x22_1` have no facts) with their defining equations in the history; error joins 0088,
00a8, 0408 carry their per-edge reason fact (1.2-7).

Record each closed block: certificate at
`tools/block/closures/decodeparentheader_fp301_callers/<case>/CLOSURE.json`, a copy rule in
`ZesuSsz/Proofs/DecodeParentHeader/FP301/dune`, then re-render
`Compliance/ParentHeaderBlockObligations.v`.

Acceptance: `ParentHeaderOpenBlocks` contains only fields whose leftover is class `MEANING`.

#### 2.4 decodeParentHeader meaning

**M1, machine implies candidate.** New `ZesuSsz/Compliance/ParentHeaderCandidateFacts.v`. For each
exit (5 return slots; 21 incoming edges of the error joins 0088, 00a8, 0408; the direct error
returns), one pure lemma: the exit's history facts (opened with `zesu_hist_elim`; about 97 of 143
at slot 0: every call record, the cursor equations, one branch fact per decision, lengths, domain)
imply `parentHeaderCandidateResult bytes result`. Structure: an invariant
`candidateWalkState bytes k cursor remaining acc` ("after field k of the schedule the candidate
walk is at this cursor with these values"), one step lemma per field kind proved once from a call
record and its branch facts, then each exit lemma is a chain of step lemmas. Registered as residual
lemmas for the exit blocks. Prototype of one edge: `R/join-facts/sem/` (`jf_meaning_0060_00a8`).

**M2, candidate against Sail.** New `ZesuSsz/Compliance/ParentHeaderSailAgreement.v`:
```coq
Theorem candidateParentHeader_sail (bytes : list byte) :
  headerFits bytes -> Z.of_nat (length bytes) < 2 ^ 31 ->
  (forall bug, List.In bug knownBugs -> parentHeaderBugTrigger bug bytes = false) ->
  parentHeaderSailAgrees bytes.
```
Proof by the Sail evaluation method of `Compliance/DecodeItemSailEvaluation.v`,
`DecodeItemSailFold.v` and `DecodeItemSailIntroduction.v` (`sail_eval` with unfolding hints) applied
to `decode_parent_header_fields` (`Compliance/ProjectionParentHeader.v`), by induction on the
schedule. Each place where the proof needs a fact about the input that no trigger excludes is a
divergence: refine that trigger or add a constructor, add its `vm_compute` witness, and send the
change to the user. The meaning then follows from M1, M2 and `destruct` on the boolean triggers.

**Final theorem.** `ParentHeaderOpenBlocks` empty; in
`Compliance/ParentHeaderGeneratedComposition.v` add
`Theorem parentHeaderCompliance : ParentHeaderContractCorrect.` from
`parentHeaderGeneratedCompliance`, `nextUint64Compliance` and the empty record.

## Critical files & anchors

- `tools/block/render_fp301_entries.py`, `body_source` (lines 469 to 523) and the assertion at
  592: the one place entries get their shape; sealing goes here, edge proofs never do.
- `ZesuSsz/Automation2/Finish.v`: `zesu_finish_v1` (400), `zesu_run_pass_v1` (1230), `zesu_block2`
  (1452); `ZesuSsz/Automation2/Hooks.v`: `liImpl` (1280), `zesu_liAStep` (2479). Six steps edit
  these two files; merge order is fixed in Operating rules.
- `ZesuSsz/Compliance/ParentHeaderGeneratedComposition.v` (theorem at 148) and
  `ParentHeaderBlockObligations.v` (record `ParentHeaderOpenBlocks`, line 109, rendered by
  `tools/block/render_open_blocks.py`): the end state is measured here.
- `ZesuSsz/Contracts/ParentHeaderRung2.v` and `ZesuSsz/Compliance/KnownBugs.v`: the meaning and the
  bug list; every change needs the user (step 2.1, step 2.4).
- `R/all-together/lib/src/p*.v` with `R/whole-fn/prelude/hooks.v`, `R/all-together/hooks_sp.v`,
  `hooks_diag.v`: the integrated rule prototypes and exactly which tactics they override.

## Verification

Run from a clean worktree at the final main.

1. `make check-fast`, `make check-iris`, `make check-signatures`; `tools/soundness_gate.py` as in
   `docs/SOUNDNESS_GATE.md`. All exit 0.
2. Final theorems: a scratch file with
   `Require Import ZesuSsz.Compliance.ParentHeaderGeneratedComposition. Print Assumptions
   parentHeaderCompliance. Print Assumptions nextUint64Compliance.` prints
   `Closed under the global context` twice. `grep -c "parentHeaderOpen_" ZesuSsz/Compliance/ParentHeaderBlockObligations.v`
   prints 0; the same for `nextUint64Open_`.
3. `make check-support-freshness` passes (obligation records match the certificates).
4. New behaviour, contract: in `ZesuSsz/Evidence/ParentHeaderCandidateVectors.v` the examples hold
   by `vm_compute`: W2 (`210 :: e 15 ++ [7; 128; 5]`) gives `candidateHeaderSuccess` with blob gas
   used `Some 5` and triggers only `ParentHeaderBlobGasUnaligned`; W4 gives `candidateHeaderError`
   and triggers only `ParentHeaderUintOver8`; the nine-`0xff` input fails `headerFits`.
   `cd R/exec-check && ../run_scoped.sh 4 python3 drive.py` still reports the same 36 results.
5. New behaviour, automation (bench on the final main, base = the run of step 0.3):
   `bench.py report` for PH-ALL shows 90 of 90 closed and for NU-ALL 10 of 10; BENCH-v1 loses no
   block; decodeItem sweep 24 of 24; free 39 of 39; berlinGasCalc 9 of 9.
6. Per step: 1.1 acceptance list; 1.3 at least 8 of 10; 1.5 anchors (0300 at most 120 CPU-s; call
   blocks at most 500 CPU-s, flat in call number); 1.6 empty diff or green compliance.
7. Hygiene: `python3 ZesuSsz/Evidence/check_proof_hygiene.py` passes with the `EDGE-PROOF` rule; a
   test edge file containing `Admitted.` or a sentence outside `EDGE_SENTENCES` is refused
   (`test_check_proof_hygiene.py`).

## Assumptions & contingencies

- **decodeItem moves to the new generator path with every fact visible** (step 1.6), so nothing is
  hidden there and its residual lemmas keep working. To hide facts in decodeItem, or to leave
  decodeItem on the legacy path, change 1.6 only; no other step depends on it.
- **nextUint64 is in scope as decodeParentHeader's callee**: `ParentHeaderContractCorrect` takes
  `NextUint64ContractCorrect` as a premise today.
- **Development probes use the research runner**, not `tools/resource_guard.sh`; gates use the
  project tooling. The other coordinator stays paused while this plan runs.
- **The `KnownBug` drafts and the candidate-first meaning shape of 2.1 are proposals**; the user
  reviews them at gate 2.1 and at every later trigger change.
- **C1, M2 does not close.** If `candidateParentHeader_sail` is not proved after the divergence
  list has been stable for two refinement rounds, state
  `Definition ParentHeaderSailAgreementOutsideKnownBugs : Prop := forall bytes, …` (the statement
  of M2), make it an explicit premise of `parentHeaderCompliance`, list it in `docs/TRUST.md` as an
  open premise, and report to the user. M1 and all blocks are unaffected.
- **C2, block 0000 still picks the zero-size region.** Port the region-bounds fallback (fix FM,
  `R/stack-proj/fix_prelude.v.in`) into `Automation2/UninitRegions.v` `zesu_region_bounds` (line
  164), restricted to requests whose size and whose candidate region's size are closed numerals
  (unrestricted it drove one block to 6 GiB); test on that block (`R/stack-proj/RESULT.md` names
  it) before the gates.
- **C3, 02e4, 0348 or 03e8 stay open on the call window after 1.2-7.** Cherry-pick the generator
  window fact from `origin/orch/call-window` (commit `884a79c57`: one
  `<call>_window_<binder>` fact per kept slice), mark window facts `hist_visible`, and make joins
  keep a window fact that every incoming edge holds instead of weakening it to `True`.
- **C4, an edge instance is too slow or its rendered proof fails.** Leave that edge's facts
  visible at both blocks (add the facts' pattern to the function's `hist_visible`); the block stays
  correct and costs more. Record the edge in the PR body.
- **C5, a generated entry's statement is false** (as nextUint64 0064 was: a join dropped a fact).
  It is a generator defect: fix the join or the visible list, re-render, never weaken the block
  statement.
- **C6, a block exceeds 2,400 CPU-s or 16 GiB with every rule on.** Profile it once with `perf`
  (`AGENTS.md`), report the tactic and the term, and treat the finding as a rule defect; do not
  split the block.
