# Agent-assisted proofs: pause note, 2026-11-25

Work on `docs/AGENT_ASSISTED_RLP_PLAN.md` (issue #347) is paused. This note says where the work stands, what the agent-assisted method has shown, and how to resume. It is written for a reader who was not present.

## Summary

- The aim was a cheap, repeatable way to prove machine-code functions with agents: a generator writes the block proofs, cheap models prove the leftover pure goals, and a coordinator makes the few real decisions.
- Three helper functions are proved and merged. Their Sail agreement theorem for the caller is proved and merged.
- Termination, as a bound on executed instructions, works. Four functions have a proved bound. These proofs sit in draft pull requests against a modified Islaris and are not on `main`.
- The fourth function, `txAccessList` (323 instructions), is not proved. 14 of its 54 block cases are closed. It consumed most of the last two days.
- The method is not yet cheap or repeatable for a function of that size. The section "What the method has shown" gives the evidence.

## State of the plan

| Stage | Content | State |
|---|---|---|
| A | Tooling: obligation store, router, goal packaging, machine-run screen, annotation rows, generator hooks | merged |
| B1 | Contract statements for the four functions, reviewed and pinned | merged (#362, #363) |
| B2 | `keysToOwnedSlice` (121 instructions) | proved, merged (#395) |
| B3 | `entriesToOwnedSlice` (138 instructions) | proved, merged (#396) |
| B4 | `keysEnsureCapacity` (107 instructions) | proved, merged (#404) |
| B5 | `txAccessList` (323 instructions, 54 block cases) | open: 14 cases closed and certified |
| B6 | `txAccessListSailAgreement` | proved, merged (#378) |
| C1 | Sizing of `decodeTxFields` | round-1 derivation only (148 requests, 53 loop cuts) |
| T1–T5 | Step budgets: Islaris fork, compatibility, budget layer, generator | done; T5 on `main`, T2–T4 in drafts |
| T6–T8a | Charged proofs of four functions | proved, in drafts |
| T8b | Charged `txAccessList` | not started; needs B5 |
| T9 | Switch the default Islaris, merge the drafts | not started |

No instruction of `txAccessList` is yet under a Sail-compliance theorem. The three helpers have contract proofs only; the compliance statement needs `txAccessListCompliance`.

`main` is at `1dd527a9b`. Its last complete gate was at `e916544ee` (`make check-iris` rc 0, `make check-fast` rc 0). Eight later merges each passed their own branch gates. A gate of `1dd527a9b` was started at the pause; its result is in `/home/cody/.cache/zesu-tmp/maingate/gates3.log` (lines `CHECK-IRIS rc=` and `CHECK-FAST rc=`). Read it before any new merge.

## Termination

Design note: `docs/AGENT_ASSISTED_RLP_TERMINATION.md`.

- The Islaris fork (`github.com/codygunton/islaris`, branch `zesu-step-budget`, head `d2073eb`) charges one credit for each fetch of an instruction at a charged address. `isla_budget_adequacy` concludes that the number of such fetches is at most the budget. `fetches_bound_steps` turns that into a bound on machine steps. Both are closed under `Print Assumptions`.
- The fork lives in `/home/cody/islaris-budget` with its own opam switch. `/home/cody/islaris` and its switch are unchanged. Build this repository against the fork with `ISLARIS_REPO=/home/cody/islaris-budget`.
- This repository builds against the fork with edits to three files in `ZesuSsz/Export/` and one test. Existing proofs cost about 1% more instructions.

| Function | Budget (fetches) | Charged cases closed | Needed a prover | Added instructions | Pull request |
|---|---|---|---|---|---|
| `keysEnsureCapacity` | 197 | 25 of 25 | 0 | +2.4% | #411 |
| `keysToOwnedSlice` | 194 | 30 of 30 | 0 | +3.2% | #418 |
| `entriesToOwnedSlice` | 204 | 30 of 30 | 0 | +2.9% | #418 |
| `decodeItem` (two loops) | 75 | 24 of 24 | not reported | +3.7% | #410 |

- The draft chain is #406 (`aa/t3`) → #405 (`aa/t4`) → #411 (`aa/t6`) and #410 (`aa/t7`) → #418 (`aa/t8a`). Each passed `make check-iris` and `make check-fast` against the fork. None was gated against a `main` later than `459c53ff6`.
- The budgets of `alloc` (53), `remap` (9), `free` (42) and `memcpy` (3) are assumed premises. Derived from the existing premises they do not count the callee's instructions; `docs/TRUST.md` on `aa/t6` states which reading is the trust item.
- The charged proofs found one real error: `budgets.py` gave budget 0 to a block that is unreachable on one edge but runs after a call return. Two budgets moved from 175 and 185 to 194 and 204 (#417).
- The `decodeItem` agent ran past its request budget and gave no final report. Its theorem and gate results were checked on the branch.

## `txAccessList`

Run directory: `_build/agents/aa/txAccessList/`. Read `HANDOFF.md` and `HANDOFF-bridges.md` there first; each begins with a section marked PAUSED.

| Class (bench `bench-b9b`, render round 56, plus five cases not rerun) | Cases |
|---|---|
| Closed and certified | 14 |
| Pure leftover goals | 17 |
| Spatial leftover | 17 |
| CPU cap, 3,600 s | 4 |
| Memory limit, 32 GiB | 1 |
| Crash (`coqc` SIGSEGV) | 1 |

- Every block renders since round 51. The composition compiles: `txAccessListComplianceFrom : TxAccessListOpenBlocks -> TxAccessListContractCorrect`, with both end bridges proved. 40 cases are in the open record.
- Round 58 was not rendered. The render step was killed at its 16 GiB guard while loading a 3.8 GB `FORWARD.json`. Round 58 carries two untested remedies: compact stored words for blocks `0368` and `0404`, and visible branch facts for `0128` and `01bc`.
- Eight exported goals are true in their block and unprovable as exported, because the export drops the 7,700-node `decodeItem` call facts. Branch `aa/rules14` addresses this.

The capped blocks have two measured causes, and neither is block length:

| Block | Instructions | Lithium steps | Cause |
|---|---|---|---|
| `0128` | 13 | 8,947 at the cap | the tail is proved 4 times after pointer loads whose fault cases are not refuted |
| `01bc` | 15 | 11,557 at the cap | the same, 6 times |
| `0368` | 10 | 2,580 at 30.9 GiB | goal of 140k to 186k nodes: each stored word stated as 8 byte-extracts of a large expression |
| `0000` (closes in 690 s) | 26 | 4,561 | reference |

The memory is live data: a forced compaction freed 7%.

## What the method has shown

### Cost of a region

| Function | Instructions | Rounds | Decisions (floor) | Hand-written Rocq lines | Prover tokens |
|---|---|---|---|---|---|
| `keysToOwnedSlice` | 121 | 30 | 18 (5) | about 1,560 | 7.58 M |
| `entriesToOwnedSlice` | 138 | 10 | not recorded | 11 new lemma lines beyond the shared bridges | 9.42 M |
| `keysEnsureCapacity` | 107 | 9 | 13 (5) | 1,999, of which 510 annotation rows | 729 k per block |
| `txAccessList`, unfinished | 323 | 58 render rounds | 30 so far | about 1,600 in composition, call specification and hints | not totalled |

The plan's targets were at most 3 rounds and at most twice the decision floor. No region met them.

### What worked

- A second region of the same shape is cheap. `entriesToOwnedSlice` reused the bridges of `keysToOwnedSlice` and needed 10 rounds against 30.
- Charged variants are nearly free once the uncharged proof exists: 109 of 109 charged cases closed, the 85 array-list cases with no prover.
- The kernel is the only judge. No accepted proof was later found wrong. The defects found were in statements, rows and tools.
- Saved goals and traces located every cost problem that was solved. The fixes that mattered removed one divergent call or one repeated search; they did not make a solver faster.
- Statement review by agents found a false assumed premise (#363: the allocator capacity check wraps near 2^64).

### What did not work

- The generator is not general. `txAccessList` needed about a dozen new annotation keys in six merged generator pull requests (#402, #407, #409, #413, #416, #419) and the unmerged `aa/gen-lowbound-next7`. Each gap was found one block further into the function. A scan of the whole function before the first bench would have found most of them earlier.
- Cheap provers close a minority of the goals. On `keysEnsureCapacity` the Haiku tiers closed 47% of the pure goals; the target was 70%. On `txAccessList` two passes over 32 tasks gave 8 proofs from 49 attempts.
- The real-state screen was absent for the whole of `txAccessList`: no binder map existed, record binders were rejected, and the driver sent unscreened goals to provers. Eleven false goals went through two prover passes. The screen is now a gate (#423, #425, #426), but it is unproven on a full round.
- Goals reach provers in a form that omits needed premises (facts over 2,048 nodes), or restates values the generator got wrong. A prover's "false" or "need context" verdict was more often a pipeline defect than a hard goal.
- Rule work was reactive. Seven rule branches (`rules7` to `rules12`, `rules14`) each fixed the stop of one or two blocks. Two of them failed `make check-iris` on their first heads by breaking older proofs.
- Agents hit their request budget before finishing. One region passed through nine owners. Each handoff cost a reading pass, and one agent ran 22 hours and 600 requests without a final report.
- Coordination needed a ruling about once an hour. Several rulings were about soundness of a tool shortcut and could not be delegated.
- Gates were a bottleneck and a hazard: a full `make check-iris` takes 1.5 to 2 hours cold, the gate's wall budget killed correct builds twice, and two gates in one worktree hung for 9 hours.

### Money

Single agents cost 10 to 70 dollars each (for example: `T7DecodeItem` 71.5, `RulesExport` 49, `B5Bridges5` 44, `B5Goals9` 39, `Rules10Cost` 29). No total was kept. The prover rounds themselves are a small part; the Opus region owners and rule agents dominate.

### Reading

The pipeline proves a 100 to 140 instruction function with allocator calls in about a day once a similar function is done. It does not yet scale to a 323-instruction function with nested loops and twelve calls without continuous generator and rule development. The next gain is not in the provers. It is in (1) finding generator gaps before benching, (2) making the screen and the export trustworthy so that prover spend goes to true, complete goals, and (3) keeping context and entry size small so block proofs finish.

## Unmerged branches

| Branch | Head | Content | State |
|---|---|---|---|
| `aa/b5-tx` | `f0358b82c` | region: round-56 render, 14 certificates, residual modules, composition | pushed; lacks `main` after `fa2c024db`; `make check-fast` not rerun since the certificates were renewed |
| `aa/b5-tx-r41` | `da5c2af54` | annotation rows through round 58 | pushed |
| `aa/b5-tx-coq` | `4dfefee29` | region hint and bridge modules | pushed; merged into `aa/b5-tx` |
| `aa/gen-lowbound-next7` | `cef578f5a` | generator key `word_binders` | goldens 0 diff; no gate, no pull request |
| `aa/rules12` | `4958504a3` | linear solver without runaway dividing facts | last gate `CHECK-IRIS rc=2`, cause not read; two earlier heads failed for real reasons |
| `aa/rules14` | `683905860` | export and closing of pure existentials with large call facts | gate on `cf7a0e50e` rc 0; gate on the merged head `CHECK-IRIS rc=2`, cause not read |
| `aa/t3`, `aa/t4`, `aa/t6`, `aa/t7`, `aa/t8a` | `df4ead236`, `25102eefc`, `5d66a388a`, `3ea5f39ac`, `67d71fdbf` | Stage T drafts | gated against the fork; need a merge of `main` and a new gate |

The two `rc=2` results show no Rocq error in their logs and ran while every block proof rebuilt after #427. The gate's wall budget may have ended them. This is not confirmed.

## How to resume

1. Read `gates3.log` for `main`. If `make check-iris` failed with a proof error, the suspects are #424 and #427; revert the one named and gate again.
2. `aa/rules12` and `aa/rules14`: merge `main`, gate each once and alone (`make check-iris`, then `make check-fast`, never two gates in one worktree), read the first error if any, open the pull requests. Handoffs: `_build/agents/aa/txAccessList/HANDOFF-bridges.md`, `_build/agents/aa/rules14/HANDOFF.md`.
3. `aa/gen-lowbound-next7`: `make check-fast`, pull request.
4. Round 58: rerun the render with `ZESU_TOOL_MEMORY_GIB=48` (command in `HANDOFF.md`, step 2), install, bench all 54 cases, certify. This run answers whether `0128`, `01bc`, `0368` and `0404` finish.
5. Screen the leftovers with the binder map, list unscreened goals with reasons, then run a prover round (`tools/oblig/drive_kernel.py`, `run_round("txAccessList", <run dir>)`).
6. Take the 17 spatial stops in the order listed in `HANDOFF-bridges.md`.
7. At 0 open cases: `txAccessListCompliance`, registry row, gates, pull request. Then the charged variant by the recipe of `aa/t6`, and T9.

Rules that cost time when they were ignored:

- Use `/usr/bin/git worktree add`; do not use `git stash`.
- Start gates with `env -u OCAMLPATH`; check a silent gate after 30 minutes.
- Do not run a render or a golden comparison in a worktree where a gate runs.
- After a pull request is reported ready, put later commits on a new branch.
- Do not run `tools/cleanup_after_merge.sh` for a branch whose last name component names a run directory.

## Decisions waiting for the user

1. Whether to continue `txAccessList` with the present method. If round 58 does not bring the four capped blocks under the cap, the remaining choice is to cut blocks at `+0x13c`, `+0x1d4` and `+0x290` (one annotation row and one entry each); no cut helps `0368`.
2. Whether to merge Stage T now (T9) without the charged `txAccessList`. The four charged proofs do not depend on it.
3. The per-agent request budget: 600 in the session that ran this work, 200 by default. The setting was not saved.
4. Whether to do the suggested spike for another architecture (one small AArch64 function by hand with stock Islaris), to measure how much of `ZesuSsz/Automation2/` is RISC-V-specific.
5. `ZesuSsz/Proofs/Tests/RegionFaultNegatedBounds.v` takes 10 to 14 minutes of every `make check-iris`; it is over the 60-second goal for a non-proof module.

## Where things are

- Plan: `docs/AGENT_ASSISTED_RLP_PLAN.md`. Earlier status: `docs/AGENT_ASSISTED_RLP_STATUS.md` (2026-11-23, not updated since).
- Run directories: `_build/agents/aa/<function>/`, each with `HANDOFF.md`. Charged variants: `_build/agents/aa/<function>Budget/`.
- Rule lanes: `_build/agents/aa/rules7/` to `rules14/`, each with `HANDOFF.md`, saved goals and cost logs.
- Fork notes: `/home/cody/islaris-budget/T1-HANDOFF.md`, `T2-HANDOFF.md`, `T3-HANDOFF.md`, `install-theory.sh` (untracked there).
- Scratch worktrees that can be removed after a check that they are clean: `.worktrees/aa-gen-next7-r58`, `.worktrees/aa-gen-next7-old`, `.worktrees/aa-t5-base`, `.worktrees/aa-t5-smoke`, `.worktrees/aa-maingate`, `.worktrees/aa-b5-tx-r31`.
