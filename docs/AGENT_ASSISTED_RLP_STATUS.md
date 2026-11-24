# Agent-assisted RLP plan: status

Plan: `docs/AGENT_ASSISTED_RLP_PLAN.md` (tracked on main). Tracking issue #347. This file is the running status; it is updated by the coordinator and is not yet committed.

Last update: 2026-11-23.

## Stage A: tooling — done

| Task | State | Pull requests |
|---|---|---|
| A0 cleanup | done; 186 GB of 200 GB | — |
| A1 close-out, rules | merged | #349, #350, #351 |
| A2 store, A7 router and report | merged | #353, #361, #372, #374, #375 |
| A3 goal packaging, spatial export, machine runs | merged | #358, #366, #354, #355, #370 |
| A4 hint pack | merged | #352 |
| A5 tier replay, routing table | merged; see "Haiku provers" | #367, #369, #373 |
| A6 derivation, annotations | merged | #356, #364 |
| A8 Sail modules, scope note | merged | #365 |
| A9 relocatable artifacts | merged | #357, #359, #360 |
| Production prover driver (not in the plan) | merged | #371 |
| Generator annotation consumption for allocator calls (beyond A6 items 5 and 6) | merged, +336/−32 lines | #368 |

Last full gate on main: `make check-fast` rc 0 and `make check-iris` rc 0 at `2015b187e`.

## Stage B: prove-out — in progress

| Task | State |
|---|---|
| B0 inputs | done (traces existed; selected-code files, hint packs, round-1 requests) |
| B1 statements | array-list side reviewed, fixed, pinned and merged (#363). `txAccessList` side (#362): reviewed; fixes and class registration in the lane, full gate cycle running. Reviews: `_build/agents/aa/review/` |
| B2 `keysToOwnedSlice` | render round 23+ on the merged contracts; rules #376 merged; second rules branch (`aa/rules2`) merged into the region; 12 open blocks being rerun |
| B3 `entriesToOwnedSlice` | started from the ported `keysToOwnedSlice` annotations: round 3 renders 33 entries, 30 callers, 0 refused |
| B4 `keysEnsureCapacity` | started: adapter and annotations written, derive round 4 |
| B5 `txAccessList` | not started (blocks); contract written |
| B6 Sail agreement | proved: 43 of 43 lemmas kernel-checked, assembled, `Print Assumptions` closed (#378). Waits on #362; then rewire to the registered classes |

## Stage C

C1 sizing of `decodeTxFields`: round-1 derivation done (148 requests, decision floor 61, 53 loop cuts, jump table filed as a `predicate` request). Token projection waits on Stage B figures. Details: `_build/agents/aa/DERIVATIONS.md`.

## Haiku provers

All provers so far ran with no tools and at most two attempts per tier.

| Test | Haiku result | Opus result |
|---|---|---|
| Replay, 68 known-true `decodeItem` lemmas | 46 closed, all of them goals the no-model tactic also closes (52 of 68); 0 of the 16 hard ones | 0 of 10 hard ones; 2 of 11 with the definitions recipe |
| Sail lemmas (43, task text hand-built by an Opus agent) | 9 closed (6 low, 1 medium, 2 high) | 34 closed |
| `keysToOwnedSlice` pure goals (32 in round 20) | 1 closed | 8 closed |

- Share of closed pure/meaning goals closed by Haiku tiers on real work: about 21% (target 70%).
- Tokens per closed Sail lemma: `haiku-low` 1.08 M, `haiku-high` 2.75 M, `opus-medium` 0.20 M, because most Haiku attempts fail and escalate.
- Typical Haiku failure: asks for more context, or claims "proved" with a proof that does not compile.
- `check_proof` tool (PR #377): a prover can test its proof against the kernel within one attempt. First probe, 3 failed `keysToOwnedSlice` goals at `haiku-low`: 4 check calls each, all three still answered "need more context".

## Decisions (delegated to the coordinator by the user, 2026-11-23)

1. B1 review: done by reviewer agents. All 13 packet questions accepted as proposed. The three Sail divergence classes are being registered (#362).
2. Review finding on #363: `altFlAllocCallPremise` was false for a bump position near 2^64 (the capacity check wraps; reproduced on the pinned ELF). Fix: heap position at most 2^63. Minor: comment on the parent-header memcpy, a literal address reached through `freeListsPointer`, undocumented `premise` registry field. Review text: `_build/agents/aa/review/arraylist/REVIEW.md`.
3. Generator changes in #368 (beyond the plan's "only A6 items 5 and 6"): stand.
4. Routing ladder: mechanical 1, `haiku-low` 2, `haiku-high` 1, `opus-medium` 2; `haiku-medium` dropped; a goal never spins before the top tier ran.
5. Prompt limit: 12,000 bytes by default, 32,000 for retries, Sail lemmas and goals too large at 12,000.

## Targets missed so far

| Measure | Target | `keysToOwnedSlice` now |
|---|---|---|
| Rounds per region | at most 3 | 20 |
| Decisions per region | at most 2 × floor | 18 against a floor of 5 |
| Pure goals closed by Haiku tiers | at least 70% | 1 of 9 closed goals |

## Incidents

- A0 removed a worktree that a test reads by path; restored.
- `tools/cleanup_after_merge.sh aa/replay` deleted the replay run dir (matched by name). The corpus was rebuilt; per-attempt records of the first replay are lost.
