# Push 3: automation

## Phase 0 baseline

| Measure | Baseline |
| --- | ---: |
| New-style modules | 287 |
| Toggle-pair files | 315 |
| New-style callee poses | 44 |
| New-style `Unshelve` uses | 180 |
| Median and maximum `instr_body` proof lines | 6 and 43 |
| Representative total time | 70.521 s |
| Representative `zesu_run` time | 19.720 s |
| Peak memory | 2,765,868 KiB |

Auto committed the measurement script and three unit tests as `7fa3827a`. Root merged that commit as `968023a2`.
Root used an approved Dune fallback because Rocq MCP could not resolve `Index.lookup` at the baseline gate.

## Merged automation commits

- Auto `89aaefd0`, Root `4b6ca999`: normalized machine bounds and two Closed tests.
- Auto `ad0c029d`, Root `aa8a61bf`: A1 continuation matching and four Closed tests. Root exported and ratcheted A1 in `2d5cf9e6`.
- Auto `7b53e8ca`, Root `a93b28c6`: A3 named code-list unfolding and a Closed symbolic-count test.
- Auto A2 `c6df7c87`, A6 `af238d75`, and A4 `71587c4d`, Root `36a11d5b`: five original statements Closed with empty MCP assumptions.
- Auto `bc5a83e5`, Root `141cb914`: guarded current-H7 preservation and true integer byte-word equality.
- Auto `bf4b8d8e`, Root `f33e9a1b`: exact folded Tail reg-col selectors.
- Auto `d1313d67`, Root `edea1156`: exact descriptor-size extraction with the full byte array retained.
- Auto `76d81c04`, Root `f6c7d005`: exact full-array pair and array-plus-pure package selectors.
- Auto `4c6198bc`, Root `e05d855d`: exact offset16/24 transaction word-image side conditions.
- Auto `f5cc81a8`, Root `cb014887`: first let-bound copied Word0 selection with fifteen later words retained.

Each listed proof rule passed its focused test, Rocq MCP assumption audit, and mandatory fast gate before Root merged it.
Root's 07:47 EDT periodic `check-iris` on `e05d855d` remained red with 44 older first-file errors.
Auto has not claimed a complete Iris gate or a CP3 checkpoint from these local closures.

## Current first-array checkpoint

Root merged Auto `9b386b5d` as `78245eba` after j32 preview fast, focused test, and Root precommit fast passed.
Its guarded opener selects the first complete bytes1571c array from a folded PostData descriptor package.
It leaves the exact size fact, hash array, five later descriptor arrays, and copied words intact.
The dedicated PostData owner statement compiled Closed and verified with MCP assumptions `[]`.
The corrected focused j16 target and enabled-cache mandatory j16 fast gate passed.
Current debt counts match Root `20d8970f`: hints 78, manual destructuring 43, trace removals 46, toggles 320, and `Unshelve` 1783.
The `Unshelve` count rose by two in earlier TX H7 pilots; Auto's first-array patch added none.
Auto linked Root's unchanged 339 A3 wrappers only for focused and fast gates.
The canonical wrapper digest was `dfab73e7a3f54519cc4e15d7ba99f02509ad514ae74512ed21d575c061e32cf6`.
Auto removed the read-only link after each gate and changed no trace or binary.
Auto rebased onto `78245eba` and pushed `islaris-native-auto` at that same remote SHA.

## Open work

Auto's private A5 continuation-order selector closes unchanged AuthorizationsFirstInt and AuthorizationsSecondInt in a clean proof graph.
Both original Module M audits report assumptions `[]`; seven A1 regression shapes still close.
The unchanged WithdrawalsRest proof exceeded 300 seconds before closure.
Tail measured a sound candidate return cut at `0x156b4`, but its loaded-word scratch array still needs a typed handoff.
Auto will keep A5 private until that original statement closes after Tail's sound split.

Auto's three B1 checker files remain untracked.
Nine checker unit tests pass, but two new predicates initially failed the zero LithiumUnfold baseline.
Tail `44f2db39` adds the exact-return hook, and TX `68438283` adds the count-entry hook.
Root will merge both hooks after the first-array gate; Auto will then rebase and run the flat final checker baseline.
Root owns the proposed Makefile and AGENTS one-line integration patches and the active native plan.

Status and CountCall used a private six-package opener to promote hash length and five descriptor-size facts before `zesu_run`.
Their next common native residual is optional conditional1596c Some/None owner selection.
Auto will keep both selectors private until fresh native goals and dedicated owner statements confirm them.

## Private cache deviation

Old private `.vo` files made the first A5 closures provisional.
Root approved a private cache audit that moved `_build/agents/auto` to a dated `/tmp` folder.
Auto rebuilt the three original A5 targets once with Dune `--cache=disabled` in the required Auto build path.
The clean graph confirmed the two authorization closures and the unchanged WithdrawalsRest cap.
Required focused and mandatory gates still use the shared Dune cache with `--cache=enabled`.

## Sep15 recovery attribution

Auto tested all 44 frozen `e05d855d` failure files with the pre-A1 `liAStep` hook and two local instance removals.
Eleven original modules closed; 33 still failed at their frozen proof lines.
Auto kept the [44-row result](/home/cody/zesislar/.worktrees/islaris-native-auto/_build/agents/auto/partition44/partition44.json) in its private build directory.
The complete `ExactByteListsPublicRawPrefix` timing scratch closed in 144.056 seconds and used 2,503,596 KiB at peak.
Its `zesu_finish` tactic used 82.225 seconds across 12 calls; its longest call used 20.750 seconds.
Its `zesu_liAStep` tactic used 14.056 seconds across 1,743 calls.

## B4 Encoder.bytes closed-call deviation (2026-09-16)

**Before.** `encoderBytesExactCallSpec := ∃ data size sp ret bytes tail P, encoderBytesExactSpec data size sp ret bytes tail P` allowed an existential caller frame `P` and exposed no named closed return.

**After.** Additive `zesuEncoderBytesExactCallSpec := ∃ data size sp ret bytes old_x5 old_x6 old_s0 old_s1 stack0 stack1 stack2 stack3 stack4 stack5 tail, <exact entry resources> ∗ instr_pre (bv_unsigned ret) (encoderBytesExactReturn data size sp ret bytes old_x6 old_s0 old_s1 stack2 tail) ∗ True`. `encoderBytesExactReturn` fixes `P := True` in the existing exact post.

**Reason.** B4 requires a closed Encoder.bytes call boundary with `ret : bv 64`, resources fixed by unification, and a named return.

**Equivalence note.** `encoder_bytes_exact_entry_equiv` proves the new entry is equivalent to `∃ data size sp ret bytes tail, encoderBytesExactSpec data size sp ret bytes tail True`. The prior open-`P` interface remains unchanged for existing callers.

Commit `c6ffe09a` implements this deviation after the local dependency cherry-pick `c6b8a4b6`, which matches approved repair `033460c3`. MCP compile printed seven Closed lines. The focused j16 target and mandatory Auto `check-fast` passed.
