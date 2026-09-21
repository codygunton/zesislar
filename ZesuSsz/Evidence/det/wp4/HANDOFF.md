# Handoff WP4

Two items for the orchestrator, independent of each other.

1. **The trace tail a call returns with (C1).** Replaces compliance plan
   7.6.2 item 3.
2. **The hygiene checker reads the working tree.** A correctness fix to
   the gate, worth taking first.

Both are written, gated and measured on branch `determinism`; nothing
here has been merged into `islaris-native`.

# Item 1: the trace tail a call returns with (C1)

## Hand-written lines per segment

| segment | before `ccf505e8` | after | removed |
|---|---|---|---|
| `write_success_exact_suffix_entry_segment` | 33 | 28 | **5** |
| `write_success_exact_tail_fields_third_segment` | 19 | 19 | 0 |
| `write_success_exact_post_transactions_segment` | 34 | 34 | 0 |
| `write_success_exact_epilogue_segment` | 14 | 14 | 0 |
| total | 100 | 95 | 5 |

The three unchanged segments stall earlier than their trace existential,
on the classes WP6 is taking next; they are not evidence against the rule.
`tools/det/handlines.py --set … --before … --after …` reproduces the
table.

## Commit

`d896ce72` — "WP4: supply the trace witness at the existential, and drop
five hand lines". Parent `21f280d6` adds the two inclusion lemmas and the
prober; both are needed.

## Files

| file | change |
|---|---|
| `ZesuSsz/Automation/TraceTailLemmas.v` | new. `zesu_scons_snap_subseteq_scons` and `zesu_scons_subseteq_scons`, proved by Islaris's own `spec_solver`. It sits below `Hooks.v` so the import does not cycle. |
| `ZesuSsz/Automation/Hooks.v` | `zesu_open_trace_exist`, `zesu_close_trace_inclusion`, `zesu_finish_trace_tail`. The project's Lithium hook redefinitions belong in this module and the hygiene checker enforces that. |
| `ZesuSsz/Automation/Finish.v` | `zesu_open_trace_exist` last in the search list of `zesu_run_pass`, so Lithium keeps first refusal; `zesu_finish_trace_tail` in the finisher's pure chain. |
| `ZesuSsz/Proofs/WriteSuccess/WriteSuccessExactSuffixEntrySegment.v` | five hand lines deleted: the three-line `iExists` and the `unfold subseteq, spec_subseteq, scons, scons_snap; naive_solver`. |
| `ZesuSsz/Proofs/WriteSuccess/WriteSuccessExactTailRawLoad.v` | one `match goal` matched a hypothesis by a name Coq generated (`vmem`); it now matches the shape. Needed by `21f280d6`. |

## What the rule does

A call returns with its events still open, so the block is asked for

```
∃ x : spec *ₗ (), ⌜scons_snap event accept x ⊆ scons event tail⌝ ∗ … x …
```

Lithium's `liExist` ends with `fail "not handled by liExist"` for a
`li_prod` existential whose body uses the variable, which is exactly this
shape, so the author supplies the witness. The witness is always the
caller's tail — the second argument of the `scons` on the right of the
inclusion — and that term does not mention the bound variable, so it can
be read out from under the binder. The inclusion then holds because
`scons_snap` only adds a constraint on the snapshot that `scons` does not
make.

Two things the orchestrator should not re-derive:

- **Discharge the inclusion in the same step.** Splitting the product into
  evars and letting Lithium continue does not return: with the spec open,
  `instr_pre … ?x` matches anything in the context. A probe with that rule
  ran 171 s and was killed at its 6 GiB cap, and wired into the automation
  it took `check-iris` past the 200 GiB batch cap twice, at 25 and at 32
  jobs, against 75 GiB without it.
- **Compare the events syntactically.** The finisher entry requires the
  open spec to be an evar and uses `constr_eq` on the events. A `unify`
  instead runs a conversion check over the whole event history: the first
  version did not finish the suffix-entry segment in forty minutes.

## Benchmark, both frozen baselines

Measured with `tools/residual/benchmark.py --automation HEAD`, against
`ccf505e81f85` and `ccf505e81f85-rule15`.

| set | metric | baseline | after |
|---|---|---|---|
| full, 305 | closed | 2 (0.66 %) | 2 (0.66 %) |
| full | C1 row | 56 | **55** |
| full | C3 row | 2 | 3 |
| full | C4 row | 13 | 13 |
| full | timeouts | 1 | 0 |
| full | median s | 8.0 | 7.0 |
| rule-15, 48 | closed | 2 (4.17 %) | 2 (4.17 %) |
| rule-15 | C1 row | 10 | **9** |
| rule-15 | C3 row | 2 | 3 |
| rule-15 | C4 row | 2 | 2 |
| rule-15 | timeouts | 1 | 0 |
| rule-15 | median s | 13.7 | 6.6 |

One lemma leaves C1 on each set and lands in C3, a sealed-unfold residual
behind it. The frozen sets are the *residual* population, where most C1
records are a different shape from the one at a call return; the segment
table above is where this rule is meant to show, and it does.

No regression: no outcome moves from `closed` or `residual` to `timeout`
or `error` on either set.

## Tests and gate

- `make check-iris`: exit 0, all proofs, peak 9 GiB, no guard kill.
- Uncached checks before the gate: proof hygiene, parity, spec shapes,
  the decoder cases, and both unit suites. `tools/det/gate.sh` runs them
  itself so a cached Dune step cannot report success for them.
- `ZesuSsz/Proofs/Tests/` builds as part of `check-iris`. This rule has no
  test of its own yet; the suffix-entry segment is its regression test
  until one is written.

## Merge order

1. `21f280d6` — the lemmas, the `Hooks.v` tactics, the `Finish.v` wiring,
   and the `WriteSuccessExactTailRawLoad.v` shape match. Gate here.
2. `d896ce72` — the five hand lines deleted from the suffix-entry
   segment. Gate here.

Take them together or not at all: after step 1 the segment's `iExists`
has nothing left to instantiate and the module does not compile, which is
the failure the orchestrator would otherwise meet first.

`7a95dcaf` (the gate rule and the widened hygiene checker) is independent
and can go before or after; it is worth taking first, because it is what
catches a `Ltac … ::=` in a module that is new but not yet committed.

# Item 2: the hygiene checker reads the working tree

`7a95dcaf` — "Gate rule: the checkers run uncached, and they see new
files". Take this one first: it is what makes the rest of the gate
trustworthy, and it is independent of item 1.

## The defect

`ZesuSsz/Evidence/check_proof_hygiene.py` collected the files it scans
with `git ls-files`, which lists only *tracked* files. A module that is
new but not yet committed is invisible to every rule in the checker —
the placeholder check, the forbidden-name check, the size baseline, the
`Automation.All` import rule, and the Lithium hook-redefinition rule.

That is not hypothetical. A `Ltac … ::=` outside `Hooks.v` stood in a new
module for two commits on this branch. The checker had nothing to say
about it until the module was committed, and by then a `check-fast` that
Dune answered from its cache had already reported success twice.

## The fix

```python
["git", "ls-files", "--cached", "--others", "--exclude-standard"]
```

`--others --exclude-standard` adds the files that are new but not
ignored, which is what a reviewer sees. `_build`, `build` and the
generated trace directories stay out through `.gitignore`, so nothing
else changes. One call site, `tracked_files()`.

## The second half: a cached gate is not a gate

`tools/det/gate.sh` now runs the checkers itself — proof hygiene, parity,
spec shapes, the decoder cases, and both unit suites — before any step
Dune can satisfy from its cache, and prints `uncached checks passed`.
Every report on this branch names that run. The orchestrator's gate
should do the same; the two-line shape is:

```
python3 ZesuSsz/Evidence/check_proof_hygiene.py
… the other checkers …
echo "uncached checks passed"
```

## Effect on the current tree

Running the widened checker over this branch finds no new failure beyond
the one it was meant to catch, which is already fixed. It reports the
same two baselines it reported before: 298 proof-size violations and 591
forbidden-name occurrences, both warnings.

## Merge order

Independent of item 1, and it can go first. It touches one Python
function and one shell script; no `.v` file changes, so no gate risk.
