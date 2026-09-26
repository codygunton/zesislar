# Non-raising entry dispatch

This draft starts at `ed945cd3`. It ports the outer dispatch from
`measure-nonraising` at `dcf02bfe`. The user approved this v1 change.

The live and legacy entries first try `iStartProof`. Their existing Iris
branches remain unchanged. A non-BI goal uses `solve [zesu_finish]`.
If that attempt fails, `idtac` retains the original goal. The live v2
entry uses the same safe fallback. The prototype's inner search loop is
excluded because its measurement changed Iris outcomes adversely.
No support-fact import, hook, rule, or frozen legacy search path changes.

## Focused verification

Both test modules import `Automation.All`. The legacy test also requires
`Legacy.Finish` and calls its qualified tactic. No new test imports
`AllLegacy`. Both test modules cover pure arithmetic, transparent unfolding, an unknown
pure residual, Iris identity, an unknown Iris residual, and the native array
load at `0x15048`. The residual tests reject false closure. The machine
load uses `zesu_block` without hand steps. Each module prints six instances
of `Closed under the global context`.

The focused scratch files embed the edited entry text over immutable
`ed945cd357ac` build artifacts. The copied artifacts remain private.
Every scratch compile uses `resource_guard.sh batch` and `coqc_scratch.sh`.
At most two compiles run together.

| Entry | Exit | Seconds | Peak KiB |
|---|---:|---:|---:|
| Live | 0 | 5.777 | 828496 |
| Legacy, qualified entry | 0 | 4.527 | 869216 |

`rocq_health` passed with Coq 8.19.2+lsp. `rocq_start` failed with
`{"success":false,"error":"No node at point","reason":"crashed"}`.
The coordinator approved the guarded scratch fallback after this failure.
`rocq_compile_file`, with the explicit worktree and absolute file path,
entered the base tree and stopped before proof compilation:

```text
Error: Coq theory IslaTraces.allocator_get is defined twice:
- generated/isla-traces/allocator_get/dune:3
- generated/isla-traces/isla-traces/allocator_get/dune:3
```

`rocq_verify` passed both final six-test sources. Each result used
`shared_defs` and reported `assumptions: []`. The coordinator ran check-fast: session 96538, exit 0, 338.646 s,
peak 2708428 KiB. Benchmark measurements and the full preview remain
the coordinator's tasks.

## Measurement population

The existing determinism harness supplies these inputs:

- `ZesuSsz/Evidence/residuals/corpus_all_set.txt`, SHA-256
  `95c00989213e01cf438f35f687104687197f59ac3c45721af0ea88bdecf64372`.
- `ZesuSsz/Evidence/residuals/corpus.jsonl`, SHA-256
  `505ab2bc63ee951d67d4aaf4fe3d2c74a6a35d93684e20999ccb7f5156b18415`.

The population has 2315 unique `(module, lemma)` keys: 1922 Iris,
385 pure, and 8 unfold. All selected statements match between `434db041`
and `ed945cd3`. No selected statement is missing. The v1 Automation path
also matches between these roots, before this draft.

The applicable v1 baseline is
`benchmark/434db04166fa-corpus.json`. The corresponding prototype result is
`benchmark/dcf02bfe2d00-corpus-nr.json`. Both paths are relative to
`ZesuSsz/Evidence/residuals/` in the determinism worktree.
The standard root baseline is `benchmark/ed945cd357ac*.json`.

The coordinator uses `--no-reprobe` for the corpus measurement to match
its baseline. The standard 305-row and 48-row arms retain their existing
re-probe policy. Compare outcome, class, signature, and goal hash by key
and population. Accept more pure/unfold closures and fewer errors only.
No Iris outcome may worsen. The frozen collector and baseline files remain
unchanged.

The qualified legacy machine test has an initial-goal record in
`legacy-load-initial.jsonl`. Its raw capture is `legacy-load-initial.log`.
The hygiene parser counts the qualified tactic as one hand line. The
actual proof uses no manual step. The guarded capture passed in 4.528 s
with peak 888968 KiB and printed `Closed under the global context`.
