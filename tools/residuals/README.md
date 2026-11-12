# Residual goal export (diagnostic only)

`export_block.py` turns one block into goal dirs for the solver-first, then-model step.

```
tools/residuals/export_block.py --block 6960 --bank _build/banks/<main-sha> --out <new dir> [--heavy]
tools/residuals/export_block.py --compare <run1>/MANIFEST.json <run2>/MANIFEST.json
```

The command runs in one resource-guard batch, with one scope for each compile.
It does these steps:

1. It probes the live Ltac bodies of the block's plain caller (`CALLERS24.json`).
   It keeps the copies that reparse faithfully (`ltac_probe.py`).
2. It runs the caller in census residual mode (`census_gen.py`, `core.v.in`, `res.v.in`).
   The SearchBudget size guard applies, and each solver call has a diagnostic limit
   (`--call-seconds`, default 300 s) inside the scope.
3. It collects each pure goal where the selected-facts solver fails.
   These are pure goals left open, and outermost failed `Lia.lia` or `tactics.bv_solve` calls.
   Copies with the same selected statement merge.
4. It writes `<out>/<block>-<n>/`: `goal.v`, `goal_full.v`, `FACTS.md`, `check.sh` (one scope,
   1 GiB booking), and `CONTROL`. The whole-context control marks each goal `true` (passed)
   or `unknown` (did not pass). The tool keeps unknown goals. Non-pure goals go to `spatial.tsv`.
5. It writes `MANIFEST.json`: block, bank, main sha, goal list, control results, and run times.

Goal ids follow log order, so the same bank and block give the same goal list.
`--compare` checks two manifests without their run times.
Control proofs and the census files stay in `<out>/_work/`, outside the goal dirs.

Use `--heavy` for heavy blocks (6a78, 698c, 69b0, 6ae0, 6a40, 6b08): the issue-10 probe class
with a 64 GiB scope. Timeouts are allowed here only because this is a diagnostic tool.
The tool writes no proof text and calls no model.

## Exact export and the residual loop

`tools/block/residual_loop.py` replaces this census exporter as the export source. It runs the
production tactics unchanged: a copy of the block caller imports `ZesuSsz.Automation2.ResidualExportOn`,
and the hooks in `Diagnostics.v` print the exact source of each pure goal at the split point and at the
end of `zesu_block2` (`ResidualExport.v`: every implicit argument and literal width is explicit, and the
premises are the facts that the conclusion reaches).

```
tools/block/residual_loop.py export --block 69a4 --caller <caller.v> --bank <bank> --out <run> [--stop-quiet S]
tools/block/residual_loop.py collect --run <run>     # check RUN/answers/<id>.v, minimize premises
tools/block/residual_loop.py register --run <run>    # add the passing lemmas to ZesuSsz/Residuals/Block800d<B>.v
tools/block/residual_loop.py rerun --run <run>       # compile the module and the caller; open goals start the next round
tools/block/residual_loop.py results --run <run>     # one RESULT line per goal, no proof text
```

The tool calls no model. The coordinator starts one standing agent per block on `RUN/tasks/`.
