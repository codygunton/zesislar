# WP1: where the seconds go

Measured 2026-09-20 on branch `determinism`, automation at `30550341`.

## What was measured

Four probes, all built from the module text up to the target `Proof.`, with
the hand lines dropped. None of them edits a proof.

| probe | what it costs | what it gives |
|---|---|---|
| `prefix` | compiles the module text, then `Abort` | the seconds every probe pays before the automation starts |
| `stepped` | the introduction phase plus 600 interpreter steps | the frame the search sees, and how many of its hypotheses are memory points |
| `counted` | the whole block automation, plus one failing `lazymatch` per step | the automation seconds, and how many instructions the block stepped |
| `timed` | the same, with a `time` label on every finisher entry, every alternative of the search loop, and every alternative of Lithium's `liStep` | seconds and calls per entry |

The copies of `zesu_finish`, `zesu_run_pass`, `zesu_block` and `liStep` are
generated from the automation source at probe time (`tools/det/timed.py`),
so they cannot drift from the automation they measure. `Show Ltac Profile`
cannot be used here: Coq's profiler raises "invalid stack (wrong self node)"
as soon as Lithium backtracks into a profiled tactic, which every proof that
steps an instruction does.

Population: the 1,922 Iris lemmas of the corpus. 1,832 have a frame, 1,764 a
finished `counted` run, 1,761 both plus a prefix cost.

## Result 1: the finisher is the cost

Over the 16 lemmas that the `timed` probe finished (1,562 s of run time):

| bucket | seconds | share |
|---|---|---|
| `zesu_finish`, all entries | 978.3 | 62.6 % |
| the `repeat first [ … ]` search loop | 546.7 | 35.0 % |
| of which Lithium's `liStep` | 325.5 | 20.8 % |
| of which `liFindInContext` | 108.6 | 7.0 % |
| the introduction phase | 12.3 | 0.8 % |

Inside the finisher, one entry dominates: `bv_solve` costs 576.8 s in 98
calls, 5.9 s per call and **36.9 % of all run seconds**. `lia` adds 8.1 %.
The battery of alternatives that the search loop tries and that fail costs
almost nothing (0 to 12 s per lemma): the linear battery is expensive
because of what its entries do when they run, not because there are forty
of them.

## Result 2: lookup cost is quadratic in the frame

`liFindInContext` seconds per call, against the frame the search sees:

| frame | 20-39 | 56-67 | 65-84 | 91-125 |
|---|---|---|---|---|
| ms per call | 0.2-4.0 | 1.9-7.9 | 15-23 | 33-35 |

From frame 38 to frame 125 the cost per call rises by a factor of 12 for a
factor of 3.3 in frame: an exponent near 2.2. So the lookup is quadratic in
the frame, as rule 20 of the compliance plan says. Its share of today's
seconds is only 7 % because the finisher dominates; after WP2 it is the next
ceiling.

## Result 3: the fit, and why it cannot reach a factor of two

The model is a power law in frame size and instruction count, fitted by
weighted least squares on the logarithms (`tools/det/fit.py`):

```
fit on 1761 lemmas: const +1.967  log_frame -0.309  log_instructions +0.209
                    log_frame^2 +0.158  log_instructions^2 +0.095
within a factor of two: population 63.9 %, the 244 expensive probes 43.3 %
                        (49.6 % of the 123 that finished)
```

With the 244 held out of the training set the test share falls to 29.2 %.
**The acceptance is not met, and no fit of these two variables can meet it.**
Inside one cell of the (frame band, instruction band) grid the seconds
spread p90/p10 by a median factor of **5.8**, and the two bands explain only
**40.2 %** of the variance in log seconds. A factor-of-two prediction needs a
residual spread under 4; the data has 5.8.

Result 1 says why. More than half of every proof's seconds are the finisher,
and the finisher's cost is decided by the *shape* of the goals it meets --
whether `bv_solve` is invoked on a goal it cannot close -- not by how wide
the frame is or how long the block is. Two lemmas with the same frame and
the same instruction count differ by an order of magnitude when one of them
hands `bv_solve` six goals it cannot close.

The prediction becomes possible only after WP2 removes that term. The
splitting policy of WP8 therefore waits for WP2, and its predictor will be
instruction count times a per-step cost measured by the `stepped` probe,
not a fit of frame size alone.

## Decision for WP3

WP3a, the extension-level index, first. The evidence for the interpreter
level (WP3b) is real -- the quadratic term is inside Lithium's own
`liFindInContext` -- but it is 7 % of today's seconds and at most 21 % even
if the whole `liStep` were free. A fork is not justified before WP2 lands
and the finisher stops hiding it. Re-measure the share after WP2.

## Reproduce

From the worktree root, with the theory built into `_build/agents/det`:

```
make check-iris AGENT_BUILD_DIR=$PWD/_build/agents/det AGENT_JOBS=48
for shape in prefix stepped counted; do
  python3 tools/det/run_profile.py --set ZesuSsz/Evidence/det/iris_set.txt \
    --shape $shape --jobs 48 --seconds 600 \
    --out _build/agents/det/iris_$shape.jsonl
done
python3 tools/det/run_profile.py --set ZesuSsz/Evidence/det/profile_set.txt \
  --shape timed --jobs 17 --seconds 3600 --out _build/agents/det/wp1_timed.jsonl
python3 tools/det/join.py --frames _build/agents/det/iris_frames.jsonl \
  --counted _build/agents/det/iris_counted.jsonl \
  --prefix _build/agents/det/iris_prefix.jsonl --out _build/agents/det/joined.jsonl
python3 tools/det/wp1_table.py --timed _build/agents/det/wp1_timed.jsonl \
  --frames _build/agents/det/iris_frames.jsonl \
  --counted _build/agents/det/iris_counted.jsonl \
  --out ZesuSsz/Evidence/det/wp1/profile_table.jsonl \
  --entries ZesuSsz/Evidence/det/wp1/entries.json
python3 tools/det/fit.py --joined _build/agents/det/joined.jsonl \
  --test-set ZesuSsz/Evidence/det/expensive_set.txt \
  --out ZesuSsz/Evidence/det/wp1/fit.json
```

`measurements.jsonl` is the joined table these commands produce;
`profile_table.txt` is the printed decomposition.
