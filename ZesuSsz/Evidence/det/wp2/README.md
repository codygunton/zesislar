# WP2: the finisher

Measured 2026-09-20 on branch `determinism`. Automation `ddc66074`;
the dispatch alone is `b37e3f23`; the baseline automation is `491bc41a`,
which is `origin/islaris-native` `ccf505e8` unchanged.

## What was built

1. **`zesu_finish` dispatches on the head of the goal.** One normalization
   pass, then a branch for an Iris entailment, a branch for a pure goal,
   and the shelved-side-condition branch. An entailment no longer reaches
   `reflexivity`, the bitvector entries, `lia` or `bv_solve`. Every entry
   that can act on an entailment keeps its old position relative to the
   others, so the finisher closes no fewer goals.
2. **`zesu_block` stops refusing a pure goal**, in both the current and the
   legacy automation. `iStartProof` fails on a goal that is not a bi
   assertion; the block tactic now hands such a goal to the finisher.

Two entries had to stay in both branches: `zesu_normalize_nat_powers` and
`zesu_saturate_alignment` work on the Coq context rather than the
conclusion, and leaving them out of the entailment branch stopped
`repeat progress` one step early and lost a proof.

## The primary metric, on both frozen baselines

| set | metric | baseline `ccf505e81f85` | after |
|---|---|---|---|
| full (305) | closed | 2 (0.66 %) | 2 (0.66 %) |
| full | C4 row | 13 | 13 |
| full | timeouts | 1 | 0 |
| full | median s | 8.0 | 9.8 |
| rule-15 (48) | closed | 2 (4.17 %) | 2 (4.17 %) |
| rule-15 | C4 row | 2 | 2 |
| rule-15 | timeouts | 1 | 0 |
| rule-15 | median s | 13.7 | 7.3 |

Closed fraction and the C4 row do not move on either baseline. The one
timeout in each set becomes a residual. The two median columns move in
opposite directions and neither is evidence: see the timing section.

## The former error row

The corpus counted 443 hand lines written only because `zesu_block` refused
to start on a goal that is not a bi assertion, over 388 records. Re-probed
against this automation:

| outcome | before | after |
|---|---|---|
| error | 388 | 1 |
| closed by `zesu_block.` alone | 0 | 111 (28.6 %) |
| residual, classified | 0 | 276 |

So the row is gone: 387 of 388 now reach the automation, 111 of them close
outright, and the rest become residuals the harness can classify (C2 88,
C1 56, C4 35, unknown 90). 327 of the 388 needed the legacy fix; the
dispatch commit alone fixed the 61 in current-automation modules, all 61.

## Timing: what the change costs and saves

A benchmark median is not evidence for a change of this size. Two probe
runs minutes apart differ by more than the change does: a first before and
after over 1,922 lemmas showed the 1 to 10 s band 28 percent slower and the
30 s band 20 percent faster -- and the same pattern appeared in the 1,364
lemmas pinned to the legacy automation, which that commit had not touched.

`tools/det/ab.py` runs both arms in one interleaved thread pool, against
two source trees, paired lemma by lemma. Over the 399 current-automation
lemmas, all finishing in both arms:

| variant | total wall | median ratio | lemmas over 100 s |
|---|---|---|---|
| dispatch (`b37e3f23`) | **-6.4 %** | +11 % | **-13 %**, 9,581 s to 8,050 s |
| `lia` and `bv_solve` capped at 5 s | +7.1 % | +27 % | +1 % |

The dispatch is kept: it is the only variant that lowers total seconds, and
it lowers them where the plan cares. Its cost falls on cheap lemmas, whose
absolute seconds are small: the 3 to 10 s band grows by 292 s in total
while the band over 100 s falls by 1,531 s.

## Why the acceptance is out of reach

The acceptance asks for the median `zesu_run` seconds at least halved. It
is not met, and finisher work cannot meet it.

- In the median band the finisher is 50.7 percent of the run
  (40 profiled lemmas, 254 s). A **free** finisher would halve the median
  and no more; the other 49 percent is the Lithium interpreter.
- The finisher's seconds are not waste. `bv_solve` over the WP1 probes:
  404 calls, median 0.06 s, p90 1.15 s, max 152.9 s, 598 s in total, with
  21 calls holding 403 of those seconds. Capping at 2 s lost nine proofs.
  Capping at 5 s keeps them all and is 7.1 percent slower overall, because
  the truncated calls were closing goals and the search then redid the
  work.
- Coq's `timeout` costs about 0.03 ms per call (measured: 200 calls of
  `lia` in 0.026 s, of `timeout 600 lia` in 0.032 s), so the cap's loss is
  behaviour, not instrument overhead.

The lever that remains is to *call* the expensive solver less often, not to
cap or skip it: a cheap sound test that a goal is one `bv_solve` can close.
That needs the shapes of the 21 heavy calls, which is the next measurement.

## Reproduce

```
make check-iris AGENT_BUILD_DIR=$PWD/_build/agents/det AGENT_JOBS=48
python3 tools/residual/benchmark.py --automation HEAD --jobs 44 \
  --build-dir _build/agents/det
python3 tools/residual/benchmark.py --automation HEAD --name rule15 \
  --set ZesuSsz/Evidence/residuals/benchmark_set_rule15.txt \
  --jobs 44 --build-dir _build/agents/det
python3 tools/residual/benchmark.py --automation HEAD --name notbi \
  --set ZesuSsz/Evidence/det/not_bi_set.txt --jobs 44 \
  --build-dir _build/agents/det
python3 tools/det/ab.py --set ZesuSsz/Evidence/det/wp2_ab_set.txt \
  --before 491bc41a --jobs 44 --out _build/agents/det/wp2_ab.jsonl
python3 tools/det/ab_report.py --records _build/agents/det/wp2_ab.jsonl \
  --field wall
```

A gate run on a loaded machine is not reproducible: two modules failed one
`check-iris` with `Error: Timeout!` from the automation's own `timeout 2`
entries, and passed on an idle machine. Coq's `timeout` is wall clock.
