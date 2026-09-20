# Determinism evidence

Data for `docs/ai/plan/PLAN_DETERMINISM.md`. One directory per work package
result, plus the lemma sets the packages measure.

## Lemma sets

- `profile_set.txt` — the WP1 profile set: 13 benchmark lemmas spanning
  frame sizes 22 to 266, plus the four merged segment lemmas.
- `expensive_set.txt` — the 244 expensive probes of the corpus (`timeout`,
  or at least 120 s), which the WP1 fit must predict.
- `expensive_no_context.txt` — the 118 of those whose corpus probe stored
  no context, so their frame has to be measured again.

- `iris_set.txt` — the 1,922 Iris lemmas of the corpus, the population WP1
  measures and the benchmark serves.

## WP1: where the seconds go

`wp1/README.md` holds the result, the numbers, and the one command block
that reproduces them.
