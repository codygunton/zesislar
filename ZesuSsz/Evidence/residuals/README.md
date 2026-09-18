# Residual corpus

`corpus.jsonl` holds one JSON record per probed proof, in the shape of
section 4.2 of `PLAN_RESIDUAL_CORPUS.md`. Each record keeps the first 8 KiB of
the residual goal and its SHA-256. The full goal text stays untracked, in
`_build/agents/corpus/residuals/<sha>.txt`.

Rebuild or extend the corpus with:

```
python3 tools/residual/run_corpus.py --tier 1 --jobs 12
python3 tools/residual/report.py --tier 1
```

Both are idempotent: a proof that already has a record at the current
`origin/islaris-native` commit is skipped.
