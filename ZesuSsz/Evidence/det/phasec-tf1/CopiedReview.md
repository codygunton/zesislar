# TF1 copied-word junction

`tail_fields_copied_junction` converts the original copied-word predicate.
The converted view has one seven-word array at `sp+16`.
The array order is `[tail1; tail0; tail3; tail2; tail5; tail4; tail6]`.
One globally opaque predicate owns the untouched copied words.
The converted view has three top-level conjuncts, including `True`.
`tailFieldsCopiedUntouched_unfold` gives its exact view.
The junction equivalence preserves both conversion directions.
The segment proof does not split an array.

The proof uses four recorded MCP lines.
The focused compile passed.
`Print Assumptions tail_fields_copied_junction` returned:

```
Closed under the global context
```

The array conversion spent 0.582 seconds on representation rewriting.
The framing step spent 1.223 seconds.
`Qed` spent 0.482 seconds.
The root must gate and review this candidate before merge.

Final MCP verification passed with `assumptions: []`.
