# Pending decoder decisions

These decisions set the public proof claims. The named agreement propositions below are proof obligations, not proved theorems.

## C1: `decodeItem` input domain

Decided 2026-10-04 by the user: the exact binary result relation, with the eight-byte length wrap recorded as the known bug `RlpLongLengthWrap` in the reused `KnownBugs` pattern (fixed constructor list; the compliance relation is agreement with Sail or an applicable known bug with its exact observation). `headerFits` remains a lemma callers may use to exclude the bug; it is not the public domain.

## Rung 2: nested-header domain

Resolved by the C1 pattern: no domain narrowing. A nested length wrap is the same known bug applied to the nested slice, under the agreement-modulo-known-bugs relation. `allContiguousHeadersFit` stays a candidate lemma only.

## C4: seven Sail host externs

Decided 2026-10-04 by the user: all seven reached externs are named premises. No verified implementation and no keccak verification is required. The premises must appear explicitly in each reviewed compliance type and in the gate's runtime-premise list, separately from global axioms.
