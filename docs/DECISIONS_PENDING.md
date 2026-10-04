# Pending decoder decisions

These decisions set the public proof claims. The named agreement propositions below are proof obligations, not proved theorems.

## C1: `decodeItem` input domain

**Recommended: approve C1-A.** The public result relation `C1AResult` requires `headerFits` for the complete input slice. Each caller must prove this condition. `decodeItemC1ASailAgreement` states the required agreement with `SailRun.runRlpDecodeItem` and `relateItem`. The Level 1 machine proof must establish the 40-byte result separately.

**Alternative: approve C1-B.** `C1BResult` specifies the exact machine result, including `binaryWrapCase`. `decodeItemC1BSailAgreement` requires Sail agreement only when `headerFits` holds. `decodeItemC1BWrapDivergence` states that Sail rejects a wrap input while the machine produces its specified result. The proved `decodeItemWrapWitness` shows one such input. A wrap result grants no payload ownership outside the input.

Choosing C1-B does not permit unconditional machine–Sail equality. Both choices still require a Level 1 proof against the ELF.

## Rung 2: nested-header domain

**Decision open: the candidate `allContiguousHeadersFit` needs revision.** The Rocq condition requires `headerFits` for the outer input and every reached child slice. The child slices follow the parent-header field walk. The existing `nestedC1AObligation` lists the call-site proof duty. The lemmas `outerHeaderFits` and `nestedHeaderDoesNotFit` prove that the outer condition alone does not discharge it.

The candidate excludes a reached child whose long-length header wraps, even when the outer header fits. It keeps truncated and other malformed inputs when their reached headers satisfy `headerFits`. The plain form retains the outer domain and requires a separate `nestedC1AObligation` proof at each call. Sail cursor checks alone do not discharge those binary obligations. See [the domain note](RUNG2_DOMAIN_NOTE.md).

The [Q29 vectors](../ZesuSsz/Evidence/PARENT_HEADER_VECTORS.json) show a remaining mismatch. Both domains include 20 field-boundary truncations, and Sail accepts them. Selected ELF guards reject several missing required fields by static analysis. Do not claim unconditional Sail agreement on this candidate domain.

## C4: seven Sail host externs

Decided 2026-10-04 by the user: all seven reached externs are named premises. No verified implementation and no keccak verification is required. The premises must appear explicitly in each reviewed compliance type and in the gate's runtime-premise list, separately from global axioms.
