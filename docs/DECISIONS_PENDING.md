# Pending decoder decisions

These decisions set the public proof claims. The named agreement propositions below are proof obligations, not proved theorems.

## C1: `decodeItem` input domain

**Recommended: approve C1-A.** The public result relation `C1AResult` requires `headerFits` for the complete input slice. Each caller must prove this condition. `decodeItemC1ASailAgreement` states the required agreement with `SailRun.runRlpDecodeItem` and `relateItem`. The Level 1 machine proof must establish the 40-byte result separately.

**Alternative: approve C1-B.** `C1BResult` specifies the exact machine result, including `binaryWrapCase`. `decodeItemC1BSailAgreement` requires Sail agreement only when `headerFits` holds. `decodeItemC1BWrapDivergence` states that Sail rejects a wrap input while the machine produces its specified result. The proved `decodeItemWrapWitness` shows one such input. A wrap result grants no payload ownership outside the input.

Choosing C1-B does not permit unconditional machine–Sail equality. Both choices still require a Level 1 proof against the ELF.

## Rung 2: nested-header domain

**Recommended: approve the candidate `allContiguousHeadersFit`.** The planned Rocq condition requires `headerFits` for the outer input and every reached child slice. The child slices follow the parent-header field walk. The existing `nestedC1AObligation` lists the call-site proof duty. The lemmas `outerHeaderFits` and `nestedHeaderDoesNotFit` prove that the outer condition alone does not discharge it.

This choice excludes a reached child whose long-length header wraps, even when the outer header fits. It keeps truncated and other malformed inputs when their reached headers satisfy `headerFits`. The alternative retains the outer domain and requires a separate `nestedC1AObligation` proof at each call. Sail cursor checks alone do not discharge those binary obligations. See [the domain note](RUNG2_DOMAIN_NOTE.md).

## C4: seven Sail host externs

Decide whether to supply verified bodies or approve named premises for these seven externs:

- Scratch: `host_scratch_reserve`, `host_scratch_store_byte`, `host_scratch_store_stateless_input`, `host_scratch_store_word`, and `host_scratch_truncate`.
- Hash: `scratch_keccak256` and `stateless_input_keccak256`.

Each premise must state completion, exact return values, scratch effects, input preservation, and unrelated-state preservation where applicable. The [extern audit](C4_TRANSACTION_HOST_EXTERNS.md) gives each declared type and its reached roots.

The Rocq lemma `transactionProjectionIgnoresHashOutputs` proves that changing constructed `sender` and `signing_hash` leaves `TransactionProjection` unchanged. It does not prove that the full Sail decoder action ignores either hash. C4 still needs the action-level state contract and a bridge from the Q18 transaction type to the C2 transaction type. Named premises remain part of the final trust claim unless their bodies receive proofs.
