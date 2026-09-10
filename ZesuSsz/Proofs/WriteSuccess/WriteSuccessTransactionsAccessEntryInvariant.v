From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAccessInvariantCore.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAccessInvariantStack.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAccessInvariantBounds.

Import ListNotations.

Lemma write_success_transactions_access_entry_invariant
    `{!islaG Sigma} (sp : bv 64) (base : Z)
    (entries : list writeSuccessAccessEntry) (bytes : list (bv 8))
    (Hentries : entries <> [])
    (Hbytes : bytes = writeSuccessAccessEntriesBytes entries)
    (Hlength : length bytes = (40 * length entries)%nat)
    (Hbound : (length entries < 2 ^ 64)%nat)
    (HspAlign : bv_unsigned sp `mod` 16 = 0)
    (HspLow : 0x20000000 <= bv_unsigned sp - 48)
    (HspHigh : bv_unsigned sp + 1896 < 0x40000000)
    (HbaseLow : 0x20000000 <= base)
    (HbaseHigh : base + Z.of_nat (length bytes) < 0x40000000) :
  ⊢ writeSuccessAccessListsInvariant sp base entries [] entries bytes [] bytes.
Proof.
  rewrite /writeSuccessAccessListsInvariant.
  iPoseProof (write_success_transactions_access_invariant_bounds
    base entries bytes True HbaseLow HbaseHigh with "[]") as "Hbounds".
  { done. }
  iPoseProof (write_success_transactions_access_invariant_stack
    sp _ HspAlign HspLow HspHigh with "Hbounds") as "Hstack".
  iApply (write_success_transactions_access_invariant_core
    entries bytes _ Hbytes Hlength Hbound with "Hstack").
Qed.
