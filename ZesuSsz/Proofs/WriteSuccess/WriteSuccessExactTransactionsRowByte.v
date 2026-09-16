Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLayout.

Lemma exact_transaction_row_byte prefix transaction suffix offset :
  Forall writeSuccessTransactionValid prefix ->
  writeSuccessTransactionValid transaction ->
  (offset < 288)%nat ->
  default (BV 8 0)
    (writeSuccessTransactionsBytes (prefix ++ transaction :: suffix) !!
      (288 * length prefix + offset)%nat) =
    writeSuccessTransactionByte transaction offset.
Proof.
  intros Hprefix [Hlength Hvalid] Hoffset.
  unfold writeSuccessTransactionByte.
  rewrite -(lookup_drop _ (288 * length prefix)%nat offset).
  rewrite (exact_transactions_row_drop prefix transaction suffix Hprefix).
  rewrite lookup_app_l; [reflexivity|rewrite Hlength; lia].
Qed.
Print Assumptions exact_transaction_row_byte.
