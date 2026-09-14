Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsLayout WriteSuccessExactTransactionsFlagLoads WriteSuccessTransactionsSpec.

Lemma exact_transaction_row_byte prefix transaction suffix offset :
  Forall writeSuccessTransactionValid prefix ->
  writeSuccessTransactionValid transaction ->
  (offset < 288)%nat ->
  transactionRowByte
    (writeSuccessTransactionsBytes (prefix ++ transaction :: suffix))
    (288 * length prefix)%nat offset =
    bv_zero_extend 64 (writeSuccessTransactionByte transaction offset).
Proof.
  intros Hprefix Htransaction Hoffset.
  have Hlength := proj1 Htransaction.
  have Hrow : transactionRowByte
    (writeSuccessTransactionsBytes (prefix ++ transaction :: suffix))
    (288 * length prefix)%nat offset =
    transactionRowByte (writeSuccessTransactionBytes transaction) 0 offset.
  { unfold transactionRowByte.
    rewrite -drop_drop (exact_transactions_row_drop prefix transaction suffix Hprefix).
    rewrite drop_app_le; [|lia]. rewrite take_app_le; [reflexivity|].
    rewrite length_drop Hlength. lia. }
  rewrite Hrow exact_transaction_row_byte_extend; last (simpl; lia).
  reflexivity.
Qed.
Print Assumptions exact_transaction_row_byte.

