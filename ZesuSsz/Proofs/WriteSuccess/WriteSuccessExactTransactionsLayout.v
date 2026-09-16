Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
Require Import ZesuSsz.Automation.ArrayByteValues.

Lemma exact_transactions_bytes_app prefix suffix :
  writeSuccessTransactionsBytes (prefix ++ suffix) =
    writeSuccessTransactionsBytes prefix ++ writeSuccessTransactionsBytes suffix.
Proof.
  induction prefix as [|transaction prefix IH]; simpl; [reflexivity|].
  rewrite IH app_assoc. reflexivity.
Qed.

Lemma exact_transactions_bytes_length transactions :
  Forall writeSuccessTransactionValid transactions ->
  length (writeSuccessTransactionsBytes transactions) =
    (288 * length transactions)%nat.
Proof.
  induction transactions as [|transaction transactions IH]; intros Hvalid;
    [reflexivity|].
  inversion Hvalid as [|head rest Hhead Htail]; subst.
  destruct Hhead as [Hlength _]. simpl.
  rewrite app_length Hlength (IH Htail). lia.
Qed.

Lemma exact_transactions_row_drop prefix transaction suffix :
  Forall writeSuccessTransactionValid prefix ->
  drop (288 * length prefix)%nat
    (writeSuccessTransactionsBytes (prefix ++ transaction :: suffix)) =
    writeSuccessTransactionBytes transaction ++ writeSuccessTransactionsBytes suffix.
Proof.
  intros Hvalid. rewrite exact_transactions_bytes_app.
  rewrite -(exact_transactions_bytes_length prefix Hvalid) drop_app_length.
  reflexivity.
Qed.

Lemma exact_transactions_own_valid `{!islaG Sigma} transactions :
  writeSuccessTransactionsOwn transactions -∗
  writeSuccessTransactionsOwn transactions ∗
    ⌜Forall writeSuccessTransactionValid transactions⌝ ∗ True.
Proof.
  induction transactions as [|transaction transactions IH].
  - simpl. iIntros "_". iSplit; [done|]. iSplit; [iPureIntro; constructor|done].
  - cbn [writeSuccessTransactionsOwn]. iIntros "(Hhead & Htail & _)".
    iDestruct "Hhead" as
      "(Hdata & Haccess & Hentries & Hblob & Hauth & %Hvalid & _)".
    iDestruct (IH with "Htail") as "(Htail & %HtailValid & _)".
    iSplitL; [iFrame; done|]. iSplit; [iPureIntro; constructor; assumption|done].
Qed.

Lemma exact_transaction_row_word prefix transaction suffix offset :
  Forall writeSuccessTransactionValid prefix ->
  writeSuccessTransactionValid transaction ->
  (offset + 8 <= 288)%nat ->
  transactionRowWord
    (writeSuccessTransactionsBytes (prefix ++ transaction :: suffix))
    (288 * length prefix)%nat offset =
    writeSuccessTransactionWord transaction offset.
Proof.
  intros Hprefix [Hlength Hvalid] Hoffset.
  unfold transactionRowWord, writeSuccessTransactionWord.
  rewrite -drop_drop (exact_transactions_row_drop prefix transaction suffix Hprefix).
  rewrite drop_app_le; [|lia]. rewrite take_app_le; [reflexivity|].
  rewrite length_drop Hlength. lia.
Qed.

Lemma exact_transaction_row_byte_extend bytes index offset :
  (index + offset < length bytes)%nat ->
  transactionRowByte bytes index offset = bv_zero_extend 64
    (default (BV 8 0) (bytes !! (index + offset)%nat)).
Proof.
  intros Hbound. unfold transactionRowByte.
  destruct (nth_lookup_or_length bytes (index + offset)%nat (BV 8 0))
    as [Hlookup|Hlookup]; [|lia].
  rewrite Hlookup. simpl. symmetry. apply array_byte_lookup. exact Hlookup.
Qed.

Print Assumptions exact_transactions_own_valid.
Print Assumptions exact_transactions_bytes_app.
Print Assumptions exact_transactions_bytes_length.
Print Assumptions exact_transactions_row_drop.
Print Assumptions exact_transaction_row_word.
Print Assumptions exact_transaction_row_byte_extend.
