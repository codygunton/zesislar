Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessNativeCode WriteSuccessTransactionsSpec WriteSuccessExactTransactionsSpec
 WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsLayout
 WriteSuccessExactTransactionsLiveSpec WriteSuccessExactTransactionsLiveFieldFrame
 WriteSuccessExactTransactionsSourceFieldLayout WriteSuccessExactTransactionsSourceFieldEvents
 WriteSuccessExactTransactionsSourceSuffixModel
 WriteSuccessExactTransactionsLiveBlobFieldGuard
 WriteSuccessExactTransactionsLiveZeroGuard
 WriteSuccessExactTransactionsLiveSourceRegion
 WriteSuccessExactTransactionsLoopIndexEntry WriteSuccessExactTransactionsIndexCell
 WriteSuccessExactTransactionsIndexSourceEntry
 WriteSuccessExactTransactionsChainWordImage.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessExactTransactionsBlobCountTailModel WriteSuccessExactBlobHashesModel.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessExactTransactionsTypeTailModel.

Definition transactionLiveCurrentFieldEntry `{!islaG Sigma} `{!threadG}
    sp base transactions processed transaction rest bytes tail (P : iProp Sigma) : iProp Sigma :=
  transactionSourceFieldPost sp base bytes (length processed)
    (288 * length processed) (writeSuccessTransactionData transaction)
    (writeSuccessTransactionAccessBytes transaction)
    (transactionChainWordImage
      (transactionRowWord bytes (288 * length processed) 160)
      (transactionRowWord bytes (288 * length processed) 168))
    (writeSuccessTransactionAccessEntries transaction)
    (writeSuccessExactTransactionAfterBlobCountEvents sp transaction
      (writeSuccessExactTransactionsEvents sp rest tail))
    (transactionLiveFieldFrame sp base transactions processed transaction rest bytes P).

Lemma transactions_live_zero_blob_field_transition `{!islaG Sigma} `{!threadG}
    sp base transactions processed transaction rest bytes tail (P : iProp Sigma) :
  length (writeSuccessTransactionBlobBytes transaction) =
    (32 * length (writeSuccessTransactionBlobHashes transaction))%nat ->
  transactionRowWord bytes (288 * length processed) 232 =
    Z_to_bv 64 (Z.of_nat (length (writeSuccessTransactionBlobHashes transaction))) ->
  (Z.of_nat (length (writeSuccessTransactionBlobHashes transaction)) <
    18446744073709551616)%Z ->
  transactionRowWord bytes (288 * length processed) 224 =
    writeSuccessTransactionBlobPointer transaction ->
  transactionRowWord bytes (288 * length processed) 240 =
    writeSuccessTransactionAuthorizationPointer transaction ->
  (mapRamBase defaultMap <= bv_unsigned sp - 32)%Z ->
  writeSuccessTransactionAuthorizationBytes transaction = [] ->
  writeSuccessExactBlobHashesEvents sp 0
    (length (writeSuccessTransactionBlobHashes transaction))
    (writeSuccessTransactionBlobBytes transaction)
    (transactionSourceAfterBlobEvents sp bytes (288 * length processed) []
      (writeSuccessExactTransactionsEvents sp rest tail)) =
  writeSuccessExactTransactionAfterBlobCountEvents sp transaction
    (writeSuccessExactTransactionsEvents sp rest tail) ->
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15584
    (transactionLiveZeroCountEntry sp base transactions processed transaction rest bytes tail P) -∗
  □ instr_pre 0x153d0
    (transactionLiveCurrentFieldEntry sp base transactions processed transaction rest bytes tail P).
Proof.
  intros HblobLength HblobCount HblobBound HblobPointer HauthPointer HstackLow
    HauthBytes Hevents. iIntros "#Hcode #Hcount".
  unfold transactionLiveZeroCountEntry, transactionLiveCurrentFieldEntry.
  unfold transactionSourceAfterBlobEvents in Hevents.
  iApply (transactions_live_blob_field_guard sp base transactions processed
    transaction rest bytes (writeSuccessTransactionData transaction)
    (writeSuccessTransactionAccessBytes transaction)
    (transactionChainWordImage
      (transactionRowWord bytes (288 * length processed) 160)
      (transactionRowWord bytes (288 * length processed) 168))
    (writeSuccessTransactionAccessEntries transaction)
    (writeSuccessTransactionBlobBytes transaction) []
    (transactionSourceSignatureEvents sp bytes (288 * length processed)
      (writeSuccessExactTransactionsEvents sp rest tail))
    (writeSuccessExactTransactionAfterBlobCountEvents sp transaction
      (writeSuccessExactTransactionsEvents sp rest tail)) P
    ltac:(reflexivity) ltac:(symmetry; exact HauthBytes) HblobLength HblobCount HblobBound
    HblobPointer HauthPointer HstackLow Hevents with "Hcode Hcount").
Qed.
Print Assumptions transactions_live_zero_blob_field_transition.
