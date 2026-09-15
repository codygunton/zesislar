Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessTransactionsSpec WriteSuccessExactTransactionsSpec
 WriteSuccessNativeCode WriteSuccessExactTransactionsSourceAuthorizationZeroContinuation
 WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsLayout
 WriteSuccessExactTransactionsLiveSpec
 WriteSuccessExactTransactionsSourceAuthorizationSpec
 WriteSuccessExactTransactionsSourceAuthorizationLiveFrame
 WriteSuccessExactTransactionsSourceBlobFeeFrame
 WriteSuccessExactTransactionsSourceSuffixModel
 WriteSuccessExactTransactionsChainWordImage
 WriteSuccessExactTransactionsMaxBlobFeeCount
 WriteSuccessExactAuthorizationsCount.

Definition transactionLiveZeroSignatureEntry `{!islaG Sigma} `{!threadG}
    sp base transactions processed transaction rest bytes tail (P : iProp Sigma) : iProp Sigma :=
  transactionSourceAuthorizationExit sp base bytes
    (length processed) (288 * length processed)
    (writeSuccessTransactionData transaction)
    (writeSuccessTransactionAccessBytes transaction)
    (transactionChainWordImage
      (transactionRowWord bytes (288 * length processed) 160)
      (transactionRowWord bytes (288 * length processed) 168))
    (writeSuccessTransactionAccessEntries transaction)
    (writeSuccessTransactionBlobBytes transaction) []
    (transactionSourceSignatureEvents sp bytes (288 * length processed)
      (writeSuccessExactTransactionsEvents sp rest tail))
    (transactionLiveAuthorizationRemainder sp base transactions processed transaction rest bytes P).

Definition transactionLiveZeroCountEntry `{!islaG Sigma} `{!threadG}
    sp base transactions processed transaction rest bytes tail (P : iProp Sigma) : iProp Sigma :=
  authorizationCountPost sp
    (transactionRowWord bytes (288 * length processed) 248)
    (transactionSourceSignatureEvents sp bytes (288 * length processed)
      (writeSuccessExactTransactionsEvents sp rest tail))
    (maxBlobFeeCountFrame sp
      (transactionRowWord bytes (288 * length processed) 80)
      (transactionRowWord bytes (288 * length processed) 88)
      (transactionSourceBlobFeeRetained sp base bytes (length processed)
        (288 * length processed) (writeSuccessTransactionData transaction)
        (writeSuccessTransactionAccessBytes transaction)
        (transactionChainWordImage
          (transactionRowWord bytes (288 * length processed) 160)
          (transactionRowWord bytes (288 * length processed) 168))
        (writeSuccessTransactionAccessEntries transaction)
        (writeSuccessTransactionBlobBytes transaction)
        (writeSuccessByteArrayOwn
          (transactionRowWord bytes (288 * length processed) 240) [] ∗
         transactionLiveAuthorizationRemainder sp base transactions processed
           transaction rest bytes P)%I)).

Lemma transactions_live_zero_count_transition `{!islaG Sigma} `{!threadG}
    sp base transactions processed transaction rest bytes tail (P : iProp Sigma) :
  (bv_unsigned sp + 1896 < machineRamEnd defaultMap)%Z ->
  transactionRowWord bytes (288 * length processed) 248 = BV 64 0 ->
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15620
    (transactionLiveZeroSignatureEntry sp base transactions processed transaction rest bytes tail P) -∗
  □ instr_pre 0x15584
    (transactionLiveZeroCountEntry sp base transactions processed transaction rest bytes tail P).
Proof.
  intros HstackHigh Hcount. iIntros "#Hcode #Hsignature".
  unfold transactionLiveZeroSignatureEntry, transactionLiveZeroCountEntry.
  iApply (transactions_source_authorization_zero_continuation sp base bytes
    (length processed) (288 * length processed)
    (writeSuccessTransactionData transaction)
    (writeSuccessTransactionAccessBytes transaction)
    (transactionChainWordImage
      (transactionRowWord bytes (288 * length processed) 160)
      (transactionRowWord bytes (288 * length processed) 168))
    (writeSuccessTransactionAccessEntries transaction)
    (writeSuccessTransactionBlobBytes transaction)
    (transactionSourceSignatureEvents sp bytes (288 * length processed)
      (writeSuccessExactTransactionsEvents sp rest tail))
    (transactionLiveAuthorizationRemainder sp base transactions processed transaction rest bytes P)
    HstackHigh Hcount with "Hcode Hsignature").
Qed.
Print Assumptions transactions_live_zero_count_transition.
