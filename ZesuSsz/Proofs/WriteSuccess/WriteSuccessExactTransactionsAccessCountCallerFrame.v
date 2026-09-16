Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsAccessCallerFrame WriteSuccessExactTransactionsDataAccessEntry
  WriteSuccessExactTransactionsAccessCountCall WriteSuccessExactEncoderIntFramedCall
  WriteSuccessExactTransactionsDataToAccessCount WriteSuccessExactTransactionsValueToData
  WriteSuccessExactTransactionsValueCall WriteSuccessExactTransactionsRecipientValueRegion
  WriteSuccessExactTransactionsRecipientAbsentToValue WriteSuccessExactTransactionsRecipientOutputToValue
  WriteSuccessExactTransactionsGasToRecipient WriteSuccessExactTransactionsGasPriceCall
  WriteSuccessExactTransactionsNonceToGasPrice WriteSuccessAccessListsSpec.

Lemma transactions_access_count_caller_frame `{!islaG Sigma} `{!threadG}
    (sp nonce gaslow gashigh feeTag feeLow feeHigh value tag first second w0 w1 w2 w3
      data size count x19 savedX22 : bv 64) (last : bv 32) dataBytes base entries accessBytes tail
    (F P : iProp Sigma) :
  transactionAccessCountPost sp count tail
    (transactionDataAccessFrame data size sp feeLow dataBytes
      (transactionValueDataSourceFrame sp w0 w1 w2 w3
        (transactionRecipientValueExitFrame sp tag first second last
          (transactionGasRecipientCarry sp gaslow gashigh feeTag feeHigh value nonce
            (F ∗ transactionAccessAfterDataCaller sp x19 savedX22 count base entries accessBytes P ∗ True)%I)))) ⊣⊢
  transactionAccessCountPost sp count tail
    (transactionDataAccessFrame data size sp feeLow dataBytes
      (transactionValueDataSourceFrame sp w0 w1 w2 w3
        (transactionRecipientValueExitFrame sp tag first second last
          (transactionGasRecipientCarry sp gaslow gashigh feeTag feeHigh value nonce
            (transactionAccessAfterDataCaller sp x19 savedX22 count base entries accessBytes (F ∗ P ∗ True)%I))))).
Proof.
  rewrite /transactionAccessCountPost /encoderIntExactFramedPost /transactionAccessCountFrame
    /transactionDataAccessFrame /transactionValueDataSourceFrame /transactionValueFrame
    /transactionGasRecipientCarry /transactionGasPriceFrame /transactionNonceGasPriceFrame
    /transactionRecipientValueExitFrame.
  destruct (bool_decide (tag = BV 64 0));
    rewrite /transactionRecipientAbsentValueSourceFrame /transactionRecipientValueSourceFrame.
  all: repeat f_equiv.
  all: rewrite bi.sep_True; apply transactions_access_caller_frame.
Qed.
Print Assumptions transactions_access_count_caller_frame.
