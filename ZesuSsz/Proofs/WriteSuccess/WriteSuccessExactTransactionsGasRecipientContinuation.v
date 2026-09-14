Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsGasToRecipient
  WriteSuccessExactTransactionsGasLimitCall WriteSuccessExactTransactionsPriorityValueToGasLimit
  WriteSuccessExactTransactionsNonceToGasPrice WriteSuccessExactTransactionsRecipientDataAccessRegion
  WriteSuccessExactTransactionsRecipientBranchHandoff WriteSuccessExactTransactionsRecipientValueRegion
  WriteSuccessExactTransactionsValueToData WriteSuccessExactTransactionsDataToAccessCount
  WriteSuccessExactTransactionsAccessCountCall.

Lemma transactions_gas_recipient_continuation `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh feeTag feeLow feeHigh value nonce tag first second w0 w1 w2 w3
      old12 old13 data size count old6 : bv 64) (last : bv 32) bytes tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x151d0 (transactionAccessCountPost sp count tail
    (transactionDataAccessFrame data size sp feeLow bytes
      (transactionValueDataSourceFrame sp w0 w1 w2 w3
        (transactionRecipientValueExitFrame sp tag first second last
          (transactionGasRecipientCarry sp gaslow gashigh feeTag feeHigh value nonce P))))) -∗
  □ instr_pre 0x15154 (transactionGasLimitPost sp value
    (transactionRecipientValueTrace sp tag first second w0 w1 w2 w3 last
      (transactionDataAccessOutputTrace data size sp count bytes tail))
    (transactionFeeGasLimitFrame sp gaslow gashigh feeTag feeLow feeHigh
      (transactionNonceGasPriceFrame sp nonce
        (transactionGasRecipientSourceCaller sp tag first second w0 w1 w2 w3 old12 old13
          data size count old6 last bytes P)))).
Proof.
  iIntros "#Hcode #Hnext".
  iPoseProof (transactions_recipient_data_access_region_correct sp tag first second w0 w1 w2 w3
    data size count (BV 64 0x15154) (BV 64 0x2401a0b8) (BV 64 8) old12 old13
    (sp - BV 64 16)%bv old6 feeLow last bytes tail
    (transactionGasRecipientCarry sp gaslow gashigh feeTag feeHigh value nonce P)
    with "Hcode Hnext") as "Hcallee".
  iModIntro. iApply (instr_pre_wand 0x15154 0x15154 false true with "Hcallee"); [done | done |].
  iApply transactions_gas_limit_to_recipient.
Qed.
Print Assumptions transactions_gas_recipient_continuation.
