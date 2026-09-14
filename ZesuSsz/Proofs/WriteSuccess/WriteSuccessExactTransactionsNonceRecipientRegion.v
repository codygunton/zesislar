Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsGasRecipientContinuation
  WriteSuccessExactTransactionsGasToRecipient WriteSuccessExactTransactionsNoncePricePriorityRegion
  WriteSuccessExactTransactionsRecipientDataAccessRegion WriteSuccessExactTransactionsRecipientBranchHandoff
  WriteSuccessExactTransactionsRecipientValueRegion WriteSuccessExactTransactionsValueToData
  WriteSuccessExactTransactionsDataToAccessCount WriteSuccessExactTransactionsAccessCountCall.

Lemma transactions_nonce_recipient_region_correct `{!islaG Sigma} `{!threadG}
    (sp nonce gaslow gashigh feeTag feeLow feeHigh value tag first second w0 w1 w2 w3
      oldra old5 old11 old12 old13 data size count old6 : bv 64)
    (last : bv 32) bytes tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x151d0 (transactionAccessCountPost sp count tail
    (transactionDataAccessFrame data size sp feeLow bytes
      (transactionValueDataSourceFrame sp w0 w1 w2 w3
        (transactionRecipientValueExitFrame sp tag first second last
          (transactionGasRecipientCarry sp gaslow gashigh feeTag feeHigh value nonce P))))) -∗
  instr_body 0x150fc (transactionNoncePricePriorityEntry sp nonce gaslow gashigh feeTag feeLow feeHigh
    value oldra old5 old11
    (transactionRecipientValueTrace sp tag first second w0 w1 w2 w3 last
      (transactionDataAccessOutputTrace data size sp count bytes tail))
    (transactionGasRecipientSourceCaller sp tag first second w0 w1 w2 w3 old12 old13
      data size count old6 last bytes P)).
Proof.
  iStartProof. iIntros "#Hcode #Hnext".
  iPoseProof (transactions_gas_recipient_continuation with "Hcode Hnext") as "#HrecipientNext".
  iApply (transactions_nonce_price_priority_region_correct with "Hcode HrecipientNext").
Qed.
Print Assumptions transactions_nonce_recipient_region_correct.
