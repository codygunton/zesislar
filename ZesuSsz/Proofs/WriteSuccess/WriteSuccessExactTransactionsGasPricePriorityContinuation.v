Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsPriorityGasRegion
  WriteSuccessExactTransactionsGasPriceCall WriteSuccessExactTransactionsGasPriceToPriority
  WriteSuccessExactTransactionsPriorityValueToGasLimit WriteSuccessExactTransactionsGasLimitCall.

Lemma transactions_gas_price_priority_continuation `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh tag low high value : bv 64) tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15154 (transactionGasLimitPost sp value tail
    (transactionFeeGasLimitFrame sp gaslow gashigh tag low high P)) -∗
  □ instr_pre 0x15118 (transactionGasPricePost sp gaslow gashigh
    (transactionPriorityGasTrace sp tag low high value tail)
    ("x27" ↦ᵣ RVal_Bits tag ∗
     ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗
      ("x26" ↦ᵣ RVal_Bits value ∗ P ∗ True) ∗ True) ∗ True)).
Proof.
  iIntros "#Hcode #Hnext".
  iPoseProof (transactions_priority_gas_native_pre sp gaslow gashigh tag low high value tail P
    with "Hcode Hnext") as "#Hpriority".
  iModIntro. iApply (instr_pre_wand 0x15118 0x15118 true true with "Hpriority"); [done | done |].
  iIntros "Hpost". iApply (transactions_gas_price_to_priority with "Hpost").
Qed.
Print Assumptions transactions_gas_price_priority_continuation.
