Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsNoncePriorityFrame
  WriteSuccessExactTransactionsNonceToGasPrice WriteSuccessExactTransactionsNonceCall
  WriteSuccessExactTransactionsGasPriceCall WriteSuccessExactTransactionsGasPricePriorityContinuation
  WriteSuccessExactTransactionsPriorityGasRegion WriteSuccessExactTransactionsPriorityValueToGasLimit
  WriteSuccessExactTransactionsGasLimitCall WriteSuccessExactEncoderU128.

Lemma transactions_nonce_price_priority_continuation `{!islaG Sigma} `{!threadG}
    (sp nonce gaslow gashigh tag low high value : bv 64) tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15154 (transactionGasLimitPost sp value tail
    (transactionFeeGasLimitFrame sp gaslow gashigh tag low high (transactionNonceGasPriceFrame sp nonce P))) -∗
  □ instr_pre 0x15108 (transactionNoncePost sp nonce
    (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16) (writeSuccessU128WordsPayload gaslow gashigh)
      (transactionPriorityGasTrace sp tag low high value tail))
    (transactionNonceGasPriceCaller sp gaslow gashigh
      ("x27" ↦ᵣ RVal_Bits tag ∗
       ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗
        ("x26" ↦ᵣ RVal_Bits value ∗ P ∗ True) ∗ True) ∗ True))).
Proof.
  iIntros "#Hcode #Hnext".
  iPoseProof (transactions_gas_price_priority_continuation sp gaslow gashigh tag low high value tail
    (transactionNonceGasPriceFrame sp nonce P) with "Hcode Hnext") as "#HpriceCanonical".
  iAssert (□ instr_pre 0x15118 (transactionGasPricePost sp gaslow gashigh
    (transactionPriorityGasTrace sp tag low high value tail)
    (transactionNonceGasPriceFrame sp nonce
      ("x27" ↦ᵣ RVal_Bits tag ∗
       ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗
        ("x26" ↦ᵣ RVal_Bits value ∗ P ∗ True) ∗ True) ∗ True))))%I as "#HpriceNext".
  { iModIntro. iApply (instr_pre_wand 0x15118 0x15118 true true with "HpriceCanonical"); [done | done |].
    iIntros "Hpost". iApply (transactions_gas_price_nonce_frame_pack with "Hpost"). }
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iApply (transactions_nonce_gas_price_continuation with "[] Hu128 Houtput HpriceNext").
  iApply instr_lookup_collect; last iExact "Hlookup".
  repeat constructor; reflexivity.
Qed.
Print Assumptions transactions_nonce_price_priority_continuation.
