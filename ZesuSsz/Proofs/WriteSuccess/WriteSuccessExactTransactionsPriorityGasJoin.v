Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsBooleanToGasLimit WriteSuccessExactTransactionsPriorityValueToGasLimit
  WriteSuccessExactTransactionsGasPriceCall WriteSuccessExactTransactionsGasLimitCall
  WriteSuccessExactEncoderIntFramedCall.

Lemma transactions_absent_gas_frame_pack `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh tag low high value : bv 64) tail (P : iProp Sigma) :
  transactionGasLimitPost sp value tail (transactionGasLimitCallerFrame sp gaslow gashigh tag
    ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗ P ∗ True)) -∗
  transactionGasLimitPost sp value tail (transactionFeeGasLimitFrame sp gaslow gashigh tag low high P).
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hscratch & Hmmio & Htrace & Hlimit & _)".
  iDestruct "Hlimit" as "(Hvalue & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(Htag & Hlower & Hgas & _)".
  iDestruct "Hgas" as "(HgasHigh & HgasLow & %HgasAlign & %HgasLow & %HgasHigh & Hfee & _)".
  iDestruct "Hfee" as "(Hlowword & Hhighword & HP & _)".
  unfold transactionGasLimitPost, encoderIntExactFramedPost,
    transactionGasLimitFrame, transactionFeeGasLimitFrame, transactionGasPriceFrame.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_absent_gas_frame_pack.
