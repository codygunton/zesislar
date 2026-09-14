Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsNonceToGasPrice WriteSuccessExactTransactionsGasPriceCall WriteSuccessExactEncoderU128.

Lemma transactions_gas_price_nonce_frame_pack `{!islaG Sigma} `{!threadG}
    (sp nonce gaslow gashigh tag low high value : bv 64) tail (P : iProp Sigma) :
  transactionGasPricePost sp gaslow gashigh tail
    (transactionNonceGasPriceFrame sp nonce
      ("x27" ↦ᵣ RVal_Bits tag ∗
       ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗
        ("x26" ↦ᵣ RVal_Bits value ∗ P ∗ True) ∗ True) ∗ True)) -∗
  transactionGasPricePost sp gaslow gashigh tail
    ("x27" ↦ᵣ RVal_Bits tag ∗
     ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗
      ("x26" ↦ᵣ RVal_Bits value ∗ transactionNonceGasPriceFrame sp nonce P ∗ True) ∗ True) ∗ True)%I.
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hbytes & Hgap & Hret & Hmmio & Htrace & Hgas & _)".
  iDestruct "Hgas" as "(HgasHigh & HgasLow & %Halign & %Hlow & %Hhigh & Hnonce & _)".
  iDestruct "Hnonce" as "(Hnonceword & %HnonceAlign & %HnonceLow & %HnonceHigh & Hcaller & _)".
  iDestruct "Hcaller" as "(Htag & Hfee & _)".
  iDestruct "Hfee" as "(Hlowword & Hhighword & Hvalue & _)".
  iDestruct "Hvalue" as "(H26 & HP & _)".
  unfold transactionGasPricePost, encoderU128ExactPost, transactionGasPriceFrame, transactionNonceGasPriceFrame.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_gas_price_nonce_frame_pack.
