Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsNonceCall WriteSuccessExactTransactionsGasPriceCall
  WriteSuccessExactEncoderU128 WriteSuccessExactEncoderIntFramedCall.

Definition transactionNonceGasPriceCaller `{!islaG Sigma} `{!threadG}
    (sp low high : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x24" ↦ᵣ RVal_Bits high ∗ "x25" ↦ᵣ RVal_Bits low ∗
   (bv_unsigned sp - 32) ↦ₘ? 16 ∗ ⌜0x20000000 <= bv_unsigned sp - 32⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionNonceGasPriceCaller) := I.

Definition transactionNonceGasPriceFrame `{!islaG Sigma} `{!threadG}
    (sp nonce : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 272) ↦ₘ nonce ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 32⌝ ∗ ⌜bv_unsigned sp + 280 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionNonceGasPriceFrame) := I.

Lemma transactions_nonce_to_gas_price `{!islaG Sigma} `{!threadG}
    (sp nonce low high : bv 64) tail (P : iProp Sigma) :
  transactionNoncePost sp nonce
    (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16) (writeSuccessU128WordsPayload low high) tail)
    (transactionNonceGasPriceCaller sp low high P) -∗
  instr_pre 0x15118 (transactionGasPricePost sp low high tail (transactionNonceGasPriceFrame sp nonce P)) -∗
  transactionGasPriceEntry sp low high (BV 64 0x15108) (BV 64 0x2401a0b8) tail
    (transactionNonceGasPriceFrame sp nonce P).
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hupper & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hnonce & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(Hhighword & Hlowword & Hlower & %Hscratchlow & HP & _)".
  iAssert ((bv_unsigned sp - 32) ↦ₘ? 32)%I with "[Hlower Hupper]" as "Hscratch".
  { iApply (mem_mapsto_uninit_combine 16 with "Hlower"); first lia.
    replace (bv_unsigned sp - 32 + 16)%Z with (bv_unsigned sp - 16)%Z by lia. iExact "Hupper". }
  iAssert (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64)])
    with "[H10 H11]" as "Hregs".
  { rewrite !reg_col_cons reg_col_nil. iSplitL "H10"; first (iExists _; iFrame; done).
    iSplitL "H11"; last done. iExists _; iFrame; done. }
  unfold transactionGasPriceEntry, transactionGasPriceFrame, transactionNonceGasPriceFrame.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_nonce_to_gas_price.
