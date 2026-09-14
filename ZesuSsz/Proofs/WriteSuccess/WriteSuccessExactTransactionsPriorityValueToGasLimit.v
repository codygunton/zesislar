Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CallScratchSized.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsPriorityValueCall WriteSuccessExactTransactionsGasLimitCall
  WriteSuccessExactTransactionsGasPriceCall WriteSuccessExactEncoderU128
  WriteSuccessObservation WriteSuccessOutputSemantic.

Definition transactionFeeGasLimitFrame `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh tag low high : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x27" ↦ᵣ RVal_Bits tag ∗ "x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗
   (bv_unsigned sp - 32) ↦ₘ? 16 ∗ transactionGasPriceFrame sp gaslow gashigh P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionFeeGasLimitFrame) := I.

Lemma transactions_priority_value_to_gas_limit `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh tag low high value : bv 64) tail (P : iProp Sigma) :
  transactionPriorityValuePost sp low high
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail)
    ("x27" ↦ᵣ RVal_Bits tag ∗ transactionGasPriceFrame sp gaslow gashigh
      ("x26" ↦ᵣ RVal_Bits value ∗ P ∗ True) ∗ True)%I -∗
  instr_pre 0x15154 (transactionGasLimitPost sp value tail
    (transactionFeeGasLimitFrame sp gaslow gashigh tag low high P)) -∗
  transactionGasLimitEntry sp value (BV 64 0x15138) (BV 64 0x2401a0b8) (BV 64 16) tail
    (transactionFeeGasLimitFrame sp gaslow gashigh tag low high P).
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hpayload & Hgap & Hret & Hmmio & Htrace & Hfee & _)".
  iDestruct "Hfee" as "(Hhighword & Hlowword & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(Htag & Hgas & _)".
  iDestruct "Hgas" as "(HgasHigh & HgasLow & %HgasAlign & %HgasLow & %HgasHigh & Hvalue & _)".
  iDestruct "Hvalue" as "(H26 & HP & _)".
  have Hlen : length (writeSuccessU128WordsPayload low high) = N.to_nat 16 by reflexivity.
  have Hoffset : Z_to_bv 64 (Z.of_N 16 + 16) = BV 64 32 by bv_solve.
  iEval (rewrite -Hoffset) in "Hpayload".
  iPoseProof (call_scratch_reuse_sized sp (BV 64 0x15138) _ 16 Hlen Hlow
    with "[$Hpayload $Hgap $Hret]") as "Hscratch".
  iDestruct (mem_mapsto_uninit_split 16 with "Hscratch") as "[Hlower Hupper]"; first lia.
  iEval (replace (bv_unsigned sp - 32 + 16)%Z with (bv_unsigned sp - 16)%Z by lia) in "Hupper".
  iAssert (reg_col [(KindReg "x10", BitsShape 64)])%I with "[H10]" as "Harg".
  { rewrite reg_col_cons reg_col_nil. iSplitL "H10"; last done. iExists _; iFrame; done. }
  unfold transactionGasLimitEntry, transactionFeeGasLimitFrame, transactionGasPriceFrame.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_priority_value_to_gas_limit.
