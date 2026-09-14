Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.CallScratchSized.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsValueCall WriteSuccessExactEncoderU256Spec
  WriteSuccessExactTransactionsDataJump WriteSuccessExactTransactionsDataToBytes
  WriteSuccessExactEncoderBytes WriteSuccessObservation WriteSuccessOutputSemantic.

Definition transactionValueDataSourceFrame `{!islaG Sigma} `{!threadG}
    (sp w0 w1 w2 w3 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x12" ↦ᵣ RVal_Bits w2 ∗ "x13" ↦ᵣ RVal_Bits w3 ∗
   transactionValueFrame sp w0 w1 w2 w3 P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionValueDataSourceFrame) := I.

Definition transactionValueDataCaller `{!islaG Sigma} `{!threadG}
    (data size sp w0 w1 w2 w3 old6 old9 : bv 64) bytes tail
    (P : iProp Sigma) : iProp Sigma :=
  ("x8" ↦ᵣ RVal_Bits data ∗ "x22" ↦ᵣ RVal_Bits size ∗
   "x6" ↦ᵣ RVal_Bits old6 ∗ "x9" ↦ᵣ RVal_Bits old9 ∗
   bv_unsigned data ↦ₘ∗ bytes ∗ ⌜bv_unsigned size = length bytes⌝ ∗ P ∗
   (∀ stack2 : bv 64, instr_pre 0x151c4
     (encoderBytesExactPost data size sp (BV 64 0x151c4) bytes old6 data old9 stack2
       tail ("x22" ↦ᵣ RVal_Bits size ∗ transactionValueDataSourceFrame sp w0 w1 w2 w3 P ∗ True))) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionValueDataCaller) := I.

Lemma transactions_value_to_data `{!islaG Sigma} `{!threadG}
    (data size sp w0 w1 w2 w3 old6 old9 : bv 64) bytes tail (P : iProp Sigma) :
  transactionValuePost sp w0 w1 w2 w3
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)))
      (writeOutputEvents data size bytes tail))
    (transactionValueDataCaller data size sp w0 w1 w2 w3 old6 old9 bytes tail P) -∗
  transactionDataJumpEntry data size (BV 64 0x151b4) (sp - BV 64 48)%bv (BV 64 32)
    (transactionDataBytesFrame data size sp (BV 64 (mapIoContextAddress defaultMap)) old6 old9 bytes tail
      (transactionValueDataSourceFrame sp w0 w1 w2 w3 P)).
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & H12 & H13 & Hpayload & Hgap & Hret & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(H18 & H20 & Hword2 & H21 & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(H8 & H22 & H6 & H9 & Hbytes & %Hlen & HP & Hnext & _)".
  have HpayloadLength : length (writeSuccessU256WordsPayload w0 w1 w2 w3) = N.to_nat 32 by reflexivity.
  iPoseProof (call_scratch_reuse_sized sp (BV 64 0x151b4) _ 32 HpayloadLength Hlow) as "Hreuse".
  iEval (replace (Z_to_bv 64 (Z.of_N 32 + 16)) with (BV 64 48) by bv_solve; cbn) in "Hreuse".
  iPoseProof ("Hreuse" with "[$Hpayload $Hgap $Hret]") as "Hscratch".
  unfold transactionDataJumpEntry, transactionDataBytesFrame,
    transactionValueDataSourceFrame, transactionValueFrame.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_value_to_data.
