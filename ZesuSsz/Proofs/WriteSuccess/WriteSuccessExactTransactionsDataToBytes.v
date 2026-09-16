Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsDataJump WriteSuccessExactEncoderBytes
  WriteSuccessObservation WriteSuccessOutputSemantic.

Definition transactionDataBytesFrame `{!islaG Sigma} `{!threadG}
    (data size sp old5 old6 old9 : bv 64) (bytes : list (bv 8)) tail
    (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ "x5" ↦ᵣ RVal_Bits old5 ∗ "x6" ↦ᵣ RVal_Bits old6 ∗
   "x9" ↦ᵣ RVal_Bits old9 ∗ (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   bv_unsigned data ↦ₘ∗ bytes ∗ ⌜bv_unsigned size = length bytes⌝ ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
     (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)))
     (writeOutputEvents data size bytes tail)) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗ P ∗
   (∀ stack2 : bv 64, instr_pre 0x151c4
     (encoderBytesExactPost data size sp (BV 64 0x151c4) bytes old6 data old9 stack2
       tail ("x22" ↦ᵣ RVal_Bits size ∗ P ∗ True))) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionDataBytesFrame) := I.

Lemma transactions_data_to_bytes `{!islaG Sigma} `{!threadG}
    data size sp old5 old6 old9 bytes tail (P : iProp Sigma) :
  transactionDataJumpPost data size (transactionDataBytesFrame data size sp old5 old6 old9 bytes tail P) -∗
  encoderBytesExactSpec data size sp (BV 64 0x151c4) bytes tail
    ("x22" ↦ᵣ RVal_Bits size ∗ P ∗ True)%I.
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H8 & H22 & H1 & H10 & H11 & Hframe & _)".
  iDestruct "Hframe" as "(Hsp & H5 & H6 & H9 & Hscratch & Hbytes & %Hlen & Hmmio & Htrace & %Halign & %Hlow & %Hhigh & HP & Hnext & _)".
  iDestruct (encoder_bytes_uninit_48_to_words with "Hscratch") as (w0 w1 w2 w3 w4 w5)
    "(H0 & Hs1 & H2 & H3 & H4 & Hs5)".
  iSpecialize ("Hnext" $! w2).
  unfold encoderBytesExactSpec.
  iExists old5, old6, data, old9, w0, w1, w2, w3, w4, w5.
  iFrame. repeat iSplit; try done; iPureIntro; bv_solve.
Qed.
Print Assumptions transactions_data_to_bytes.
