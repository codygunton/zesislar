Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsValueDataContinuation
  WriteSuccessExactTransactionsValueToData WriteSuccessExactTransactionsValueCall
  WriteSuccessExactTransactionsValueAccessFrame WriteSuccessExactTransactionsDataToAccessCount
  WriteSuccessExactTransactionsAccessCountCall WriteSuccessExactEncoderBytes
  WriteSuccessExactEncoderU256Spec WriteSuccessObservation WriteSuccessOutputSemantic.

Definition transactionValueDataAccessCaller `{!islaG Sigma} `{!threadG}
    (data size sp count old6 old9 : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ("x8" ↦ᵣ RVal_Bits data ∗ "x22" ↦ᵣ RVal_Bits size ∗
   "x6" ↦ᵣ RVal_Bits old6 ∗ "x9" ↦ᵣ RVal_Bits old9 ∗
   bv_unsigned data ↦ₘ∗ bytes ∗ ⌜bv_unsigned size = length bytes⌝ ∗
   transactionDataAccessCaller sp count P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionValueDataAccessCaller) := I.

Lemma transactions_value_data_access_continuation `{!islaG Sigma} `{!threadG}
    (data size sp w0 w1 w2 w3 old6 old9 count : bv 64) bytes tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x151d0 (transactionAccessCountPost sp count tail
    (transactionDataAccessFrame data size sp old9 bytes
      (transactionValueDataSourceFrame sp w0 w1 w2 w3 P))) -∗
  □ instr_pre 0x151b4 (transactionValuePost sp w0 w1 w2 w3
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)))
      (writeOutputEvents data size bytes
        (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
          (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned count))) tail)))
    (transactionValueDataAccessCaller data size sp count old6 old9 bytes P)).
Proof.
  iIntros "#Hcode #Hnext".
  iPoseProof (transactions_value_data_continuation data size sp w0 w1 w2 w3 old6 old9 bytes
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned count))) tail)
    (transactionDataAccessCaller sp count P) with "Hcode") as "#Hcallee".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iAssert ([∗ list] instruction ∈ IslaTraces.write_success_51.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I as "#HaccessCode".
  { iApply instr_lookup_collect; last iExact "Hlookup". repeat constructor; reflexivity. }
  iAssert (□ ∀ stack2 : bv 64, instr_pre 0x151c4
    (encoderBytesExactPost data size sp (BV 64 0x151c4) bytes old6 data old9 stack2
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned count))) tail)
      ("x22" ↦ᵣ RVal_Bits size ∗ transactionValueDataSourceFrame sp w0 w1 w2 w3
        (transactionDataAccessCaller sp count P) ∗ True)))%I as "#HbytesNext".
  { iModIntro. iIntros (stack2).
    iPoseProof (transactions_data_access_continuation data size sp old6 old9 stack2 count bytes tail
      (transactionValueDataSourceFrame sp w0 w1 w2 w3 P)
      with "HaccessCode Hint Houtput Hnext") as "#Hcanonical".
    iApply (instr_pre_wand 0x151c4 0x151c4 true true with "Hcanonical"); [done | done |].
    iApply transactions_bytes_value_access_frame_pack. }
  iModIntro. iApply (instr_pre_wand 0x151b4 0x151b4 true true with "Hcallee"); [done | done |].
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & H12 & H13 & Hpayload & Hgap & Hret & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(H18 & H20 & Hword2 & H21 & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(H8 & H22 & H6 & H9 & HdataBytes & %Hlen & Haccess & _)".
  unfold transactionValuePost, encoderU256ExactPost, transactionValueFrame, transactionValueDataCaller.
  iFrame "HbytesNext". iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_value_data_access_continuation.
