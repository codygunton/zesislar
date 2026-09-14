Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CallScratchBytes.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsAccessCountCall WriteSuccessExactEncoderBytes WriteSuccessOutputSemantic.

Definition transactionDataAccessCaller `{!islaG Sigma} `{!threadG}
    (sp count : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 264) ↦ₘ count ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗ ⌜bv_unsigned sp + 272 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionDataAccessCaller) := I.

Definition transactionDataAccessFrame `{!islaG Sigma} `{!threadG}
    (data size sp old9 : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (("x6" ↦ᵣ: fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x8" ↦ᵣ RVal_Bits data ∗ "x9" ↦ᵣ RVal_Bits old9 ∗ "x22" ↦ᵣ RVal_Bits size ∗
   bv_unsigned data ↦ₘ∗ bytes ∗ (bv_unsigned sp - 48) ↦ₘ? 32 ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 272 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionDataAccessFrame) := I.

Lemma transactions_data_to_access_count `{!islaG Sigma} `{!threadG}
    data size sp old6 old9 stack2 count bytes tail (P : iProp Sigma) :
  encoderBytesExactPost data size sp (BV 64 0x151c4) bytes old6 data old9 stack2
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned count))) tail)
    ("x22" ↦ᵣ RVal_Bits size ∗ transactionDataAccessCaller sp count P ∗ True)%I -∗
  instr_pre 0x151d0 (transactionAccessCountPost sp count tail
    (transactionDataAccessFrame data size sp old9 bytes P)) -∗
  transactionAccessCountEntry sp count (BV 64 0x151c4) (BV 64 0x2401a0b8) size tail
    (transactionDataAccessFrame data size sp old9 bytes P).
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & H5 & H10 & H11 & Hbytes & Hmmio & Htrace & Hreturned & _)".
  iDestruct "Hreturned" as "(H6 & Hsp & H8 & H9 & HcountBytes & Hcountret & Hstack2 & Hsaved9 & Hsaved8 & Hret & Hcaller)".
  iDestruct "Hcaller" as "(H22 & Haccess & _)".
  iDestruct "Haccess" as "(Hcount & %Halign & %Hlow & %Hhigh & HP & _)".
  have Hlen : length (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size))) = 8%nat by reflexivity.
  iPoseProof (call_bytes_scratch_reuse sp (BV 64 0x151c4) (BV 64 0x15c90) stack2 old9 data _ Hlen Hlow
    with "[$HcountBytes $Hcountret $Hstack2 $Hsaved9 $Hsaved8 $Hret]") as "Hscratch".
  iDestruct (mem_mapsto_uninit_split 32 with "Hscratch") as "[Hlower Hupper]"; first lia.
  iEval (replace (bv_unsigned sp - 48 + 32)%Z with (bv_unsigned sp - 16)%Z by lia) in "Hupper".
  iAssert (reg_col [(KindReg "x10", BitsShape 64)])%I with "[H10]" as "Harg".
  { rewrite reg_col_cons reg_col_nil. iSplitL "H10"; last done. iExists _; iFrame; done. }
  unfold transactionAccessCountEntry, transactionDataAccessFrame.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_data_to_access_count.
