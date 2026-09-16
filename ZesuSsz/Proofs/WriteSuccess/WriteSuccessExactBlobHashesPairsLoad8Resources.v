Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysPairHandoff.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFlagLoads WriteSuccessExactBlobHashesPairsLoad16
  WriteSuccessExactBlobHashesPairHandoff WriteSuccessExactBlobHashesLoads8
  WriteSuccessExactBlobHashesUpperLoadHandoff WriteSuccessExactBlobHashesLowerLoadHandoff
  WriteSuccessExactBlobHashesInitialLoads.

Definition blobPairs16Carry `{!islaG Sigma} `{!threadG}
    (count : bv 64) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (⌜(index + 32 <= length bytes)%nat⌝ ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 16) + bv_unsigned (storageKeyByte bytes index 17) * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 18) * 65536 + bv_unsigned (storageKeyByte bytes index 19) * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 20) + bv_unsigned (storageKeyByte bytes index 21) * 256)) ∗
   "x25" ↦ᵣ RVal_Bits (transactionRowByte bytes index 15) ∗
   blobPairs16RemainingFrame count bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@blobPairs16Carry) := I.

Lemma blob_pairs16_to_load8 `{!islaG Sigma} `{!threadG}
    row count base bytes index (old26 : bv 64) (P : iProp Sigma) :
  blobPairs16Post
    (storageKeyByte bytes index 16) (storageKeyByte bytes index 17)
    (storageKeyByte bytes index 18) (storageKeyByte bytes index 19)
    (storageKeyByte bytes index 20) (storageKeyByte bytes index 21)
    (blobByte15PostFrame row base bytes index
      (blobPairs16RemainingFrame count bytes index
        (⌜(index + 32 <= length bytes)%nat⌝ ∗ "x26" ↦ᵣ RVal_Bits old26 ∗ P ∗ True)%I)) -∗
  blobLoads8Entry row base bytes index (blobPairs16Carry count bytes index P).
Proof.
  iIntros "Hpost".
  iEval (unfold blobPairs16Post, blobByte15PostFrame, blobPairs16RemainingFrame) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H6 & H7 & H28 & H8 & H9 & H18 &
      (H25 & Hrow & Harray & %Hcursor & %Hbound16 & %Hlow & %Hhigh &
        (Hcount & H20 & H21 & Hrest & _) & _) & _)".
  iEval (unfold blobLoaded28Frame, blobLoaded24Frame, blobLoaded4Frame) in "Hrest".
  iDestruct "Hrest" as
    "(H10 & H14 & H13 & H12 & (H11 & H5 & H17 & H16 &
      (H15 & H31 & H30 & H29 & (H22 & H23 & H24 &
        (%Hbound32 & H26 & HP & _) & _) & _) & _) & _)".
  iAssert (reg_col [(KindReg "x8", BitsShape 64); (KindReg "x9", BitsShape 64);
    (KindReg "x18", BitsShape 64); (KindReg "x26", BitsShape 64)])
    with "[H8 H9 H18 H26]" as "Hregs".
  { rewrite !reg_col_cons reg_col_nil. iSplitL "H8".
    { iExists _. iFrame. done. }
    iSplitL "H9". { iExists _. iFrame. done. }
    iSplitL "H18". { iExists _. iFrame. done. }
    iSplitL "H26". { iExists _. iFrame. done. } done. }
  iEval (unfold blobLoads8Entry, blobPairs16Carry, blobPairs16RemainingFrame,
    blobLoaded28Frame, blobLoaded24Frame, blobLoaded4Frame).
  iFrame. iPureIntro. lia.
Qed.
Print Assumptions blob_pairs16_to_load8.
