Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysPairHandoff.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesLowPairs WriteSuccessExactBlobHashesLowPairsHandoff
  WriteSuccessExactBlobHashesUpperWords WriteSuccessExactBlobHashesWide.

Definition blobUpperWordsFrame `{!islaG Sigma} `{!threadG}
    (row count : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  ("x25" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 15) * 16777216)) ∗
   "x21" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 0) + bv_unsigned (storageKeyByte bytes index 1) * 256)) ∗
   "x22" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 2) * 65536 + bv_unsigned (storageKeyByte bytes index 3) * 16777216)) ∗
   "x23" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 2) * 65536)) ∗
   "x26" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 3) * 16777216)) ∗
   "x15" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 4) + bv_unsigned (storageKeyByte bytes index 5) * 256)) ∗
   "x31" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 5) * 256)) ∗
   "x30" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 6) * 65536)) ∗
   "x29" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 6) * 65536 + bv_unsigned (storageKeyByte bytes index 7) * 16777216)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 24) + bv_unsigned (storageKeyByte bytes index 25) * 256)) ∗
   "x5" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 25) * 256)) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 26) * 65536 + bv_unsigned (storageKeyByte bytes index 27) * 16777216)) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 28) + bv_unsigned (storageKeyByte bytes index 29) * 256)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 30) * 65536 + bv_unsigned (storageKeyByte bytes index 31) * 16777216)) ∗ blobWordFrame row count base bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@blobUpperWordsFrame) := I.

Lemma blob_low_pairs_to_upper_words `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  blobLowPairsPost (storageKeyByte bytes index 0) (storageKeyByte bytes index 1) (storageKeyByte bytes index 2) (storageKeyByte bytes index 3) (storageKeyByte bytes index 4) (storageKeyByte bytes index 5) (storageKeyByte bytes index 6) (storageKeyByte bytes index 7) (storageKeyByte bytes index 14) (storageKeyByte bytes index 15) (storageKeyByte bytes index 24) (storageKeyByte bytes index 25) (storageKeyByte bytes index 26) (storageKeyByte bytes index 27) (storageKeyByte bytes index 28) (storageKeyByte bytes index 29) (storageKeyByte bytes index 30) (storageKeyByte bytes index 31)
    (blobLowPairsFrame row count base bytes index P) -∗
  blobUpperWordsEntry (storageKeyByte bytes index 16) (storageKeyByte bytes index 17) (storageKeyByte bytes index 18) (storageKeyByte bytes index 19) (storageKeyByte bytes index 20) (storageKeyByte bytes index 21) (storageKeyByte bytes index 22) (storageKeyByte bytes index 23) (storageKeyByte bytes index 8) (storageKeyByte bytes index 9) (storageKeyByte bytes index 10) (storageKeyByte bytes index 11) (storageKeyByte bytes index 12) (storageKeyByte bytes index 13) (storageKeyByte bytes index 14) (storageKeyByte bytes index 15)
    (blobUpperWordsFrame row count base bytes index P).
Proof.
  iIntros "Hpost".
  iEval (unfold blobLowPairsPost, blobLowPairsFrame) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H24 & H25 & H21 & H22 & H23 & H26 & H15 & H31 & H30 & H29 & H11 & H5 & H17 & H16 & H10 & H14 & H13 & H12 &
      (Hrow & Hcount & Harray & %Hcursor & %Hbound & %Hlow & %Hhigh & H8 & H9 & H18 & H20 & H6 & H7 & H28 & HP & _) & _)".
  iAssert (reg_col [(KindReg "x13", BitsShape 64); (KindReg "x14", BitsShape 64);
    (KindReg "x17", BitsShape 64)]) with "[H13 H14 H17]" as "Hregs".
  { rewrite !reg_col_cons reg_col_nil.
    iSplitL "H13". { iExists _. iFrame. done. }
    iSplitL "H14". { iExists _. iFrame. done. }
    iSplitL "H17". { iExists _. iFrame. done. } done. }
  iEval (unfold blobUpperWordsEntry, blobUpperWordsFrame, blobWordFrame).
  iFrame. done.
Qed.
Print Assumptions blob_low_pairs_to_upper_words.
