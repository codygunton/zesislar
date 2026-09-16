Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysPairHandoff.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesUpperWords WriteSuccessExactBlobHashesUpperWordsHandoff
  WriteSuccessExactBlobHashesLowerWords WriteSuccessExactBlobHashesWide.

Definition blobLowerWordsFrame `{!islaG Sigma} `{!threadG}
    (row count : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  ("x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(storageKeyByte bytes index 16);(storageKeyByte bytes index 17);(storageKeyByte bytes index 18);(storageKeyByte bytes index 19)])) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(storageKeyByte bytes index 20);(storageKeyByte bytes index 21);(storageKeyByte bytes index 22);(storageKeyByte bytes index 23)])) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(storageKeyByte bytes index 8);(storageKeyByte bytes index 9);(storageKeyByte bytes index 10);(storageKeyByte bytes index 11)])) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(storageKeyByte bytes index 12);(storageKeyByte bytes index 13);(storageKeyByte bytes index 14);(storageKeyByte bytes index 15)])) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 16) + bv_unsigned (storageKeyByte bytes index 17) * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 18) * 65536 + bv_unsigned (storageKeyByte bytes index 19) * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 20) + bv_unsigned (storageKeyByte bytes index 21) * 256)) ∗
   "x20" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 22) * 65536 + bv_unsigned (storageKeyByte bytes index 23) * 16777216)) ∗
   "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 10) * 65536 + bv_unsigned (storageKeyByte bytes index 11) * 16777216)) ∗
   "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 12) + bv_unsigned (storageKeyByte bytes index 13) * 256)) ∗
   "x24" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 14) * 65536 + bv_unsigned (storageKeyByte bytes index 15) * 16777216)) ∗
   "x25" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 15) * 16777216)) ∗
   "x23" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 2) * 65536)) ∗
   "x26" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 3) * 16777216)) ∗
   "x31" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 5) * 256)) ∗
   "x30" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (storageKeyByte bytes index 6) * 65536)) ∗
   blobWordFrame row count base bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLowerWordsFrame) := I.

Lemma blob_upper_to_lower_words `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  blobUpperWordsPost (storageKeyByte bytes index 16) (storageKeyByte bytes index 17) (storageKeyByte bytes index 18) (storageKeyByte bytes index 19) (storageKeyByte bytes index 20) (storageKeyByte bytes index 21) (storageKeyByte bytes index 22) (storageKeyByte bytes index 23) (storageKeyByte bytes index 8) (storageKeyByte bytes index 9) (storageKeyByte bytes index 10) (storageKeyByte bytes index 11) (storageKeyByte bytes index 12) (storageKeyByte bytes index 13) (storageKeyByte bytes index 14) (storageKeyByte bytes index 15)
    (blobUpperWordsFrame row count base bytes index P) -∗
  blobLowerWordsEntry (storageKeyByte bytes index 0) (storageKeyByte bytes index 1) (storageKeyByte bytes index 2) (storageKeyByte bytes index 3) (storageKeyByte bytes index 4) (storageKeyByte bytes index 5) (storageKeyByte bytes index 6) (storageKeyByte bytes index 7) (storageKeyByte bytes index 24) (storageKeyByte bytes index 25) (storageKeyByte bytes index 26) (storageKeyByte bytes index 27) (storageKeyByte bytes index 28) (storageKeyByte bytes index 29) (storageKeyByte bytes index 30) (storageKeyByte bytes index 31)
    (blobLowerWordsFrame row count base bytes index P).
Proof.
  iIntros "Hpost".
  iEval (unfold blobUpperWordsPost, blobUpperWordsFrame) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H13 & H14 & H8 & H17 & H6 & H7 & H28 & H20 & H9 & H18 & H24 &
      (H25 & H21 & H22 & H23 & H26 & H15 & H31 & H30 & H29 & H11 & H5 & H16 & H10 & H12 & Hframe & _) & _)".
  iAssert (reg_col [(KindReg "x5", BitsShape 64)]) with "[H5]" as "Hregs".
  { rewrite reg_col_cons reg_col_nil. iSplit; last done. iExists _. iFrame. done. }
  iEval (unfold blobLowerWordsEntry, blobLowerWordsFrame).
  iFrame.
Qed.
Print Assumptions blob_upper_to_lower_words.
