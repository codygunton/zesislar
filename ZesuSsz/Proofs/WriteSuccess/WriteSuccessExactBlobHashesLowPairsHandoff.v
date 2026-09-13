Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysPairHandoff.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFlagLoads WriteSuccessExactBlobHashesRemainingShifts
  WriteSuccessExactBlobHashesShiftsHandoff WriteSuccessExactBlobHashesLowPairs.

Definition blobLowPairsFrame `{!islaG Sigma} `{!threadG}
    (row count : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  ("x19" ↦ᵣ RVal_Bits row ∗ "x27" ↦ᵣ RVal_Bits count ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length bytes)%nat⌝ ∗
   ⌜(0x20000000 <= base)%Z⌝ ∗ ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 8) + bv_unsigned (storageKeyByte bytes index 9) * 256)) ∗
   "x9" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 10) * 65536 + bv_unsigned (storageKeyByte bytes index 11) * 16777216)) ∗
   "x18" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 12) + bv_unsigned (storageKeyByte bytes index 13) * 256)) ∗
   "x20" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 22) * 65536 + bv_unsigned (storageKeyByte bytes index 23) * 16777216)) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 16) + bv_unsigned (storageKeyByte bytes index 17) * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 18) * 65536 + bv_unsigned (storageKeyByte bytes index 19) * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 20) + bv_unsigned (storageKeyByte bytes index 21) * 256)) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLowPairsFrame) := I.

Lemma blob_shifts_to_low_pairs `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  blobRemainingShiftsPost (storageKeyByte bytes index 14) (storageKeyByte bytes index 15) (storageKeyByte bytes index 1) (storageKeyByte bytes index 2) (storageKeyByte bytes index 3) (storageKeyByte bytes index 5) (storageKeyByte bytes index 6) (storageKeyByte bytes index 7) (storageKeyByte bytes index 25) (storageKeyByte bytes index 26) (storageKeyByte bytes index 27) (storageKeyByte bytes index 29) (storageKeyByte bytes index 30) (storageKeyByte bytes index 31)
    (blobShiftsFrame row count base bytes index P) -∗
  blobLowPairsEntry (storageKeyByte bytes index 0) (storageKeyByte bytes index 1) (storageKeyByte bytes index 2) (storageKeyByte bytes index 3) (storageKeyByte bytes index 4) (storageKeyByte bytes index 5) (storageKeyByte bytes index 6) (storageKeyByte bytes index 7) (storageKeyByte bytes index 14) (storageKeyByte bytes index 15) (storageKeyByte bytes index 24) (storageKeyByte bytes index 25) (storageKeyByte bytes index 26) (storageKeyByte bytes index 27) (storageKeyByte bytes index 28) (storageKeyByte bytes index 29) (storageKeyByte bytes index 30) (storageKeyByte bytes index 31)
    (blobLowPairsFrame row count base bytes index P).
Proof.
  iIntros "Hpost".
  iEval (unfold blobRemainingShiftsPost, blobShiftsFrame) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H24 & H25 & H22 & H23 & H26 & H31 & H30 & H29 & H5 & H17 & H16 & H14 & H13 & H12 &
      (Hrow & Hcount & Harray & %Hcursor & %Hbound & %Hlow & %Hhigh & H8 & H9 & H18 & H20 & H6 & H7 & H28 & H21 & H10 & H11 & H15 & HP & _) & _)".
  iEval (unfold blobLowPairsEntry).
  iEval (rewrite
    -(storage_keys_row_byte bytes index 0 ltac:(lia))
    -(storage_keys_row_byte bytes index 4 ltac:(lia))
    -(storage_keys_row_byte bytes index 24 ltac:(lia))
    -(storage_keys_row_byte bytes index 28 ltac:(lia))).
  iEval (unfold blobLowPairsFrame).
  iFrame. done.
Qed.
Print Assumptions blob_shifts_to_low_pairs.
