Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysPairHandoff.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFlagLoads WriteSuccessExactBlobHashesLoads0
  WriteSuccessExactBlobHashesPairHandoff WriteSuccessExactBlobHashesPairs8Load0
  WriteSuccessExactBlobHashesUpperLoadHandoff WriteSuccessExactBlobHashesLowerLoadHandoff
  WriteSuccessExactBlobHashesInitialLoads WriteSuccessExactBlobHashesRemainingShifts.

Definition blobShiftsFrame `{!islaG Sigma} `{!threadG}
    (row count : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  ("x19" ↦ᵣ RVal_Bits row ∗ "x27" ↦ᵣ RVal_Bits count ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length bytes)%nat⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗ ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗
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
   "x21" ↦ᵣ RVal_Bits (transactionRowByte bytes index 0) ∗
   "x10" ↦ᵣ RVal_Bits (transactionRowByte bytes index 28) ∗
   "x11" ↦ᵣ RVal_Bits (transactionRowByte bytes index 24) ∗
   "x15" ↦ᵣ RVal_Bits (transactionRowByte bytes index 4) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobShiftsFrame) := I.

Lemma blob_load0_to_shifts `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  blobLoads0Post row base bytes index (blobPairs8Carry count bytes index P) -∗
  blobRemainingShiftsEntry
    (storageKeyByte bytes index 14) (storageKeyByte bytes index 15)
    (storageKeyByte bytes index 1) (storageKeyByte bytes index 2) (storageKeyByte bytes index 3)
    (storageKeyByte bytes index 5) (storageKeyByte bytes index 6) (storageKeyByte bytes index 7)
    (storageKeyByte bytes index 25) (storageKeyByte bytes index 26) (storageKeyByte bytes index 27)
    (storageKeyByte bytes index 29) (storageKeyByte bytes index 30) (storageKeyByte bytes index 31)
    (blobShiftsFrame row count base bytes index P).
Proof.
  iIntros "Hpost".
  iEval (unfold blobLoads0Post, blobPairs8Carry,
    blobLoaded28Frame, blobLoaded24Frame, blobLoaded4Frame) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H0 & H1 & H2 & H3 & Hrow & Harray & %Hcursor & %Hbound4 & %Hlow & %Hhigh & (%Hbound32 & Hcount & H8 & H21 & H20 & H9 & H6 & H7 & H28 & (H10 & H14 & H13 & H12 & (H11 & H5 & H17 & H16 & (H15 & H31 & H30 & H29 & (H18 & H23 & HP & _) & _) & _) & _) & _) & _)".
  iEval (unfold blobRemainingShiftsEntry).
  iEval (rewrite
    -(storage_keys_row_byte bytes index 14 ltac:(lia))
    -(storage_keys_row_byte bytes index 15 ltac:(lia))
    -(storage_keys_row_byte bytes index 1 ltac:(lia))
    -(storage_keys_row_byte bytes index 2 ltac:(lia))
    -(storage_keys_row_byte bytes index 3 ltac:(lia))
    -(storage_keys_row_byte bytes index 5 ltac:(lia))
    -(storage_keys_row_byte bytes index 6 ltac:(lia))
    -(storage_keys_row_byte bytes index 7 ltac:(lia))
    -(storage_keys_row_byte bytes index 25 ltac:(lia))
    -(storage_keys_row_byte bytes index 26 ltac:(lia))
    -(storage_keys_row_byte bytes index 27 ltac:(lia))
    -(storage_keys_row_byte bytes index 29 ltac:(lia))
    -(storage_keys_row_byte bytes index 30 ltac:(lia))
    -(storage_keys_row_byte bytes index 31 ltac:(lia))).
  iEval (unfold blobShiftsFrame).
  iFrame. done.
Qed.
Print Assumptions blob_load0_to_shifts.
