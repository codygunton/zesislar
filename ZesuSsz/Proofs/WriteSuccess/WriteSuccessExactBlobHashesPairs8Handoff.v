Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysPairHandoff.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFlagLoads WriteSuccessExactBlobHashesPairs8
  WriteSuccessExactBlobHashesPairHandoff WriteSuccessExactBlobHashesLoads8
  WriteSuccessExactBlobHashesUpperLoadHandoff WriteSuccessExactBlobHashesLowerLoadHandoff
  WriteSuccessExactBlobHashesInitialLoads WriteSuccessExactBlobHashesPairsLoad8Resources.

Definition blobPairs8Frame `{!islaG Sigma} `{!threadG}
    (row count : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  ("x19" ↦ᵣ RVal_Bits row ∗ "x27" ↦ᵣ RVal_Bits count ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length bytes)%nat⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗ ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 16) + bv_unsigned (storageKeyByte bytes index 17) * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 18) * 65536 + bv_unsigned (storageKeyByte bytes index 19) * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 20) + bv_unsigned (storageKeyByte bytes index 21) * 256)) ∗
   blobLoaded28Frame bytes index (blobLoaded24Frame bytes index
     (blobLoaded4Frame bytes index
       ("x24" ↦ᵣ RVal_Bits (transactionRowByte bytes index 14) ∗
        "x25" ↦ᵣ RVal_Bits (transactionRowByte bytes index 15) ∗ P ∗ True)%I)) ∗ True)%I.
Global Instance : LithiumUnfold (@blobPairs8Frame) := I.

Lemma blob_load8_to_pairs8 `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  blobLoads8Post row base bytes index (blobPairs16Carry count bytes index P) -∗
  blobPairs8Entry
    (storageKeyByte bytes index 8) (storageKeyByte bytes index 9)
    (storageKeyByte bytes index 10) (storageKeyByte bytes index 11)
    (storageKeyByte bytes index 12) (storageKeyByte bytes index 13)
    (storageKeyByte bytes index 22) (storageKeyByte bytes index 23)
    (blobPairs8Frame row count base bytes index P).
Proof.
  iIntros "Hpost".
  iEval (unfold blobLoads8Post, blobPairs16Carry, blobPairs16RemainingFrame,
    blobLoaded28Frame, blobLoaded24Frame, blobLoaded4Frame) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H8 & H9 & H18 & H26 & Hrow & Harray & %Hcursor & %Hbound12 & %Hlow & %Hhigh &
      (%Hbound32 & H6 & H7 & H28 & H25 & (Hcount & H20 & H21 &
        (H10 & H14 & H13 & H12 & (H11 & H5 & H17 & H16 &
          (H15 & H31 & H30 & H29 & (H22 & H23 & H24 & HP & _) & _) & _) & _) & _) & _) & _)".
  iEval (unfold blobPairs8Entry).
  iEval (rewrite
    -(storage_keys_row_byte bytes index 8 ltac:(lia))
    -(storage_keys_row_byte bytes index 9 ltac:(lia))
    -(storage_keys_row_byte bytes index 10 ltac:(lia))
    -(storage_keys_row_byte bytes index 11 ltac:(lia))
    -(storage_keys_row_byte bytes index 12 ltac:(lia))
    -(storage_keys_row_byte bytes index 13 ltac:(lia))
    -(storage_keys_row_byte bytes index 22 ltac:(lia))
    -(storage_keys_row_byte bytes index 23 ltac:(lia))).
  iEval (unfold blobPairs8Frame, blobLoaded28Frame, blobLoaded24Frame, blobLoaded4Frame).
  iFrame. done.
Qed.
Print Assumptions blob_load8_to_pairs8.
