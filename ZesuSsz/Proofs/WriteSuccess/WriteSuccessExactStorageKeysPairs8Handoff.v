Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFlagLoads WriteSuccessExactStorageKeysPairs8
  WriteSuccessExactStorageKeysPairHandoff WriteSuccessExactStorageKeysLoads8
  WriteSuccessExactStorageKeysLoadHandoff WriteSuccessExactStorageKeysUpperLoadHandoff
  WriteSuccessExactStorageKeysLowerLoadHandoff WriteSuccessExactStorageKeysInitialLoads.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysPairsLoad8Resources.

Definition storageKeysPairs8Frame `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  ("x22" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length bytes)%nat⌝ ∗
   ⌜(0x20000000 <= base)%Z⌝ ∗ ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 16) + bv_unsigned (storageKeyByte bytes index 17) * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 18) * 65536 + bv_unsigned (storageKeyByte bytes index 19) * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 20) + bv_unsigned (storageKeyByte bytes index 21) * 256)) ∗
   storageKeysLoaded28Frame bytes index
     (storageKeysLoaded24Frame bytes index (storageKeysLoaded4Frame bytes index
       ("x18" ↦ᵣ RVal_Bits (transactionRowByte bytes index 14) ∗
        "x23" ↦ᵣ RVal_Bits (transactionRowByte bytes index 15) ∗ P ∗ True))) ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysPairs8Frame) := I.

Lemma storage_keys_load8_to_pairs8 `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  storageKeysLoads8Post row base bytes index (storageKeysPairs16Carry bytes index P) -∗
  storageKeysPairs8Entry
    (storageKeyByte bytes index 8) (storageKeyByte bytes index 9)
    (storageKeyByte bytes index 10) (storageKeyByte bytes index 11)
    (storageKeyByte bytes index 12) (storageKeyByte bytes index 13)
    (storageKeyByte bytes index 22) (storageKeyByte bytes index 23)
    (storageKeysPairs8Frame row base bytes index P).
Proof.
  iIntros "Hpost".
  iEval (unfold storageKeysLoads8Post, storageKeysPairs16Carry,
    storageKeysLoaded28Frame, storageKeysLoaded24Frame, storageKeysLoaded4Frame) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H8 & H26 & H1 & H21 & Hrow & Harray & %Hcursor & %Hbound12 & %Hlow & %Hhigh & (%Hbound32 & H6 & H7 & H28 & H9 & H25 & (H10 & H14 & H13 & H12 & (H11 & H5 & H17 & H16 & (H15 & H31 & H30 & H29 & (H24 & H20 & H18 & H23 & HP & _) & _) & _) & _) & _) & _)".
  iEval (unfold storageKeysPairs8Entry).
  iEval (rewrite
    -(storage_keys_row_byte bytes index 8 ltac:(lia))
    -(storage_keys_row_byte bytes index 9 ltac:(lia))
    -(storage_keys_row_byte bytes index 10 ltac:(lia))
    -(storage_keys_row_byte bytes index 11 ltac:(lia))
    -(storage_keys_row_byte bytes index 12 ltac:(lia))
    -(storage_keys_row_byte bytes index 13 ltac:(lia))
    -(storage_keys_row_byte bytes index 22 ltac:(lia))
    -(storage_keys_row_byte bytes index 23 ltac:(lia))).
  iEval (unfold storageKeysPairs8Frame, storageKeysLoaded28Frame,
    storageKeysLoaded24Frame, storageKeysLoaded4Frame).
  iFrame. done.
Qed.
Print Assumptions storage_keys_load8_to_pairs8.
