Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactStorageKeysLoads16 WriteSuccessExactStorageKeysLoads20
  WriteSuccessExactStorageKeysLoads28 WriteSuccessExactStorageKeysLoads24
  WriteSuccessExactStorageKeysLoads4 WriteSuccessExactStorageKeysLoads12
  WriteSuccessExactStorageKeysLoadHandoff WriteSuccessExactStorageKeysUpperLoadHandoff
  WriteSuccessExactStorageKeysLowerLoadHandoff WriteSuccessExactStorageKeysInitialLoads
  WriteSuccessExactStorageKeysPairs16.

Definition storageKeyByte (bytes : list (bv 8)) (index offset : nat) : bv 8 :=
  default (BV 8 0) (bytes !! (index + offset)%nat).

Lemma storage_keys_row_byte bytes index offset :
  (index + offset < length bytes)%nat ->
  transactionRowByte bytes index offset = bv_zero_extend 64 (storageKeyByte bytes index offset).
Proof.
  intros Hbound. unfold transactionRowByte, storageKeyByte.
  destruct (bytes !! (index + offset)%nat) eqn:Hlookup; simpl.
  - symmetry. apply array_byte_lookup. exact Hlookup.
  - apply lookup_ge_None in Hlookup. lia.
Qed.
Print Assumptions storage_keys_row_byte.

Definition storageKeysPairs16Frame `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  ("x22" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length bytes)%nat⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗ ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗
   "x9" ↦ᵣ RVal_Bits (transactionRowByte bytes index 22) ∗
   "x25" ↦ᵣ RVal_Bits (transactionRowByte bytes index 23) ∗
   storageKeysLoaded28Frame bytes index
     (storageKeysLoaded24Frame bytes index (storageKeysLoaded4Frame bytes index
       ("x24" ↦ᵣ RVal_Bits (transactionRowByte bytes index 12) ∗
        "x20" ↦ᵣ RVal_Bits (transactionRowByte bytes index 13) ∗
        "x18" ↦ᵣ RVal_Bits (transactionRowByte bytes index 14) ∗
        "x23" ↦ᵣ RVal_Bits (transactionRowByte bytes index 15) ∗ P ∗ True))) ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysPairs16Frame) := I.

Lemma storage_keys_initial_loads_to_pairs16 `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  storageKeysLoads12Post row base bytes index
    (storageKeysLoaded4Frame bytes index (storageKeysLoaded24Frame bytes index
      (storageKeysLoaded28Frame bytes index (storageKeysLoaded20Frame bytes index
        (storageKeysLoaded16Frame bytes index
          (⌜(index + 32 <= length bytes)%nat⌝ ∗ P ∗ True)%I))))) -∗
  storageKeysPairs16Entry
    (storageKeyByte bytes index 16) (storageKeyByte bytes index 17)
    (storageKeyByte bytes index 18) (storageKeyByte bytes index 19)
    (storageKeyByte bytes index 20) (storageKeyByte bytes index 21)
    (storageKeysPairs16Frame row base bytes index P).
Proof.
  iIntros "Hfirst".
  iEval (unfold storageKeysLoads12Post, storageKeysLoaded4Frame,
    storageKeysLoaded24Frame, storageKeysLoaded28Frame,
    storageKeysLoaded20Frame, storageKeysLoaded16Frame) in "Hfirst".
  iDestruct "Hfirst" as
    "(Hsys & H24 & H20 & H18 & H23 & Hrow & Harray & %Hcursor & %Hbound & %Hlow & %Hhigh & (H15 & H31 & H30 & H29 & (H11 & H5 & H17 & H16 & (H10 & H14 & H13 & H12 & (H8 & H26 & H9 & H25 & (H6 & H7 & H28 & H1 & HP & _) & _) & _) & _) & _) & _)".
  iEval (unfold storageKeysPairs16Entry).
  iDestruct "HP" as "(%Hbound32 & HP & _)".
  iEval (rewrite
    -(storage_keys_row_byte bytes index 16 ltac:(lia))
    -(storage_keys_row_byte bytes index 17 ltac:(lia))
    -(storage_keys_row_byte bytes index 18 ltac:(lia))
    -(storage_keys_row_byte bytes index 19 ltac:(lia))
    -(storage_keys_row_byte bytes index 20 ltac:(lia))
    -(storage_keys_row_byte bytes index 21 ltac:(lia))).
  iEval (unfold storageKeysPairs16Frame, storageKeysLoaded28Frame,
    storageKeysLoaded24Frame, storageKeysLoaded4Frame).
  iFrame. done.
Qed.
Print Assumptions storage_keys_initial_loads_to_pairs16.
