From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.

Ltac solve_blocker_empty_slice :=
  exists 0%Z; split;
  [change (0 <= 0 < 18446744073709551616)%Z; lia|];
  split; [native_compute; reflexivity|];
  split; native_compute; reflexivity.

Lemma writeSuccessBlockerDeposits :
  writeSuccessMemorySlice writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 608
    (observationDeposits writeSuccessBlockerDecoded).
Proof. solve_blocker_empty_slice. Qed.

Lemma writeSuccessBlockerWithdrawalRequests :
  writeSuccessMemorySlice writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 624
    (observationWithdrawalRequests writeSuccessBlockerDecoded).
Proof. solve_blocker_empty_slice. Qed.

Lemma writeSuccessBlockerConsolidations :
  writeSuccessMemorySlice writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 640
    (observationConsolidations writeSuccessBlockerDecoded).
Proof. solve_blocker_empty_slice. Qed.

Lemma writeSuccessBlockerBuilderDeposits :
  writeSuccessMemorySlice writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 656
    (observationBuilderDeposits writeSuccessBlockerDecoded).
Proof. solve_blocker_empty_slice. Qed.

Lemma writeSuccessBlockerBuilderExits :
  writeSuccessMemorySlice writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 672
    (observationBuilderExits writeSuccessBlockerDecoded).
Proof. solve_blocker_empty_slice. Qed.

Lemma writeSuccessBlockerParentBeaconRoot :
  writeSuccessMemoryBytes writeSuccessBlockerRepresentedMemory
    (writeSuccessBlockerOwner + 688)
    (observationParentBeaconRoot writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerChainId :
  writeSuccessMemoryInteger writeSuccessBlockerRepresentedMemory
    (writeSuccessBlockerOwner + 768) 8
    (observationChainId writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerForkName :
  writeSuccessMemoryOptionalBytes writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 776
    (observationForkName writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerActiveForkIndex :
  writeSuccessMemoryInteger writeSuccessBlockerRepresentedMemory
    (writeSuccessBlockerOwner + 792) 8
    (observationActiveForkIndex writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerActivationBlock :
  writeSuccessMemoryOptionalU64 writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 800
    (observationActivationBlock writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Lemma writeSuccessBlockerActivationTimestamp :
  writeSuccessMemoryOptionalU64 writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 816
    (observationActivationTimestamp writeSuccessBlockerDecoded).
Proof. native_compute; reflexivity. Qed.

Print Assumptions writeSuccessBlockerDeposits.
Print Assumptions writeSuccessBlockerParentBeaconRoot.
Print Assumptions writeSuccessBlockerForkName.
Print Assumptions writeSuccessBlockerActivationTimestamp.
