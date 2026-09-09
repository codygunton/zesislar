From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.

Ltac solve_blocker_empty_list :=
  exists 0%Z; split;
  [change (0 <= 0 < 18446744073709551616)%Z; lia|];
  split; [native_compute; reflexivity|];
  split; [native_compute; reflexivity|];
  intros index item Hitem; destruct index; discriminate.

Lemma writeSuccessBlockerTransactions :
  writeSuccessTransactionListMemory writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 56
    (observationTransactions writeSuccessBlockerDecoded).
Proof. solve_blocker_empty_list. Qed.

Lemma writeSuccessBlockerRawTransactions :
  writeSuccessMemoryByteLists writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 72
    (observationRawTransactions writeSuccessBlockerDecoded).
Proof. solve_blocker_empty_list. Qed.

Lemma writeSuccessBlockerWithdrawals :
  writeSuccessWithdrawalListMemory writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 88
    (observationWithdrawals writeSuccessBlockerDecoded).
Proof.
  exists 0x20001000%Z. split.
  - change (0 <= 536875008 < 18446744073709551616)%Z. lia.
  - split; [native_compute; reflexivity|].
    split; [native_compute; reflexivity|].
    intros index item Hitem. destruct index as [|index].
    + cbn in Hitem. inversion Hitem. subst item.
      unfold writeSuccessWithdrawalMemory. repeat split;
        native_compute; reflexivity.
    + destruct index as [|index].
      * cbn in Hitem. inversion Hitem. subst item.
        unfold writeSuccessWithdrawalMemory. repeat split;
          native_compute; reflexivity.
      * destruct index; discriminate.
Qed.

Lemma writeSuccessBlockerVersionedHashes :
  writeSuccessMemoryFixedList writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 592 32
    (observationVersionedHashes writeSuccessBlockerDecoded).
Proof. solve_blocker_empty_list. Qed.

Lemma writeSuccessBlockerWitnessNodes :
  writeSuccessMemoryByteLists writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 720
    (observationWitnessNodes writeSuccessBlockerDecoded).
Proof. solve_blocker_empty_list. Qed.

Lemma writeSuccessBlockerWitnessCodes :
  writeSuccessMemoryByteLists writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 736
    (observationWitnessCodes writeSuccessBlockerDecoded).
Proof. solve_blocker_empty_list. Qed.

Lemma writeSuccessBlockerWitnessHeaders :
  writeSuccessMemoryByteLists writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 752
    (observationWitnessHeaders writeSuccessBlockerDecoded).
Proof. solve_blocker_empty_list. Qed.

Lemma writeSuccessBlockerPublicKeys :
  writeSuccessMemoryByteLists writeSuccessBlockerRepresentedMemory
    writeSuccessBlockerOwner 832
    (observationPublicKeys writeSuccessBlockerDecoded).
Proof. solve_blocker_empty_list. Qed.

Print Assumptions writeSuccessBlockerTransactions.
Print Assumptions writeSuccessBlockerWithdrawals.
Print Assumptions writeSuccessBlockerPublicKeys.
