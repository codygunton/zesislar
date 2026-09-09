From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.

Lemma writeSuccessBlockerWithdrawalItems :
  writeSuccessWithdrawalItemsAt writeSuccessBlockerRepresentedMemory
    0x20001000
    (observationWithdrawals writeSuccessBlockerDecoded).
Proof.
  unfold writeSuccessWithdrawalItemsAt.
  intros index item Hitem. destruct index as [|index].
  - cbn in Hitem. inversion Hitem. subst item.
    unfold writeSuccessWithdrawalMemory. repeat split;
      native_compute; reflexivity.
  - destruct index as [|index].
    + cbn in Hitem. inversion Hitem. subst item.
      unfold writeSuccessWithdrawalMemory. repeat split;
        native_compute; reflexivity.
    + destruct index; discriminate.
Qed.

Print Assumptions writeSuccessBlockerWithdrawalItems.
