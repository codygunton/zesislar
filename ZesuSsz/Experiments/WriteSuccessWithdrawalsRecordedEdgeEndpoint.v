From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Lemma writeSuccessWithdrawalsLastAppSingleton {A : Type} (items : list A)
    (item fallback : A) :
  List.last (items ++ [item]) fallback = item.
Proof.
  induction items as [|head items IH]; first reflexivity.
  destruct items; cbn in *; assumption.
Qed.

Lemma writeSuccessWithdrawalsRecordedEdgeLast before observations after fallback :
  WriteSuccessWithdrawalsRecordedRun 1 before [observations] after ->
  exists labels,
    List.last observations fallback =
      {| microLabels := labels; microAfter := after.1 |}.
Proof.
  intros (Hrun & _).
  inversion Hrun as [|? ? ? ? ? ? Hsegment Hzero]; subst.
  inversion Hzero; subst.
  destruct Hsegment as
    [Hstart doneSource prefix labels spawned Hprefix HatDone Hdone
      Hobservations Hend].
  exists labels. rewrite Hobservations.
  apply writeSuccessWithdrawalsLastAppSingleton.
Qed.

Print Assumptions writeSuccessWithdrawalsLastAppSingleton.
Print Assumptions writeSuccessWithdrawalsRecordedEdgeLast.
