From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
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

Lemma writeSuccessWithdrawalsActualRecordedSuccessor segments states position
    observations state fallback :
  WriteSuccessWithdrawalsPositionEdges segments states ->
  nth_error segments position = Some observations ->
  nth_error states (S position) = Some state ->
  exists labels,
    List.last observations fallback =
      {| microLabels := labels; microAfter := state.1 |}.
Proof.
  intros Hedges Hobservations Hstate.
  have Hposition : (position < length segments)%nat.
  { apply nth_error_Some. intros Hnone.
    rewrite Hnone in Hobservations. discriminate. }
  destruct (writeSuccessWithdrawalsPositionEdgesNth segments states position
    Hedges Hposition) as
    (actualObservations & before & after & Hactual & _ & Hafter & Hone).
  rewrite Hobservations in Hactual. injection Hactual as ->.
  rewrite Hstate in Hafter. injection Hafter as ->.
  exact (writeSuccessWithdrawalsRecordedEdgeLast before actualObservations after
    fallback Hone).
Qed.

Print Assumptions writeSuccessWithdrawalsActualRecordedSuccessor.
