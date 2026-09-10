From Coq Require Import Lia Lists.List.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.

Import ListNotations.

Fixpoint WriteSuccessWithdrawalsMachinePositionEdges
    (segments : list (list IslaMicroObservation)) (states : list IslaState) : Prop :=
  match segments, states with
  | [], [_] => True
  | observations :: segmentTail, before :: after :: stateTail =>
      IslaInstructionSegment before observations after /\
      WriteSuccessWithdrawalsMachinePositionEdges segmentTail (after :: stateTail)
  | _, _ => False
  end.

Lemma writeSuccessWithdrawalsPositionEdgesMachines segments states :
  WriteSuccessWithdrawalsPositionEdges segments states ->
  WriteSuccessWithdrawalsMachinePositionEdges segments (map fst states).
Proof.
  revert states. induction segments as [|observations segments IH];
    intros states Hedges.
  - destruct states as [|state states]; first contradiction.
    destruct states; first exact I. contradiction.
  - destruct states as [|before states]; first contradiction.
    destruct states as [|after states]; first contradiction.
    cbn in Hedges |- *. destruct Hedges as (Hedge & Htail).
    split.
    { destruct Hedge as (Hrun & _).
      inversion Hrun as [|? ? ? ? ? ? Hsegment Hzero]; subst.
      inversion Hzero; subst. exact Hsegment. }
    change (WriteSuccessWithdrawalsMachinePositionEdges segments
      (map fst (after :: states))).
    apply IH. exact Htail.
Qed.

Lemma writeSuccessWithdrawalsMachinePositionEdgesNth segments states position :
  WriteSuccessWithdrawalsMachinePositionEdges segments states ->
  (position < length segments)%nat ->
  exists observations before after,
    nth_error segments position = Some observations /\
    nth_error states position = Some before /\
    nth_error states (S position) = Some after /\
    IslaInstructionSegment before observations after.
Proof.
  revert states position. induction segments as [|observations segments IH];
    intros states position Hedges Hposition; first (cbn in Hposition; lia).
  destruct states as [|before states]; first contradiction.
  destruct states as [|after states]; first contradiction.
  cbn in Hedges. destruct Hedges as (Hhead & Htail).
  destruct position as [|position].
  - exists observations, before, after.
    split; first reflexivity. split; first reflexivity.
    split; first reflexivity. exact Hhead.
  - destruct (IH (after :: states) position Htail ltac:(cbn in Hposition; lia))
      as (nextObservations & nextBefore & nextAfter & Hobs & Hbefore & Hafter & Hedge).
    exists nextObservations, nextBefore, nextAfter. cbn.
    split; first exact Hobs. split; first exact Hbefore.
    split; first exact Hafter. exact Hedge.
Qed.

Lemma writeSuccessWithdrawalsInstructionRunMachinePositionEdges count before
    segments after :
  IslaInstructionRun count before segments after ->
  exists states,
    length states = S count /\
    nth_error states 0 = Some before /\
    nth_error states count = Some after /\
    WriteSuccessWithdrawalsMachinePositionEdges segments states.
Proof.
  intros Hrun. induction Hrun as
    [state|count before observations middle segments after Hsegment Hrun IH].
  - exists [state]. repeat split; reflexivity.
  - destruct IH as (states & Hlength & Hstart & Hend & Hedges).
    exists (before :: states).
    split; first (cbn; lia).
    split; first reflexivity.
    split.
    + cbn. exact Hend.
    + destruct states as [|head tail]; first discriminate.
      cbn in Hstart. inversion Hstart; subst head.
      cbn. split; assumption.
Qed.

Print Assumptions writeSuccessWithdrawalsPositionEdgesMachines.
Print Assumptions writeSuccessWithdrawalsMachinePositionEdgesNth.
Print Assumptions writeSuccessWithdrawalsInstructionRunMachinePositionEdges.
