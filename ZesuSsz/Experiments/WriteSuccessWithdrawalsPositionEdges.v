From Coq Require Import Lia Lists.List.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Import ListNotations.

Fixpoint WriteSuccessWithdrawalsPositionEdges
    (segments : list (list IslaMicroObservation))
    (states : list WriteSuccessWithdrawalsConcreteState) : Prop :=
  match segments, states with
  | [], [_] => True
  | observations :: segmentTail, before :: after :: stateTail =>
      WriteSuccessWithdrawalsRecordedRun 1 before [observations] after /\
      WriteSuccessWithdrawalsPositionEdges segmentTail (after :: stateTail)
  | _, _ => False
  end.

Lemma writeSuccessWithdrawalsPositionEdgesLength segments states :
  WriteSuccessWithdrawalsPositionEdges segments states ->
  length states = S (length segments).
Proof.
  revert states. induction segments as [|observations segments IH];
    intros states Hedges.
  - destruct states as [|state states]; first contradiction.
    destruct states; first reflexivity. contradiction.
  - destruct states as [|before states]; first contradiction.
    destruct states as [|after states]; first contradiction.
    cbn in Hedges |- *. destruct Hedges as (_ & Htail).
    specialize (IH (after :: states) Htail). cbn in IH. lia.
Qed.

Lemma writeSuccessWithdrawalsPositionEdgesNth segments states position :
  WriteSuccessWithdrawalsPositionEdges segments states ->
  (position < length segments)%nat ->
  exists observations before after,
    nth_error segments position = Some observations /\
    nth_error states position = Some before /\
    nth_error states (S position) = Some after /\
    WriteSuccessWithdrawalsRecordedRun 1 before [observations] after.
Proof.
  revert states position. induction segments as [|observations segments IH];
    intros states position Hedges Hposition; first (cbn in Hposition; lia).
  destruct states as [|before states]; first contradiction.
  destruct states as [|after states]; first contradiction.
  cbn in Hedges. destruct Hedges as (Hhead & Htail).
  destruct position as [|position].
  - exists observations, before, after.
    split; first reflexivity.
    split; first reflexivity.
    split; first reflexivity.
    exact Hhead.
  - destruct (IH (after :: states) position Htail ltac:(cbn in Hposition; lia))
      as (nextObservations & nextBefore & nextAfter & Hobservations & Hbefore &
          Hafter & Hone).
    exists nextObservations, nextBefore, nextAfter. cbn.
    split; first exact Hobservations.
    split; first exact Hbefore.
    split; first exact Hafter.
    exact Hone.
Qed.

Print Assumptions writeSuccessWithdrawalsPositionEdgesLength.
Print Assumptions writeSuccessWithdrawalsPositionEdgesNth.

Lemma writeSuccessWithdrawalsPositionEdgesApp firstSegments firstStates middle
    secondSegments secondStates :
  WriteSuccessWithdrawalsPositionEdges firstSegments
    (firstStates ++ [middle]) ->
  WriteSuccessWithdrawalsPositionEdges secondSegments
    (middle :: secondStates) ->
  WriteSuccessWithdrawalsPositionEdges (firstSegments ++ secondSegments)
    (firstStates ++ middle :: secondStates).
Proof.
  revert firstStates middle secondSegments secondStates.
  induction firstSegments as [|observations firstSegments IH];
    intros firstStates middle secondSegments secondStates Hfirst Hsecond.
  - destruct firstStates; cbn in Hfirst |- *; first exact Hsecond.
    destruct firstStates; contradiction.
  - destruct firstStates as [|before firstStates]; first contradiction.
    destruct firstStates as [|after firstStates].
    + cbn in Hfirst. destruct Hfirst as (Hedge & Hempty).
      cbn. split; first exact Hedge.
      eapply (IH [] middle secondSegments secondStates); eassumption.
    + cbn in Hfirst |- *. destruct Hfirst as (Hedge & Htail).
      split; first exact Hedge.
      change (WriteSuccessWithdrawalsPositionEdges
        (firstSegments ++ secondSegments)
        ((after :: firstStates) ++ middle :: secondStates)).
      eapply IH; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawalsPositionEdgesApp.
