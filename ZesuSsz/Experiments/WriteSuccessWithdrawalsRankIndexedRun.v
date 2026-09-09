From Coq Require Import Lists.List.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.

Import ListNotations.

(** The operational coverage proof supplies this relation.  It binds every
    table position to one completed segment and contains no rank result. *)
Definition WriteSuccessWithdrawalsIndexedRun
    (remaining : nat) (before : WriteSuccessWithdrawalsConcreteState)
    (segments : list (list IslaMicroObservation))
    (states : list WriteSuccessWithdrawalsConcreteState) : Prop :=
  length states = 411%nat /\
  nth_error states 0 = Some before /\
  (forall position,
    (position < 410)%nat ->
    exists observations beforeAt afterAt,
      nth_error segments position = Some observations /\
      nth_error states position = Some beforeAt /\
      nth_error states (S position) = Some afterAt /\
      WriteSuccessWithdrawalsRecordedRun 1 beforeAt [observations] afterAt) /\
  writeSuccessWithdrawalsRankedEndpoints remaining states.

Theorem writeSuccessWithdrawalsIndexedRunEverySegmentDecreases
    remaining before segments states :
  WriteSuccessWithdrawalsIndexedRun remaining before segments states ->
  forall position,
    (position < 410)%nat ->
    exists observations beforeAt afterAt,
      nth_error segments position = Some observations /\
      nth_error states position = Some beforeAt /\
      nth_error states (S position) = Some afterAt /\
      WriteSuccessWithdrawalsRecordedRun 1 beforeAt [observations] afterAt /\
      rank_15694 afterAt < rank_15694 beforeAt.
Proof.
  intros (_ & _ & Hsegments & Hranked) position Hposition.
  destruct (Hsegments position Hposition) as
    (observations & beforeAt & afterAt & Hobservations & Hbefore & Hafter &
     Hrun).
  exists observations, beforeAt, afterAt.
  split; first exact Hobservations.
  split; first exact Hbefore.
  split; first exact Hafter.
  split; first exact Hrun.
  eapply writeSuccessWithdrawalsWholeTableRankDecreases; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawalsIndexedRunEverySegmentDecreases.
