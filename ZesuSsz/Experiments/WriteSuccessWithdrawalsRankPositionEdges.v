From Coq Require Import Lia Lists.List.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Theorem writeSuccessWithdrawalsActualSegmentEquationDecreases remaining position
    observations before after :
  (position < 410)%nat ->
  WriteSuccessWithdrawalsRecordedRun 1 before [observations] after ->
  writeSuccessWithdrawalsSegmentEquation remaining position before after ->
  (rank_15694 after < rank_15694 before)%nat.
Proof.
  intros Hposition _ Hequation.
  exact (writeSuccessWithdrawalsRankFromSegmentEquation remaining position
    before after Hposition Hequation).
Qed.

Theorem writeSuccessWithdrawalsPositionEdgesEverySegmentDecreases remaining
    segments states :
  length segments = 410%nat ->
  WriteSuccessWithdrawalsPositionEdges segments states ->
  (forall position observations before after,
    (position < 410)%nat ->
    nth_error segments position = Some observations ->
    nth_error states position = Some before ->
    nth_error states (S position) = Some after ->
    WriteSuccessWithdrawalsRecordedRun 1 before [observations] after ->
    writeSuccessWithdrawalsSegmentEquation remaining position before after) ->
  forall position,
    (position < 410)%nat ->
    exists observations before after,
      nth_error segments position = Some observations /\
      nth_error states position = Some before /\
      nth_error states (S position) = Some after /\
      WriteSuccessWithdrawalsRecordedRun 1 before [observations] after /\
      writeSuccessWithdrawalsSegmentEquation remaining position before after /\
      (rank_15694 after < rank_15694 before)%nat.
Proof.
  intros Hlength Hedges Hequations position Hposition.
  assert (Hwithin : (position < length segments)%nat) by lia.
  destruct (writeSuccessWithdrawalsPositionEdgesNth segments states position
    Hedges Hwithin) as
    (observations & before & after & Hobservations & Hbefore & Hafter & Hrun).
  pose proof (Hequations position observations before after Hposition
    Hobservations Hbefore Hafter Hrun) as Hequation.
  exists observations, before, after.
  split; first exact Hobservations.
  split; first exact Hbefore.
  split; first exact Hafter.
  split; first exact Hrun.
  split; first exact Hequation.
  eapply writeSuccessWithdrawalsActualSegmentEquationDecreases; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawalsActualSegmentEquationDecreases.
Print Assumptions writeSuccessWithdrawalsPositionEdgesEverySegmentDecreases.
