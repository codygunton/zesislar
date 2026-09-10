From Coq Require Import Lists.List.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Lemma writeSuccessWithdrawalsActualSilentSuccessor segments states position
    observations (before after : WriteSuccessWithdrawalsConcreteState) :
  WriteSuccessWithdrawalsPositionEdges segments states ->
  nth_error segments position = Some observations ->
  nth_error states position = Some before ->
  nth_error states (S position) = Some after ->
  concat (map microLabels observations) = [] ->
  snd after = snd before.
Proof.
  intros Hedges Hobservations Hbefore Hafter Hsilent.
  assert (Hposition : (position < length segments)%nat).
  { apply nth_error_Some. intros Hnone.
    rewrite Hnone in Hobservations. discriminate. }
  destruct (writeSuccessWithdrawalsPositionEdgesNth segments states position
    Hedges Hposition) as
    (actualObservations & actualBefore & actualAfter & HactualObservations &
     HactualBefore & HactualAfter & Hone).
  rewrite Hobservations in HactualObservations.
  injection HactualObservations as ->.
  rewrite Hbefore in HactualBefore. injection HactualBefore as ->.
  rewrite Hafter in HactualAfter. injection HactualAfter as ->.
  destruct Hone as (_ & Hlog). cbn [flattenMicroObservations] in Hlog.
  rewrite app_nil_r in Hlog.
  rewrite (writeSuccessWithdrawalsSilentSegmentRecords (fst actualBefore)
    actualObservations Hsilent) in Hlog.
  rewrite app_nil_r in Hlog. exact Hlog.
Qed.

Print Assumptions writeSuccessWithdrawalsActualSilentSuccessor.
