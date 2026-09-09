From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessInstructionRunSplit.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Lemma writeSuccessWithdrawalsRecordedRunSplit firstCount secondCount before
    segments after :
  WriteSuccessWithdrawalsRecordedRun (firstCount + secondCount) before
    segments after ->
  exists first middle second,
    segments = first ++ second /\
    WriteSuccessWithdrawalsRecordedRun firstCount before first middle /\
    WriteSuccessWithdrawalsRecordedRun secondCount middle second after.
Proof.
  intros (Hrun & HafterLog).
  destruct (islaInstructionRun_split firstCount secondCount before.1 segments
    after.1 Hrun) as (first & middleMachine & second & Hsegments & Hfirst & Hsecond).
  set (middleLog := before.2 ++
    segmentRecords before.1 (flattenMicroObservations first)).
  set (middle := (middleMachine, middleLog)).
  exists first, middle, second. split; first exact Hsegments. split.
  - split; first exact Hfirst. unfold middle, middleLog. reflexivity.
  - split; first exact Hsecond.
    unfold middle, middleLog. cbn.
    rewrite HafterLog Hsegments flattenMicroObservationsApp.
    rewrite (segmentRecords_app before.1 (flattenMicroObservations first)
      middleMachine (flattenMicroObservations second)).
    + apply app_assoc.
    + exact (islaInstructionRunCorrespondence _ _ _ _ Hfirst).
Qed.

Print Assumptions writeSuccessWithdrawalsRecordedRunSplit.
