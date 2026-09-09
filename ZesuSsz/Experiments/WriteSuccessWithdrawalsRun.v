From Coq Require Import Lia Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessBlockFramework.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Import ListNotations.

Definition WriteSuccessWithdrawalsRecordedRun
    (count : nat) (before : WriteSuccessWithdrawalsConcreteState)
    (segments : list (list IslaMicroObservation))
    (after : WriteSuccessWithdrawalsConcreteState) : Prop :=
  IslaInstructionRun count before.1 segments after.1 /\
  after.2 = before.2 ++
    segmentRecords before.1 (flattenMicroObservations segments).

Lemma flattenMicroObservationsApp first second :
  flattenMicroObservations (first ++ second) =
    flattenMicroObservations first ++ flattenMicroObservations second.
Proof.
  induction first as [|segment first IH]; simpl; first reflexivity.
  rewrite IH app_assoc. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsRecordedRunZero state :
  WriteSuccessWithdrawalsRecordedRun 0 state [] state.
Proof.
  split; first constructor.
  cbn. rewrite app_nil_r. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsRecordedRunOne before observations machineAfter :
  IslaInstructionSegment before.1 observations machineAfter ->
  WriteSuccessWithdrawalsRecordedRun 1 before [observations]
    (machineAfter, before.2 ++ segmentRecords before.1 observations).
Proof.
  intros Hsegment. split.
  - econstructor; first exact Hsegment. constructor.
  - cbn. rewrite app_nil_r. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsRecordedRunApp firstCount secondCount before
    first middle second after :
  WriteSuccessWithdrawalsRecordedRun firstCount before first middle ->
  WriteSuccessWithdrawalsRecordedRun secondCount middle second after ->
  WriteSuccessWithdrawalsRecordedRun (firstCount + secondCount) before
    (first ++ second) after.
Proof.
  intros [Hfirst HmiddleLog] [Hsecond HafterLog]. split.
  - eapply islaInstructionRun_app; eassumption.
  - rewrite flattenMicroObservationsApp.
    rewrite (segmentRecords_app before.1
      (flattenMicroObservations first) middle.1
      (flattenMicroObservations second)).
    + rewrite HafterLog HmiddleLog. symmetry. apply app_assoc.
    + exact (islaInstructionRunCorrespondence _ _ _ _ Hfirst).
Qed.

Lemma writeSuccessWithdrawalsRecordedRunSnoc count before segments middle
    observations machineAfter :
  WriteSuccessWithdrawalsRecordedRun count before segments middle ->
  IslaInstructionSegment middle.1 observations machineAfter ->
  WriteSuccessWithdrawalsRecordedRun (S count) before
    (segments ++ [observations])
    (machineAfter, middle.2 ++ segmentRecords middle.1 observations).
Proof.
  intros Hrun Hsegment.
  replace (S count) with (count + 1)%nat by lia.
  eapply writeSuccessWithdrawalsRecordedRunApp; first exact Hrun.
  apply writeSuccessWithdrawalsRecordedRunOne. exact Hsegment.
Qed.

Lemma writeSuccessWithdrawalsRecordedRunCount count before segments after :
  WriteSuccessWithdrawalsRecordedRun count before segments after ->
  length segments = count.
Proof. intros [Hrun _]. exact (islaInstructionRunCount _ _ _ _ Hrun). Qed.

Print Assumptions writeSuccessWithdrawalsRecordedRunZero.
Print Assumptions writeSuccessWithdrawalsRecordedRunOne.
Print Assumptions writeSuccessWithdrawalsRecordedRunApp.
Print Assumptions writeSuccessWithdrawalsRecordedRunSnoc.
Print Assumptions writeSuccessWithdrawalsRecordedRunCount.
