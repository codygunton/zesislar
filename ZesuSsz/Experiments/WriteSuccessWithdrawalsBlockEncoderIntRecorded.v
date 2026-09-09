From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderInt.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntCoverage.

Definition block_encoder_int_recorded_statement : Prop :=
  forall value sp returnAddress scratch memoryFrame priorLog state,
    Inv_encoder_int value sp returnAddress scratch memoryFrame priorLog state ->
    exists segments after records,
      WriteSuccessWithdrawalsRecordedRun 15 state segments after /\
      writeSuccessWithdrawalsConcretePc after = Some (bv_unsigned returnAddress) /\
      read_mem_list after.1.2.(seq_mem) (bv_unsigned sp - 16) 8%N =
        Some (bv_to_little_endian 8 8 (bv_unsigned value)) /\
      writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
        after.1.2.(seq_mem) memoryFrame /\
      after.2 = priorLog ++ records /\
      writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8)
        (bv_to_little_endian 8 8 (bv_unsigned value)) records.

Lemma block_encoder_int_recorded : block_encoder_int_recorded_statement.
Proof.
  unfold block_encoder_int_recorded_statement.
  intros value sp returnAddress scratch memoryFrame priorLog state Hinv.
  destruct (block_encoder_int value sp returnAddress scratch memoryFrame
    priorLog state Hinv) as
    (segments & oldAfter & oldRecords & Hrun & Hpc & Hread & Hframe &
     HoldLog & HoldRecords).
  set (records := segmentRecords state.1 (flattenMicroObservations segments)).
  set (after := (oldAfter.1, priorLog ++ records)).
  have HbeforeLog : state.2 = priorLog.
  { unfold Inv_encoder_int in Hinv. tauto. }
  have Hrecorded : WriteSuccessWithdrawalsRecordedRun 15 state segments after.
  { split; first exact Hrun. unfold after, records. cbn. rewrite HbeforeLog.
    reflexivity. }
  destruct (block_encoder_int_covered value sp returnAddress scratch memoryFrame
    priorLog state segments after Hinv Hrecorded) as
    (coveredRecords & HcoveredPc & HcoveredRead & HcoveredFrame & HcoveredLog &
     HcoveredRecords).
  exists segments, after, coveredRecords. split; first exact Hrecorded.
  split; first exact HcoveredPc. split; first exact HcoveredRead.
  split; first exact HcoveredFrame. split; assumption.
Qed.

Lemma block_encoder_int_recorded_corollary : block_encoder_int_statement.
Proof.
  unfold block_encoder_int_statement.
  intros value sp returnAddress scratch memoryFrame priorLog state Hinv.
  destruct (block_encoder_int_recorded value sp returnAddress scratch memoryFrame
    priorLog state Hinv) as
    (segments & after & records & Hrecorded & Hpc & Hread & Hframe & Hlog &
     Hrecords).
  exists segments, after, records. destruct Hrecorded as (Hrun & _).
  split; first exact Hrun. split; first exact Hpc. split; first exact Hread.
  split; first exact Hframe. split; assumption.
Qed.

Print Assumptions block_encoder_int_recorded.
Print Assumptions block_encoder_int_recorded_corollary.
