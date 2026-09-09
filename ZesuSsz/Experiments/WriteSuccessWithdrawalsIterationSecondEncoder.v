From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecorded.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderRecorded.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationFirstEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Lemma writeSuccessWithdrawalsIterationThroughSecondEncoder args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  exists segments regs0 global0 regs1 global1 regs2 global2,
    WriteSuccessWithdrawalsRecordedRun 380 state segments
      (writeSuccessWithdrawalsEncoderIntEndpoint regs2 global2 sp
         (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal),
       (priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global1 sp
          (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)) ++
       writeSuccessWithdrawalsEncoderIntRecords global2 sp
         (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal)) /\
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs0 global0 /\
    writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
      withdrawal = writeSuccess15d10Before regs1 global1 /\
    writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal =
      writeSuccess15d10Before regs2 global2.
Proof.
  intros Hinv.
  destruct (writeSuccessWithdrawalsIterationThroughFirstEncoderContext args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state Hinv)
    as (g0 & regs0 & global0 & regs1 & global1 & H0 & Hprefix & Hentry1).
  destruct (writeSuccessWithdrawals156b4SecondEncoderRecorded args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 Hinv Hprefix Hentry1) as (g1 & H1).
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 Hinv Hprefix Hentry1.
  set (log1 := priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global1 sp
    (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)).
  destruct (block_encoder_int_recorded
    (writeSuccessWithdrawalsValidatorValue withdrawal) sp
    (Z_to_bv 64 0x156c0)
    (writeSuccessWithdrawalsFirstEncoderScratch sp withdrawal)
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs1 global1 sp
      withdrawal).2.(seq_mem) log1
    (writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal,
     log1) Hinv2) as
    (g2 & after2 & records2 & H2 & Hpc2 & Hread2 & Hframe2 & Hlog2 &
     Hrecords2).
  destruct (block_encoder_int_recorded_covered_exact
    (writeSuccessWithdrawalsValidatorValue withdrawal) sp
    (Z_to_bv 64 0x156c0)
    (writeSuccessWithdrawalsFirstEncoderScratch sp withdrawal)
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs1 global1 sp
      withdrawal).2.(seq_mem) log1
    (writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal,
     log1) g2 after2 Hinv2 H2) as
    (regs2 & global2 & Hentry2 & Hafter2).
  have H01 : WriteSuccessWithdrawalsRecordedRun 365 state (g0 ++ g1)
      (writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal,
       log1).
  { replace 365%nat with (362 + 3)%nat by reflexivity.
    eapply writeSuccessWithdrawalsRecordedRunApp; eassumption. }
  have H012 : WriteSuccessWithdrawalsRecordedRun 380 state ((g0 ++ g1) ++ g2)
      after2.
  { replace 380%nat with (365 + 15)%nat by reflexivity.
    eapply writeSuccessWithdrawalsRecordedRunApp; eassumption. }
  exists ((g0 ++ g1) ++ g2), regs0, global0, regs1, global1, regs2, global2.
  rewrite Hafter2 in H012. unfold log1 in H012.
  split; first exact H012. split; first exact Hprefix.
  split; assumption.
Qed.

Print Assumptions writeSuccessWithdrawalsIterationThroughSecondEncoder.
