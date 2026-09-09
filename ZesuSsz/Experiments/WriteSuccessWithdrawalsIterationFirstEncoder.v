From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecorded.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderInt.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationPrefixJoin.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Lemma writeSuccessWithdrawalsIterationThroughFirstEncoder args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  exists segments regs global,
    WriteSuccessWithdrawalsRecordedRun 362 state segments
      (writeSuccessWithdrawalsEncoderIntEndpoint regs global sp
         (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal),
       priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
         (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)).
Proof.
  intros Hinv.
  destruct (writeSuccessWithdrawalsPrefixMemcpyRecordedJoin args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (g0 & regs0 & global0 & H0 & Hentry).
  destruct (writeSuccessWithdrawals156a8EncoderIntRecorded args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 Hinv
    Hentry) as (g1 & H1).
  have HencoderInv := writeSuccessWithdrawals156a8EncoderIntInv args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 Hinv Hentry.
  destruct (block_encoder_int_recorded
    (writeSuccessWithdrawalsIndexValue withdrawal) sp (Z_to_bv 64 0x156b4)
    encoderScratch
    (writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer
      current withdrawal).2.(seq_mem)
    priorLog
    (writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer
      current withdrawal, priorLog) HencoderInv) as
    (g2 & after2 & records2 & H2 & Hpc2 & Hread2 & Hframe2 & Hlog2 &
     Hrecords2).
  destruct (block_encoder_int_recorded_covered_exact
    (writeSuccessWithdrawalsIndexValue withdrawal) sp (Z_to_bv 64 0x156b4)
    encoderScratch
    (writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer
      current withdrawal).2.(seq_mem)
    priorLog
    (writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer
      current withdrawal, priorLog) g2 after2 HencoderInv H2) as
    (regs & global & HencoderEntry & Hafter2).
  have H01 : WriteSuccessWithdrawalsRecordedRun 347 state (g0 ++ g1)
      (writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer
        current withdrawal, priorLog).
  { replace 347%nat with (344 + 3)%nat by reflexivity.
    eapply writeSuccessWithdrawalsRecordedRunApp; eassumption. }
  have H012 : WriteSuccessWithdrawalsRecordedRun 362 state ((g0 ++ g1) ++ g2)
      after2.
  { replace 362%nat with (347 + 15)%nat by reflexivity.
    eapply writeSuccessWithdrawalsRecordedRunApp; eassumption. }
  exists ((g0 ++ g1) ++ g2), regs, global.
  rewrite Hafter2 in H012. exact H012.
Qed.

Print Assumptions writeSuccessWithdrawalsIterationThroughFirstEncoder.
