From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAmountRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0FinalEncoderCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Open Scope Z_scope.

Lemma writeSuccessWithdrawals156d0FinalEncoderPositionPath args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    outputRegs global outputPriorLog (firstValue secondValue : bv 64)
    segments after :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  global = writeSuccessEncoderIntGlobal2
    (writeSuccessEncoderIntGlobal2
      (writeSuccessWithdrawals156a8Global regs0 global0 sp pointer current) sp
      (Z_to_bv 64 0x156b4) firstValue) sp
    (Z_to_bv 64 0x156c0) secondValue ->
  outputRegs !! "x2" = Some (RVal_Bits sp) ->
  Inv_write_output (sp + BV 64 1768)%bv (BV 64 20)
    (Z_to_bv 64 0x156d0) (writeSuccessWithdrawalAddressBytes withdrawal)
    outputPriorLog (writeSuccess10190Before outputRegs global, outputPriorLog) ->
  WriteSuccessWithdrawalsRecordedRun 3
    (writeSuccess101a0After (writeSuccessOutputRegs4 outputRegs) global
       (Z_to_bv 64 0x156d0),
     outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
       (sp + BV 64 1768)%bv (BV 64 20)) segments after ->
  after =
    (writeSuccess156d8After
      (writeSuccess156d4Regs
        (writeSuccess156d0Regs
          (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
          (writeSuccessWithdrawalsAmountValue withdrawal))) global,
     outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
       (sp + BV 64 1768)%bv (BV 64 20)) /\
  exists states,
    length states = 4%nat /\
    nth_error states 0 =
      Some
        (writeSuccess101a0After (writeSuccessOutputRegs4 outputRegs) global
           (Z_to_bv 64 0x156d0),
         outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
           (sp + BV 64 1768)%bv (BV 64 20)) /\
    nth_error states 3 = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states.
Proof.
  intros Hinv Hglobal Hx2 HoutputInv Hrecorded.
  have Hafter := writeSuccessWithdrawals156d0FinalEncoderCovered args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state
    regs0 global0 outputRegs global outputPriorLog firstValue secondValue
    segments after Hinv Hglobal Hx2 HoutputInv Hrecorded.
  destruct (writeSuccessWithdrawalsRecordedRunPositionEdges 3
    (writeSuccess101a0After (writeSuccessOutputRegs4 outputRegs) global
       (Z_to_bv 64 0x156d0),
     outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
       (sp + BV 64 1768)%bv (BV 64 20)) segments after Hrecorded) as
    (states & Hlength & Hstart & Hend & Hedges).
  split; first exact Hafter.
  exists states. repeat split; assumption.
Qed.

Print Assumptions writeSuccessWithdrawals156d0FinalEncoderPositionPath.
