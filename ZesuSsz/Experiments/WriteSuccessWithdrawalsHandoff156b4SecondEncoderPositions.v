From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Lemma writeSuccessWithdrawals156b4SecondEncoderPositionPath args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs
    global segments after :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs global ->
  WriteSuccessWithdrawalsRecordedRun 3
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal,
     priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
       (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal))
    segments after ->
  after =
    (writeSuccessWithdrawalsSecondEncoderEntry regs global sp withdrawal,
     priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
       (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)) /\
  exists states,
    length states = 4%nat /\
    nth_error states 0 =
      Some
        (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal,
         priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
           (Z_to_bv 64 0x156b4)
           (writeSuccessWithdrawalsIndexValue withdrawal)) /\
    nth_error states 3 = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states.
Proof.
  intros Hinv Hprefix Hentry Hrecorded.
  have Hafter := writeSuccessWithdrawals156b4SecondEncoderCovered args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs global segments after Hinv Hprefix Hentry Hrecorded.
  destruct (writeSuccessWithdrawalsRecordedRunPositionEdges 3
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal,
     priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
       (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal))
    segments after Hrecorded) as
    (states & Hlength & Hstart & Hend & Hedges).
  split; first exact Hafter.
  exists states. repeat split; assumption.
Qed.

Print Assumptions writeSuccessWithdrawals156b4SecondEncoderPositionPath.
