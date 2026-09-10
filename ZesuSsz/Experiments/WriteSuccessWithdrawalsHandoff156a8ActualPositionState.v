From Coq Require Import Lia Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8PositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Theorem writeSuccessWithdrawals156a8ActualPositionStates args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs global segments
    after :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs global ->
  WriteSuccessWithdrawalsRecordedRun 3
    (writeSuccessWithdrawals156a8State regs global sp pointer current, priorLog)
    segments after ->
  exists states,
    after =
      (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer
        current withdrawal, priorLog) /\
    length states = 4%nat /\
    nth_error states 0 = Some
      (writeSuccessWithdrawals156a8State regs global sp pointer current,
       priorLog) /\
    nth_error states 3 = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states /\
    forall offset stateAt,
      (offset < 3)%nat ->
      nth_error states offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining (344 + offset) stateAt.
Proof.
  intros Hinv Hentry Hrecorded.
  destruct (writeSuccessWithdrawals156a8EncoderIntPositionsExact args sp pointer
    base total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs global
    segments after Hinv Hentry Hrecorded) as
    (o0 & o1 & o2 & Hsegments & Hafter & Hr0 & Hr1 & Hr2).
  destruct (writeSuccessWithdrawals156a8HandoffPositionStates args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs global
    Hinv Hentry) as (Hp0 & Hp1 & Hp2).
  exists [
    (writeSuccessWithdrawals156a8State regs global sp pointer current, priorLog);
    (writeSuccessWithdrawals156acState regs global sp pointer current withdrawal,
     priorLog);
    (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal,
     priorLog);
    after].
  split; first exact Hafter.
  split; first reflexivity.
  split; first reflexivity.
  split; first reflexivity.
  split.
  { rewrite Hsegments. cbn.
    split; first exact Hr0.
    split; first exact Hr1.
    split; first exact Hr2.
    exact I. }
  intros offset stateAt Hoffset Hnth.
  destruct offset as [|[|[|offset]]]; try lia; cbn in Hnth;
    injection Hnth as <-; assumption.
Qed.

Print Assumptions writeSuccessWithdrawals156a8ActualPositionStates.
