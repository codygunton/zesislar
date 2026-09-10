From Coq Require Import Lia Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0PositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionStateLog.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Theorem writeSuccessWithdrawals156c0ActualPositionStates args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 segments after :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal =
    writeSuccess15d10Before regs2 global2 ->
  WriteSuccessWithdrawalsRecordedRun 4
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal,
     writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
       withdrawal) segments after ->
  after =
    (writeSuccessWithdrawalsOutputEntry
       (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
         withdrawal).1.(seq_regs)
       (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
         withdrawal).2 (sp + BV 64 1768)%bv,
     writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
       withdrawal) /\
  exists states,
    length states = 5%nat /\
    nth_error states 0 = Some
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal,
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
         withdrawal) /\
    nth_error states 4 = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states /\
    forall offset stateAt,
      (offset < 4)%nat ->
      nth_error states offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining (380 + offset) stateAt.
Proof.
  intros Hinv Hprefix Hentry1 Hentry2 Hrun.
  destruct (writeSuccessWithdrawals156c0OutputPositionsExact args sp pointer
    base total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    regs1 global1 regs2 global2 segments after Hinv Hprefix Hentry1 Hentry2
    Hrun) as (o0 & o1 & o2 & o3 & Hsegments & Hafter & Hr0 & Hr1 & Hr2 & Hr3).
  split; first exact Hafter.
  have Hsemantic := writeSuccessWithdrawals156c0HandoffPositionStates args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2.
  set (first := writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
    withdrawal).
  set (second := writeSuccess156c0After first.1.(seq_regs) first.2).
  set (third := writeSuccess156c4After second.1.(seq_regs) second.2
    (sp + BV 64 1768)%bv).
  set (fourth := writeSuccess156c8After third.1.(seq_regs) third.2).
  set (log := writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2
    sp withdrawal).
  have Hr3' : WriteSuccessWithdrawalsRecordedRun 1 (fourth, log) [o3] after.
  { unfold fourth, third, second, first, log, writeSuccess156c8After,
      WriteSuccessSegment156cc.writeSuccess156ccBefore in Hr3 |- *.
    exact Hr3. }
  exists [(first, log); (second, log); (third, log); (fourth, log); after].
  split; first reflexivity.
  split; first reflexivity.
  split; first reflexivity.
  split.
  { unfold fourth, third, second, first, log.
    rewrite Hsegments Hafter. cbn.
    split; first exact Hr0.
    split; first exact Hr1.
    split; first exact Hr2.
    split; first (rewrite <- Hafter; exact Hr3').
    exact I. }
  intros offset stateAt Hoffset Hnth.
  destruct offset as [|[|[|[|offset]]]]; try lia; cbn in Hnth;
    injection Hnth as <-;
    eapply writeSuccessWithdrawalsPositionStateLog;
    eapply Hsemantic; try lia; reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawals156c0ActualPositionStates.
