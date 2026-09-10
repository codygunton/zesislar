From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedRunSplit.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntActualPositionsFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationMemcpyCoverageJoin.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationBounds.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8PositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.

Import ListNotations.
Open Scope Z_scope.

Theorem writeSuccessWithdrawalsFirstEncoderActualPositionsFrom15694 args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state segments after :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 410 state segments after ->
  exists regs global encoderSegments encoderAfter prefixStates outputStates suffixStates,
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs global /\
    Inv_encoder_int (writeSuccessWithdrawalsIndexValue withdrawal) sp
      (Z_to_bv 64 0x156b4) encoderScratch
      (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current
        withdrawal).2.(seq_mem) priorLog
      (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current
        withdrawal, priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 15
      (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer
        current withdrawal, priorLog) encoderSegments encoderAfter /\
    exists prefixGroup outputGroup suffixGroup,
      encoderSegments = (prefixGroup ++ outputGroup) ++ suffixGroup /\
      length prefixStates = 8%nat /\
      length outputStates = 6%nat /\
      length suffixStates = 4%nat /\
      nth_error prefixStates 0 = Some
        (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer
          current withdrawal, priorLog) /\
      nth_error prefixStates 7 = nth_error outputStates 0 /\
      nth_error outputStates 5 = nth_error suffixStates 0 /\
      nth_error suffixStates 3 = Some encoderAfter /\
      WriteSuccessWithdrawalsPositionEdges prefixGroup prefixStates /\
      WriteSuccessWithdrawalsPositionEdges outputGroup outputStates /\
      WriteSuccessWithdrawalsPositionEdges suffixGroup suffixStates /\
      (forall offset stateAt, (offset < 7)%nat ->
        nth_error prefixStates offset = Some stateAt ->
        writeSuccessWithdrawalsPositionState remaining (347 + offset) stateAt) /\
      (forall offset stateAt, (offset < 5)%nat ->
        nth_error outputStates offset = Some stateAt ->
        writeSuccessWithdrawalsPositionState remaining
          (347 + (7 + offset))%nat stateAt) /\
      (forall offset stateAt, (offset < 3)%nat ->
        nth_error suffixStates offset = Some stateAt ->
        writeSuccessWithdrawalsPositionState remaining
          (347 + (12 + offset))%nat stateAt).
Proof.
  intros Hinv Hrun.
  have Hrun5 : WriteSuccessWithdrawalsRecordedRun (5 + 405) state segments after
    by exact Hrun.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 5 405 state segments after
    Hrun5) as (g0 & state5 & tail405 & Hsegments0 & H0 & H405).
  rewrite (writeSuccessWithdrawalsPrefix15694RecordedCovered args sp pointer
    base total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state g0 state5
    Hinv H0) in H405.
  have Hrun339 : WriteSuccessWithdrawalsRecordedRun (339 + 66)
      (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog)
      tail405 after by exact H405.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 339 66 _ tail405 after
    Hrun339) as (g1 & state344 & tail66 & Hsegments1 & H1 & H66).
  destruct (writeSuccessWithdrawalsIterationMemcpyRecordedCoveredJoin args sp
    pointer base total processed (S remaining) withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state g1
    state344 Hinv H1) as (regs0 & global0 & Hprefix & Hstate344).
  rewrite Hstate344 in H66.
  have Hrun3 : WriteSuccessWithdrawalsRecordedRun (3 + 63)
      (writeSuccessWithdrawals156a8State regs0 global0 sp pointer current,
       priorLog) tail66 after by exact H66.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 3 63 _ tail66 after Hrun3)
    as (g2 & state347 & tail63 & Hsegments2 & H2 & H63).
  rewrite (writeSuccessWithdrawals156a8EncoderIntCovered args sp pointer base
    total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    g2 state347 Hinv Hprefix H2) in H63.
  have Hrun15 : WriteSuccessWithdrawalsRecordedRun (15 + 48)
      (writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer
        current withdrawal, priorLog) tail63 after by exact H63.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 15 48 _ tail63 after Hrun15)
    as (encoderSegments & encoderAfter & tail48 & Hsegments3 & Hencoder & H48).
  have HencoderInv := writeSuccessWithdrawals156a8EncoderIntInv args sp pointer
    base total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    Hinv Hprefix.
  destruct (writeSuccessWithdrawals156a8HandoffPositionStates args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    Hinv Hprefix) as (_ & _ & Hposition346).
  unfold writeSuccessWithdrawalsPositionState in Hposition346.
  destruct Hposition346 as (_ & _ & _ & _ & Hx9b0 & _).
  have Hx9 :
      (writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer
        current withdrawal).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccessWithdrawalsEncoderInt156b4State,
      writeSuccess156b0After, writeSuccess15694Local. cbn.
    rewrite writeSuccess156b0RegsLookupOther; try discriminate. exact Hx9b0. }
  have Hrange : (Z.of_nat (S remaining) < 2 ^ 64)%Z.
  { have Hremaining := writeSuccessWithdrawalsIterationRemainingRange args sp
      pointer base total processed (S remaining) withdrawal allBytes prefix
      current suffix scratch encoderScratch registerFrame memoryFrame priorLog
      state Hinv. lia. }
  destruct (writeSuccessWithdrawalsEncoderIntActualPositionsFromInv remaining
    347 (writeSuccessWithdrawalsIndexValue withdrawal) sp
    (Z_to_bv 64 0x156b4) encoderScratch
    (writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
      withdrawal).2.(seq_mem) priorLog
    (writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
      withdrawal, priorLog) encoderSegments encoderAfter
    ltac:(unfold writeSuccessWithdrawalsEncoderIntPositionStart; tauto)
    HencoderInv Hx9 Hrange Hencoder) as
    (prefixGroup & outputGroup & suffixGroup & prefixStates & outputStates &
     suffixStates & Hgroups).
  exists regs0, global0, encoderSegments, encoderAfter, prefixStates,
    outputStates, suffixStates.
  split; first exact Hprefix.
  split; first exact HencoderInv.
  split; first exact Hencoder.
  exists prefixGroup, outputGroup, suffixGroup. exact Hgroups.
Qed.

Print Assumptions writeSuccessWithdrawalsFirstEncoderActualPositionsFrom15694.
