From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156bc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedRunSplit.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntActualPositionsFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationFirstEncoderCoverageContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationBounds.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4PositionState.

Import ListNotations.
Open Scope Z_scope.

Theorem writeSuccessWithdrawalsSecondEncoderActualPositionsFrom15694 args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state
    segments after :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 410 state segments after ->
  exists regs0 global0 regs global encoderRegs encoderGlobal encoderSegments
      encoderAfter prefixStates outputStates suffixStates,
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs0 global0 /\
    writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
      withdrawal = writeSuccess15d10Before regs global /\
    (writeSuccessWithdrawalsSecondEncoderEntry regs global sp withdrawal,
      priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
        (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)).1 =
      writeSuccess15d10Before encoderRegs encoderGlobal /\
    encoderAfter =
      (writeSuccessWithdrawalsEncoderIntEndpoint encoderRegs encoderGlobal sp
         (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal),
       (priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
          (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)) ++
       writeSuccessWithdrawalsEncoderIntRecords encoderGlobal sp
         (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal)) /\
    Inv_encoder_int (writeSuccessWithdrawalsValidatorValue withdrawal) sp
      (Z_to_bv 64 0x156c0)
      (writeSuccessWithdrawalsFirstEncoderScratch sp withdrawal)
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).2.(seq_mem)
      (priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
        (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal))
      (writeSuccessWithdrawalsSecondEncoderEntry regs global sp withdrawal,
       priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
         (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)) /\
    WriteSuccessWithdrawalsRecordedRun 15
      (writeSuccessWithdrawalsSecondEncoderEntry regs global sp withdrawal,
       priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
         (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal))
      encoderSegments encoderAfter /\
    exists prefixGroup outputGroup suffixGroup,
      encoderSegments = (prefixGroup ++ outputGroup) ++ suffixGroup /\
      length prefixStates = 8%nat /\
      length outputStates = 6%nat /\
      length suffixStates = 4%nat /\
      nth_error prefixStates 0 = Some
        (writeSuccessWithdrawalsSecondEncoderEntry regs global sp withdrawal,
         priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
           (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)) /\
      nth_error prefixStates 7 = nth_error outputStates 0 /\
      nth_error outputStates 5 = nth_error suffixStates 0 /\
      nth_error suffixStates 3 = Some encoderAfter /\
      WriteSuccessWithdrawalsPositionEdges prefixGroup prefixStates /\
      WriteSuccessWithdrawalsPositionEdges outputGroup outputStates /\
      WriteSuccessWithdrawalsPositionEdges suffixGroup suffixStates /\
      (forall offset stateAt, (offset < 7)%nat ->
        nth_error prefixStates offset = Some stateAt ->
        writeSuccessWithdrawalsPositionState remaining (365 + offset) stateAt) /\
      (forall offset stateAt, (offset < 5)%nat ->
        nth_error outputStates offset = Some stateAt ->
        writeSuccessWithdrawalsPositionState remaining
          (365 + (7 + offset))%nat stateAt) /\
      (forall offset stateAt, (offset < 3)%nat ->
        nth_error suffixStates offset = Some stateAt ->
        writeSuccessWithdrawalsPositionState remaining
          (365 + (12 + offset))%nat stateAt).
Proof.
  intros Hinv Hrun.
  have Hrun362 : WriteSuccessWithdrawalsRecordedRun (362 + 48) state segments after
    by exact Hrun.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 362 48 state segments after
    Hrun362) as (beforeSegments & state362 & tail48 & Hsegments0 & H362 & H48).
  destruct (writeSuccessWithdrawalsIterationThroughFirstEncoderCoveredContext
    args sp pointer base total processed (S remaining) withdrawal allBytes prefix
    current suffix scratch encoderScratch registerFrame memoryFrame priorLog state
    beforeSegments state362 Hinv H362) as
    (regs0 & global0 & regs & global & Hprefix & Hentry & Hstate362).
  rewrite Hstate362 in H48.
  have Hrun3 : WriteSuccessWithdrawalsRecordedRun (3 + 45)
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal,
       priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
         (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal))
      tail48 after by exact H48.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 3 45 _ tail48 after Hrun3)
    as (handoffSegments & state365 & tail45 & Hsegments1 & Hhandoff & H45).
  rewrite (writeSuccessWithdrawals156b4SecondEncoderCovered args sp pointer base
    total processed (S remaining) withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs
    global handoffSegments state365 Hinv Hprefix Hentry Hhandoff) in H45.
  have Hrun15 : WriteSuccessWithdrawalsRecordedRun (15 + 30)
      (writeSuccessWithdrawalsSecondEncoderEntry regs global sp withdrawal,
       priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
         (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal))
      tail45 after by exact H45.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 15 30 _ tail45 after Hrun15)
    as (encoderSegments & encoderAfter & tail30 & Hsegments2 & Hencoder & H30).
  have HencoderInv := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer
    base total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    regs global Hinv Hprefix Hentry.
  destruct (writeSuccessWithdrawals156b4HandoffPositionStates args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs
    global Hinv Hprefix Hentry) as (_ & _ & Hposition364).
  unfold writeSuccessWithdrawalsPositionState in Hposition364.
  destruct Hposition364 as (_ & _ & _ & _ & Hx9bc & _).
  have Hx9 :
      (writeSuccessWithdrawalsSecondEncoderEntry regs global sp withdrawal).1.(seq_regs)
        !! "x9" = Some (RVal_Bits
          (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccessWithdrawalsSecondEncoderEntry, writeSuccess156bcAfter,
      writeSuccess15694Local. cbn.
    rewrite writeSuccess156bcRegsLookupOther; try discriminate. exact Hx9bc. }
  have Hrange : (Z.of_nat (S remaining) < 2 ^ 64)%Z.
  { have Hremaining := writeSuccessWithdrawalsIterationRemainingRange args sp
      pointer base total processed (S remaining) withdrawal allBytes prefix current
      suffix scratch encoderScratch registerFrame memoryFrame priorLog state Hinv.
    lia. }
  destruct (writeSuccessWithdrawalsEncoderIntActualPositionsFromInv remaining 365
    (writeSuccessWithdrawalsValidatorValue withdrawal) sp
    (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsFirstEncoderScratch sp withdrawal)
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).2.(seq_mem)
    (priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
      (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal))
    (writeSuccessWithdrawalsSecondEncoderEntry regs global sp withdrawal,
     priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
       (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal))
    encoderSegments encoderAfter
    ltac:(unfold writeSuccessWithdrawalsEncoderIntPositionStart; tauto)
    HencoderInv Hx9 Hrange Hencoder) as
    (encoderRegs & encoderGlobal & prefixGroup & outputGroup & suffixGroup &
     prefixStates & outputStates & suffixStates & HencoderEntry &
     HencoderAfter & Hgroups).
  exists regs0, global0, regs, global, encoderRegs, encoderGlobal,
    encoderSegments, encoderAfter, prefixStates, outputStates, suffixStates.
  split; first exact Hprefix.
  split; first exact Hentry.
  split; first exact HencoderEntry.
  split; first exact HencoderAfter.
  split; first exact HencoderInv.
  split; first exact Hencoder.
  exists prefixGroup, outputGroup, suffixGroup. exact Hgroups.
Qed.

Print Assumptions writeSuccessWithdrawalsSecondEncoderActualPositionsFrom15694.
