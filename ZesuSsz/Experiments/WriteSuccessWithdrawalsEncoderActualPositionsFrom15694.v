From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0FinalEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAmountRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFirstEncoderActualPositionsFrom15694.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsSecondEncoderActualPositionsFrom15694.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalEncoderActualPositionsFrom15694.

Import ListNotations.

Definition WriteSuccessWithdrawalsEncoderActualPositionPackage remaining start
    (value sp returnAddress : bv 64) scratch memoryFrame priorLog state segments
    after : Prop :=
  Inv_encoder_int value sp returnAddress scratch memoryFrame priorLog state /\
  WriteSuccessWithdrawalsRecordedRun 15 state segments after /\
  exists prefix output suffix prefixStates outputStates suffixStates,
    segments = (prefix ++ output) ++ suffix /\
    length prefixStates = 8%nat /\
    length outputStates = 6%nat /\
    length suffixStates = 4%nat /\
    nth_error prefixStates 0 = Some state /\
    nth_error prefixStates 7 = nth_error outputStates 0 /\
    nth_error outputStates 5 = nth_error suffixStates 0 /\
    nth_error suffixStates 3 = Some after /\
    WriteSuccessWithdrawalsPositionEdges prefix prefixStates /\
    WriteSuccessWithdrawalsPositionEdges output outputStates /\
    WriteSuccessWithdrawalsPositionEdges suffix suffixStates /\
    (forall offset stateAt, (offset < 7)%nat ->
      nth_error prefixStates offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining (start + offset) stateAt) /\
    (forall offset stateAt, (offset < 5)%nat ->
      nth_error outputStates offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining
        (start + (7 + offset))%nat stateAt) /\
    (forall offset stateAt, (offset < 3)%nat ->
      nth_error suffixStates offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining
        (start + (12 + offset))%nat stateAt).

Theorem writeSuccessWithdrawalsThreeEncoderActualPositionsFrom15694 args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state segments after :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 410 state segments after ->
  (exists regs0 global0 firstSegments firstAfter,
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs0 global0 /\
    WriteSuccessWithdrawalsEncoderActualPositionPackage remaining 347
      (writeSuccessWithdrawalsIndexValue withdrawal) sp
      (Z_to_bv 64 0x156b4) encoderScratch
      (writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer
        current withdrawal).2.(seq_mem) priorLog
      (writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer
        current withdrawal, priorLog) firstSegments firstAfter) /\
  (exists regs0 global0 regs global secondSegments secondAfter,
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs0 global0 /\
    writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
      withdrawal = writeSuccess15d10Before regs global /\
    WriteSuccessWithdrawalsEncoderActualPositionPackage remaining 365
      (writeSuccessWithdrawalsValidatorValue withdrawal) sp
      (Z_to_bv 64 0x156c0)
      (writeSuccessWithdrawalsFirstEncoderScratch sp withdrawal)
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp
        withdrawal).2.(seq_mem)
      (priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
        (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal))
      (writeSuccessWithdrawalsSecondEncoderEntry regs global sp withdrawal,
       priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
         (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal))
      secondSegments secondAfter) /\
  exists regs0 global0 regs1 global1 regs2 global2 outputRegs outputGlobal
      finalSegments finalAfter,
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs0 global0 /\
    writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
      withdrawal = writeSuccess15d10Before regs1 global1 /\
    writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal =
      writeSuccess15d10Before regs2 global2 /\
    writeSuccessWithdrawalsOutputEntry
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
        withdrawal).1.(seq_regs)
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
        withdrawal).2 (sp + BV 64 1768)%bv =
      writeSuccess10190Before outputRegs outputGlobal /\
    WriteSuccessWithdrawalsEncoderActualPositionPackage remaining 392
      (writeSuccessWithdrawalsAmountValue withdrawal) sp
      (Z_to_bv 64 0x156dc)
      (writeSuccessWithdrawalsSecondEncoderScratch sp withdrawal)
      outputGlobal.(seq_mem)
      (writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
        withdrawal ++ writeSuccessWithdrawalsOutputRecordsExact outputGlobal
          (sp + BV 64 1768)%bv (BV 64 20))
      (writeSuccess156d8After
        (writeSuccess156d4Regs
          (writeSuccess156d0Regs
            (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
            (writeSuccessWithdrawalsAmountValue withdrawal))) outputGlobal,
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
         withdrawal ++ writeSuccessWithdrawalsOutputRecordsExact outputGlobal
           (sp + BV 64 1768)%bv (BV 64 20)) finalSegments finalAfter.
Proof.
  intros Hinv Hrun.
  destruct (writeSuccessWithdrawalsFirstEncoderActualPositionsFrom15694 args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state segments
    after Hinv Hrun) as
    (regs0a & global0a & firstSegments & firstAfter & firstPrefixStates &
     firstOutputStates & firstSuffixStates & Hprefix0 & Hinv0 & Hrun0 &
     firstPrefixGroup & firstOutputGroup & firstSuffixGroup & Hgroups0).
  destruct (writeSuccessWithdrawalsSecondEncoderActualPositionsFrom15694 args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state segments
    after Hinv Hrun) as
    (regs0b & global0b & regs1b & global1b & secondSegments & secondAfter &
     secondPrefixStates & secondOutputStates & secondSuffixStates & Hprefix1 &
     Hentry1 & Hinv1 & Hrun1 & secondPrefixGroup & secondOutputGroup &
     secondSuffixGroup & Hgroups1).
  destruct (writeSuccessWithdrawalsFinalEncoderActualPositionsFrom15694 args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state segments
    after Hinv Hrun) as
    (regs0c & global0c & regs1c & global1c & regs2c & global2c & outputRegs &
     outputGlobal & finalSegments & finalAfter & finalPrefixStates &
     finalOutputStates & finalSuffixStates & Hprefix2 & Hentry2a & Hentry2b &
     Houtput2 & Hinv2 & Hrun2 & finalPrefixGroup & finalOutputGroup &
     finalSuffixGroup & Hgroups2).
  split.
  - exists regs0a, global0a, firstSegments, firstAfter.
    split; first exact Hprefix0.
    unfold WriteSuccessWithdrawalsEncoderActualPositionPackage.
    split; first exact Hinv0. split; first exact Hrun0.
    exists firstPrefixGroup, firstOutputGroup, firstSuffixGroup,
      firstPrefixStates, firstOutputStates, firstSuffixStates. exact Hgroups0.
  - split.
    + exists regs0b, global0b, regs1b, global1b, secondSegments, secondAfter.
      split; first exact Hprefix1. split; first exact Hentry1.
      unfold WriteSuccessWithdrawalsEncoderActualPositionPackage.
      split; first exact Hinv1. split; first exact Hrun1.
      exists secondPrefixGroup, secondOutputGroup, secondSuffixGroup,
        secondPrefixStates, secondOutputStates, secondSuffixStates. exact Hgroups1.
    + exists regs0c, global0c, regs1c, global1c, regs2c, global2c, outputRegs,
        outputGlobal, finalSegments, finalAfter.
      split; first exact Hprefix2. split; first exact Hentry2a.
      split; first exact Hentry2b. split; first exact Houtput2.
      unfold WriteSuccessWithdrawalsEncoderActualPositionPackage.
      split; first exact Hinv2. split; first exact Hrun2.
      exists finalPrefixGroup, finalOutputGroup, finalSuffixGroup,
        finalPrefixStates, finalOutputStates, finalSuffixStates. exact Hgroups2.
Qed.

Print Assumptions writeSuccessWithdrawalsThreeEncoderActualPositionsFrom15694.
