From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156cc.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedRunSplit.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntActualPositionsFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationThroughAddressOutput.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationThroughFinalEncoder.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationBounds.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInvContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationSecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAmountRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0FinalEncoderCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0FinalEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0PositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.

Import ListNotations.
Open Scope Z_scope.

Theorem writeSuccessWithdrawalsFinalEncoderActualPositionsFrom15694 args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state segments after :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 410 state segments after ->
  exists regs0 global0 regs1 global1 regs2 global2 outputRegs outputGlobal
      encoderSegments encoderAfter prefixStates outputStates suffixStates,
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
    WriteSuccessWithdrawalsRecordedRun 15
      (writeSuccess156d8After
        (writeSuccess156d4Regs
          (writeSuccess156d0Regs
            (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
            (writeSuccessWithdrawalsAmountValue withdrawal))) outputGlobal,
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
         withdrawal ++ writeSuccessWithdrawalsOutputRecordsExact outputGlobal
           (sp + BV 64 1768)%bv (BV 64 20))
      encoderSegments encoderAfter /\
    exists prefixGroup outputGroup suffixGroup,
      encoderSegments = (prefixGroup ++ outputGroup) ++ suffixGroup /\
      length prefixStates = 8%nat /\
      length outputStates = 6%nat /\
      length suffixStates = 4%nat /\
      nth_error prefixStates 0 = Some
        (writeSuccess156d8After
          (writeSuccess156d4Regs
            (writeSuccess156d0Regs
              (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
              (writeSuccessWithdrawalsAmountValue withdrawal))) outputGlobal,
         writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
           withdrawal ++ writeSuccessWithdrawalsOutputRecordsExact outputGlobal
             (sp + BV 64 1768)%bv (BV 64 20)) /\
      nth_error prefixStates 7 = nth_error outputStates 0 /\
      nth_error outputStates 5 = nth_error suffixStates 0 /\
      nth_error suffixStates 3 = Some encoderAfter /\
      WriteSuccessWithdrawalsPositionEdges prefixGroup prefixStates /\
      WriteSuccessWithdrawalsPositionEdges outputGroup outputStates /\
      WriteSuccessWithdrawalsPositionEdges suffixGroup suffixStates /\
      (forall offset stateAt, (offset < 7)%nat ->
        nth_error prefixStates offset = Some stateAt ->
        writeSuccessWithdrawalsPositionState remaining (392 + offset) stateAt) /\
      (forall offset stateAt, (offset < 5)%nat ->
        nth_error outputStates offset = Some stateAt ->
        writeSuccessWithdrawalsPositionState remaining
          (392 + (7 + offset))%nat stateAt) /\
      (forall offset stateAt, (offset < 3)%nat ->
        nth_error suffixStates offset = Some stateAt ->
        writeSuccessWithdrawalsPositionState remaining
          (392 + (12 + offset))%nat stateAt).
Proof.
  intros Hinv Hrun.
  have Hrun389 : WriteSuccessWithdrawalsRecordedRun (389 + 21) state segments after
    by exact Hrun.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 389 21 state segments after
    Hrun389) as (beforeSegments & state389 & tail21 & Hsegments0 & H389 & H21).
  destruct (writeSuccessWithdrawalsIterationThroughAddressOutputCovered args sp
    pointer base total processed (S remaining) withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state
    beforeSegments state389 Hinv H389) as
    (regs0 & global0 & regs1 & global1 & regs2 & global2 & outputRegs &
     outputGlobal & Hprefix & Hentry1 & Hentry2 & Houtput & Hstate389 & Hrecords).
  rewrite Hstate389 in H21.
  have Hrun3 : WriteSuccessWithdrawalsRecordedRun (3 + 18)
      (writeSuccess101a0After (writeSuccessOutputRegs4 outputRegs) outputGlobal
         (Z_to_bv 64 0x156d0),
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
         withdrawal ++ writeSuccessWithdrawalsOutputRecordsExact outputGlobal
           (sp + BV 64 1768)%bv (BV 64 20)) tail21 after by exact H21.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 3 18 _ tail21 after Hrun3)
    as (handoffSegments & state392 & tail18 & Hsegments1 & Hhandoff & H18).
  have Hglobal := writeSuccessWithdrawalsAddressOutputGlobal args sp pointer base
    total processed (S remaining) withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 outputRegs outputGlobal Hinv Hprefix Hentry1 Hentry2
    Houtput.
  have HoutInv := writeSuccessWithdrawals156c0OutputInv args sp pointer base total
    processed (S remaining) withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2.
  rewrite Houtput in HoutInv.
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer base
    total processed (S remaining) withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 Hinv Hprefix Hentry1.
  rewrite Hentry2 in Hinv2.
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2 by
    (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  destruct (writeSuccessEncoderIntCaller156c0 global2 Htable2) as
    (Halign2 & trace2 & Hcode2).
  have Hx2end := writeSuccessWithdrawalsEncoderIntEndpointX2 regs2 global2 sp
    (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal)
    trace2 Halign2 Hcode2.
  have HoutputRegs := f_equal (fun machine => machine.1.(seq_regs)) Houtput.
  cbn in HoutputRegs.
  have Hx2 : outputRegs !! "x2" = Some (RVal_Bits sp).
  { rewrite <- HoutputRegs.
    unfold writeSuccessWithdrawalsOutputEntry,
      writeSuccessWithdrawalsSecondEncoderEndpoint. cbn.
    rewrite writeSuccess156ccRegsLookupOther; try discriminate.
    rewrite writeSuccess156c8RegsLookupOther; try discriminate.
    rewrite writeSuccess156c4RegsLookupOther; try discriminate.
    rewrite writeSuccess156c0RegsLookupOther; try discriminate. exact Hx2end. }
  set (outLog := writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2
    sp withdrawal).
  rewrite (writeSuccessWithdrawals156d0FinalEncoderCovered args sp pointer base
    total processed (S remaining) withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 outputRegs
    outputGlobal outLog (writeSuccessWithdrawalsIndexValue withdrawal)
    (writeSuccessWithdrawalsValidatorValue withdrawal) handoffSegments state392
    Hinv Hglobal Hx2 HoutInv Hhandoff) in H18.
  have Hrun15 : WriteSuccessWithdrawalsRecordedRun (15 + 3)
      (writeSuccess156d8After
        (writeSuccess156d4Regs
          (writeSuccess156d0Regs
            (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
            (writeSuccessWithdrawalsAmountValue withdrawal))) outputGlobal,
       outLog ++ writeSuccessWithdrawalsOutputRecordsExact outputGlobal
         (sp + BV 64 1768)%bv (BV 64 20)) tail18 after by exact H18.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 15 3 _ tail18 after Hrun15)
    as (encoderSegments & encoderAfter & tail3 & Hsegments2 & Hencoder & H3).
  have HfinalInv := writeSuccessWithdrawals156d0FinalEncoderInv args sp pointer base
    total processed (S remaining) withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 outputRegs
    outputGlobal outLog (writeSuccessWithdrawalsIndexValue withdrawal)
    (writeSuccessWithdrawalsValidatorValue withdrawal) Hinv Hglobal eq_refl Hx2
    HoutInv.
  destruct (writeSuccessWithdrawals156d0RecordedPositionStates args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 outputRegs outputGlobal outLog handoffSegments state392
    Hinv Hprefix Hentry1 Hentry2 Houtput Hx2 HoutInv Hhandoff) as
    (Hstate392Exact & _ & _ & _ & Hx9 & _ & positionStates & HpositionFacts).
  rewrite Hstate392Exact in Hx9.
  have Hrange : (Z.of_nat (S remaining) < 2 ^ 64)%Z.
  { have Hremaining := writeSuccessWithdrawalsIterationRemainingRange args sp
      pointer base total processed (S remaining) withdrawal allBytes prefix current
      suffix scratch encoderScratch registerFrame memoryFrame priorLog state Hinv.
    lia. }
  destruct (writeSuccessWithdrawalsEncoderIntActualPositionsFromInv remaining 392
    (writeSuccessWithdrawalsAmountValue withdrawal) sp
    (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsSecondEncoderScratch sp withdrawal)
    outputGlobal.(seq_mem)
    (outLog ++ writeSuccessWithdrawalsOutputRecordsExact outputGlobal
      (sp + BV 64 1768)%bv (BV 64 20))
    (writeSuccess156d8After
      (writeSuccess156d4Regs
        (writeSuccess156d0Regs
          (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
          (writeSuccessWithdrawalsAmountValue withdrawal))) outputGlobal,
     outLog ++ writeSuccessWithdrawalsOutputRecordsExact outputGlobal
       (sp + BV 64 1768)%bv (BV 64 20))
    encoderSegments encoderAfter
    ltac:(unfold writeSuccessWithdrawalsEncoderIntPositionStart; tauto)
    HfinalInv Hx9 Hrange Hencoder) as
    (prefixGroup & outputGroup & suffixGroup & prefixStates & outputStates &
     suffixStates & Hgroups).
  exists regs0, global0, regs1, global1, regs2, global2, outputRegs, outputGlobal,
    encoderSegments, encoderAfter, prefixStates, outputStates, suffixStates.
  split; first exact Hprefix.
  split; first exact Hentry1.
  split; first exact Hentry2.
  split; first exact Houtput.
  split; first (unfold outLog in Hencoder; exact Hencoder).
  exists prefixGroup, outputGroup, suffixGroup.
  unfold outLog in Hgroups. exact Hgroups.
Qed.

Print Assumptions writeSuccessWithdrawalsFinalEncoderActualPositionsFrom15694.
