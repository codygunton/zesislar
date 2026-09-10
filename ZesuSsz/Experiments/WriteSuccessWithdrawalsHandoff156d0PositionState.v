From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_94.a156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAmountRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0EncoderIntContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0FinalEncoderCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0PositionStateDirect.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputPositionContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationThroughFinalEncoder.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Open Scope Z_scope.

Theorem writeSuccessWithdrawals156d0RecordedPositionStates args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    regs1 global1 regs2 global2 outputRegs global outputPriorLog segments after :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal =
    writeSuccess15d10Before regs2 global2 ->
  writeSuccessWithdrawalsOutputEntry
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
      withdrawal).1.(seq_regs)
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
      withdrawal).2 (sp + BV 64 1768)%bv =
    writeSuccess10190Before outputRegs global ->
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
  writeSuccessWithdrawalsConcretePc after = Some 0x15d10 /\
  after.1.1.(seq_regs) !! "x1" =
    Some (RVal_Bits (Z_to_bv 64 0x156dc)) /\
  writeSuccessWithdrawalsSelectedOccurrence after 0x15d10 = Some 2%nat /\
  after.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) /\
  exists states,
    length states = 4%nat /\
    nth_error states 0 =
      Some
        (writeSuccess101a0After (writeSuccessOutputRegs4 outputRegs) global
           (Z_to_bv 64 0x156d0),
         outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
           (sp + BV 64 1768)%bv (BV 64 20)) /\
    nth_error states 1 =
      Some
        (writeSuccess156d0After
          (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
          global (writeSuccessWithdrawalsAmountValue withdrawal),
         outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
           (sp + BV 64 1768)%bv (BV 64 20)) /\
    nth_error states 2 =
      Some
        (writeSuccess156d4After
          (writeSuccess156d0Regs
            (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
            (writeSuccessWithdrawalsAmountValue withdrawal)) global,
         outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
           (sp + BV 64 1768)%bv (BV 64 20)) /\
    nth_error states 3 = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states /\
    forall offset stateAt,
      (offset < 3)%nat ->
      nth_error states offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining (389 + offset) stateAt.
Proof.
  intros Hinv Hprefix Hentry1 Hentry2 Houtput Hx2 HoutputInv Hrecorded.
  have Hglobal := writeSuccessWithdrawalsAddressOutputGlobal args sp pointer
    base total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    regs1 global1 regs2 global2 outputRegs global Hinv Hprefix Hentry1 Hentry2
    Houtput.
  have Htable : writeSuccessWithdrawalsInstructionTable global by
    (unfold Inv_write_output in HoutputInv; cbn in HoutputInv; tauto).
  destruct (writeSuccessOutputCaller156d0 global Htable) as
    (HreturnAlign & returnTrace & HreturnCode).
  have Hstart := writeSuccessOutputEndpointExact outputRegs global
    (Z_to_bv 64 0x156d0) returnTrace HreturnAlign HreturnCode.
  have Hcode : global.(seq_instrs) !! Z_to_bv 64 0x156d0 = Some a156d0 by
    (apply Htable; cbn; tauto).
  have Htrace : returnTrace = a156d0 by congruence.
  subst returnTrace.
  have Hfacts0 : writeSuccessWithdrawalsOperationalRegisterFacts outputRegs by
    (unfold Inv_write_output in HoutputInv; cbn in HoutputInv; tauto).
  have Hfacts := writeSuccessOutputEndpointFacts outputRegs
    (Z_to_bv 64 0x156d0) Hfacts0.
  have Hsp := writeSuccessWithdrawalsOutputEndpointX2 outputRegs sp Hx2.
  have HspAlign : bv_unsigned sp `mod` 16 = 0 by
    (unfold Inv_15694 in Hinv; tauto).
  have HspLower : 0x20000000 <= bv_unsigned sp - 16 by
    (unfold Inv_15694 in Hinv; tauto).
  have HspUpper : bv_unsigned sp + 1792 < 0x40000000 by
    (unfold Inv_15694 in Hinv; tauto).
  destruct (writeSuccessWithdrawals156d0Context
    (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0)) sp
    Hfacts Hsp HspAlign HspLower HspUpper) as
    (mstatusBits & satp & oldDest & oldX1 & Hmstatus & Hsatp & Hdest & Hx1 &
     Hsys & HmstatusEval & Haligned & Hlower & Hupper).
  have Hread := writeSuccessWithdrawalsFinalAmountRead args sp pointer base total
    processed (S remaining) withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    (writeSuccessWithdrawalsIndexValue withdrawal)
    (writeSuccessWithdrawalsValidatorValue withdrawal) outputRegs Hinv.
  cbn -[writeSuccessEncoderIntGlobal2] in Hread.
  rewrite <- Hglobal in Hread.
  have HstartGlobal := f_equal snd Hstart.
  cbn in HstartGlobal. rewrite HstartGlobal in Hread.
  destruct (writeSuccessWithdrawalsOutputPositionContext args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 outputRegs global Hinv Hprefix Hentry1 Hentry2 Houtput)
    as (_ & HoutputX9 & Hrange).
  have Hx9 : writeSuccessOutputEndpointRegs outputRegs
      (Z_to_bv 64 0x156d0) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { rewrite writeSuccessOutputEndpointLookupOther; try discriminate.
    exact HoutputX9. }
  have Hrecorded' : WriteSuccessWithdrawalsRecordedRun 3
      (writeSuccess156d0Before
        (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0)) global,
       outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
         (sp + BV 64 1768)%bv (BV 64 20)) segments after.
  { have HstartPair :
      (writeSuccess101a0After (writeSuccessOutputRegs4 outputRegs) global
         (Z_to_bv 64 0x156d0),
       outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
         (sp + BV 64 1768)%bv (BV 64 20)) =
      (writeSuccess156d0Before
        (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0)) global,
       outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
         (sp + BV 64 1768)%bv (BV 64 20)) by
      (f_equal; exact Hstart).
    rewrite <- HstartPair. exact Hrecorded. }
  destruct (writeSuccessWithdrawals156d0RecordedPositionStatesDirect
    (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0)) global sp
    (writeSuccessWithdrawalsAmountValue withdrawal)
    (outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
      (sp + BV 64 1768)%bv (BV 64 20)) mstatusBits satp oldDest oldX1 segments
    after remaining
    ltac:(unfold writeSuccessOutputEndpointRegs, writeSuccess101a0Regs;
      rewrite lookup_insert;
      rewrite (writeSuccessOutputReturnTargetExact _ HreturnAlign); reflexivity)
    Hsp Hmstatus Hsatp Hdest Hx1 Hsys HmstatusEval Haligned Hlower Hupper Hread
    Htable Hx9 Hrange Hrecorded') as
    (states & Hlength & Hstate0 & Hstate1 & Hstate2 & Hstate3 & Hedges & Hpos).
  have Hafter := writeSuccessWithdrawals156d0FinalEncoderCovered args sp pointer
    base total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    outputRegs global outputPriorLog (writeSuccessWithdrawalsIndexValue withdrawal)
    (writeSuccessWithdrawalsValidatorValue withdrawal) segments after Hinv
    Hglobal Hx2 HoutputInv Hrecorded.
  split; first exact Hafter.
  split.
  { rewrite Hafter. unfold writeSuccessWithdrawalsConcretePc,
      writeSuccess156d8After, writeSuccess15694Local. cbn.
    rewrite lookup_insert. destruct writeSuccess156d8ValuesExact as (_ & _ & _ & Hpc).
    rewrite Hpc. unfold bvn_unsigned. cbn. rewrite Z_to_bv_unsigned.
    vm_compute. reflexivity. }
  split.
  { rewrite Hafter. cbn. unfold writeSuccess156d8Regs.
    rewrite lookup_insert_ne; last discriminate. rewrite lookup_insert.
    destruct writeSuccess156d8ValuesExact as (_ & Hlink & _). rewrite Hlink.
    reflexivity. }
  split.
  { rewrite Hafter. unfold writeSuccessWithdrawalsSelectedOccurrence,
      writeSuccessWithdrawalsRegisterUnsigned. cbn.
    unfold writeSuccess156d8Regs. rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert. destruct writeSuccess156d8ValuesExact as (_ & Hlink & _).
    rewrite Hlink. reflexivity. }
  split.
  { rewrite Hafter. cbn. rewrite writeSuccess156d8RegsLookupOther;
      try discriminate. rewrite writeSuccess156d4RegsLookupOther;
      try discriminate. rewrite writeSuccess156d0RegsLookupOther;
      try discriminate. exact Hx9. }
  exists states. repeat split; try assumption.
  change (nth_error states 0 =
    Some ((writeSuccess15694Local a156d0
      (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0)), global),
      outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
        (sp + BV 64 1768)%bv (BV 64 20))) in Hstate0.
  rewrite <- Hstart in Hstate0. exact Hstate0.
Qed.

Print Assumptions writeSuccessWithdrawals156d0RecordedPositionStates.
