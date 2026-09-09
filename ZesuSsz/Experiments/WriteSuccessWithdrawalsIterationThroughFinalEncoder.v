From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156cc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecorded.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntRecordsSemantic.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAmountRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInvContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0FinalEncoderCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0FinalEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0FinalEncoderRecorded.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationThroughAddressOutput.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedRunSplit.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Lemma writeSuccessWithdrawalsIntegerBytesRoundTrip bytes :
  length bytes = 8%nat ->
  bv_to_little_endian 8 8
    (bv_unsigned (Z_to_bv 64 (little_endian_to_bv 8 bytes))) = bytes.
Proof.
  intros Hlength. rewrite Z_to_bv_small.
  - apply bv_to_little_endian_to_bv. lia.
  - pose proof (little_endian_to_bv_bound 8 bytes) as Hbound.
    rewrite Hlength in Hbound. cbn in Hbound. exact Hbound.
Qed.

Lemma writeSuccessWithdrawalsAddressOutputGlobal args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 outputRegs outputGlobal :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer = writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal = writeSuccess15d10Before regs2 global2 ->
  writeSuccessWithdrawalsOutputEntry
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs)
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).2
    (sp + BV 64 1768)%bv = writeSuccess10190Before outputRegs outputGlobal ->
  outputGlobal = writeSuccessEncoderIntGlobal2
    (writeSuccessEncoderIntGlobal2
      (writeSuccessWithdrawals156a8Global regs0 global0 sp pointer current) sp
      (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)) sp
    (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal).
Proof.
  intros Hinv Hprefix Hentry1 Hentry2 Houtput.
  have Hinv1 := writeSuccessWithdrawals156a8EncoderIntInv args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 Hinv Hprefix.
  rewrite Hentry1 in Hinv1.
  have Htable1 : writeSuccessWithdrawalsInstructionTable global1 by (unfold Inv_encoder_int in Hinv1; cbn in Hinv1; tauto).
  destruct (writeSuccessEncoderIntCaller156b4 global1 Htable1) as (Ha1 & tr1 & Hc1).
  have Hg1 := writeSuccessWithdrawalsEncoderIntEndpointGlobal regs1 global1 sp (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal) tr1 Ha1 Hc1.
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 Hinv Hprefix Hentry1.
  rewrite Hentry2 in Hinv2.
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2 by (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  destruct (writeSuccessEncoderIntCaller156c0 global2 Htable2) as (Ha2 & tr2 & Hc2).
  have Hg2 := writeSuccessWithdrawalsEncoderIntEndpointGlobal regs2 global2 sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal) tr2 Ha2 Hc2.
  have He1 := f_equal snd Hentry1. cbn in He1.
  have He2 := f_equal snd Hentry2. cbn in He2.
  have Ho := f_equal snd Houtput. cbn in Ho.
  unfold writeSuccessWithdrawalsOutputEntry in Ho. cbn in Ho.
  unfold writeSuccessWithdrawalsSecondEncoderEndpoint in Ho.
  rewrite Hg2 in Ho. rewrite <- He2, Hg1, <- He1 in Ho. symmetry. exact Ho.
Qed.

Lemma writeSuccessWithdrawalsIterationThroughFinalEncoder args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  exists segments regs0 global0 regs1 global1 regs2 global2 outputRegs outputGlobal finalRegs finalGlobal,
    WriteSuccessWithdrawalsRecordedRun 407 state segments
      (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal),
       (writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal ++ writeSuccessWithdrawalsOutputRecordsExact outputGlobal (sp + BV 64 1768)%bv (BV 64 20)) ++ writeSuccessWithdrawalsEncoderIntRecords finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)) /\
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer = writeSuccess101d4Before regs0 global0 /\
    writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current withdrawal = writeSuccess15d10Before regs1 global1 /\
    writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal = writeSuccess15d10Before regs2 global2 /\
    writeSuccessWithdrawalsOutputEntry (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs) (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).2 (sp + BV 64 1768)%bv = writeSuccess10190Before outputRegs outputGlobal /\
    writeSuccess156d8After (writeSuccess156d4Regs (writeSuccess156d0Regs (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0)) (writeSuccessWithdrawalsAmountValue withdrawal))) outputGlobal = writeSuccess15d10Before finalRegs finalGlobal /\
    writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8) (writeSuccessWithdrawalIntegerBytes (observationWithdrawalIndex withdrawal)) (writeSuccessWithdrawalsEncoderIntRecords global1 sp (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)) /\
    writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8) (writeSuccessWithdrawalIntegerBytes (observationWithdrawalValidatorIndex withdrawal)) (writeSuccessWithdrawalsEncoderIntRecords global2 sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal)) /\
    writeSuccessOutputRecords (sp + BV 64 1768)%bv (BV 64 20) (writeSuccessWithdrawalAddressBytes withdrawal) (writeSuccessWithdrawalsOutputRecordsExact outputGlobal (sp + BV 64 1768)%bv (BV 64 20)) /\
    writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8) (writeSuccessWithdrawalIntegerBytes (observationWithdrawalAmount withdrawal)) (writeSuccessWithdrawalsEncoderIntRecords finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)).
Proof.
  intros Hinv.
  destruct (writeSuccessWithdrawalsIterationThroughAddressOutput args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state Hinv) as (g0 & regs0 & global0 & regs1 & global1 & regs2 & global2 & outputRegs & outputGlobal & H0 & Hp & He1 & He2 & Ho & Haddress).
  have Hglobal := writeSuccessWithdrawalsAddressOutputGlobal args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 outputRegs outputGlobal Hinv Hp He1 He2 Ho.
  have HoutInv := writeSuccessWithdrawals156c0OutputInv args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 Hinv Hp He1 He2. rewrite Ho in HoutInv.
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 Hinv Hp He1.
  rewrite He2 in Hinv2.
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2 by (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  destruct (writeSuccessEncoderIntCaller156c0 global2 Htable2) as (Ha2 & tr2 & Hc2).
  have Hx2end := writeSuccessWithdrawalsEncoderIntEndpointX2 regs2 global2 sp
    (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal)
    tr2 Ha2 Hc2.
  have Horeg := f_equal (fun machine => machine.1.(seq_regs)) Ho. cbn in Horeg.
  have Hx2 : outputRegs !! "x2" = Some (RVal_Bits sp).
  { rewrite <- Horeg. unfold writeSuccessWithdrawalsOutputEntry,
      writeSuccessWithdrawalsSecondEncoderEndpoint. cbn.
    rewrite writeSuccess156ccRegsLookupOther; try discriminate.
    rewrite writeSuccess156c8RegsLookupOther; try discriminate.
    rewrite writeSuccess156c4RegsLookupOther; try discriminate.
    rewrite writeSuccess156c0RegsLookupOther; try discriminate. exact Hx2end. }
  set (outLog := writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal).
  destruct (writeSuccessWithdrawals156d0FinalEncoderRecorded args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 outputRegs outputGlobal outLog (writeSuccessWithdrawalsIndexValue withdrawal) (writeSuccessWithdrawalsValidatorValue withdrawal) Hinv Hglobal Hx2 HoutInv) as (g1 & H1).
  have HfinalInv := writeSuccessWithdrawals156d0FinalEncoderInv args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 outputRegs outputGlobal outLog (writeSuccessWithdrawalsIndexValue withdrawal) (writeSuccessWithdrawalsValidatorValue withdrawal) Hinv Hglobal eq_refl Hx2 HoutInv.
  destruct (block_encoder_int_recorded (writeSuccessWithdrawalsAmountValue withdrawal) sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsSecondEncoderScratch sp withdrawal) outputGlobal.(seq_mem) (outLog ++ writeSuccessWithdrawalsOutputRecordsExact outputGlobal (sp + BV 64 1768)%bv (BV 64 20)) _ HfinalInv) as (g2 & after2 & records2 & H2 & Hpc & Hread & Hframe & Hlog & Hamount0).
  destruct (block_encoder_int_recorded_covered_exact (writeSuccessWithdrawalsAmountValue withdrawal) sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsSecondEncoderScratch sp withdrawal) outputGlobal.(seq_mem) (outLog ++ writeSuccessWithdrawalsOutputRecordsExact outputGlobal (sp + BV 64 1768)%bv (BV 64 20)) _ g2 after2 HfinalInv H2) as (finalRegs & finalGlobal & HfinalEntry & Hafter).
  have H01 : WriteSuccessWithdrawalsRecordedRun 392 state (g0 ++ g1)
      (writeSuccess156d8After
        (writeSuccess156d4Regs
          (writeSuccess156d0Regs
            (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
            (writeSuccessWithdrawalsAmountValue withdrawal))) outputGlobal,
       outLog ++ writeSuccessWithdrawalsOutputRecordsExact outputGlobal
         (sp + BV 64 1768)%bv (BV 64 20)) by
    (replace 392%nat with (389+3)%nat by reflexivity;
     eapply writeSuccessWithdrawalsRecordedRunApp; eassumption).
  have H012 : WriteSuccessWithdrawalsRecordedRun 407 state ((g0 ++ g1) ++ g2) after2 by (replace 407%nat with (392+15)%nat by reflexivity; eapply writeSuccessWithdrawalsRecordedRunApp; eassumption).
  rewrite Hafter in H012.
  have Hrange : islaMemoryRange (bv_unsigned sp - 16) 16 by (unfold Inv_15694 in Hinv; unfold islaMemoryRange; pose proof (bv_unsigned_in_range 64 sp); lia).
  have Hindex := writeSuccessWithdrawalsEncoderIntRecordsSemantic global1 sp (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal) Hrange.
  have Hvalidator := writeSuccessWithdrawalsEncoderIntRecordsSemantic global2 sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal) Hrange.
  have Hamount := writeSuccessWithdrawalsEncoderIntRecordsSemantic finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal) Hrange.
  exists ((g0++g1)++g2), regs0, global0, regs1, global1, regs2, global2, outputRegs, outputGlobal, finalRegs, finalGlobal.
  split; first (unfold outLog in H012; exact H012). split; first exact Hp. split; first exact He1. split; first exact He2. split; first exact Ho. split; first exact HfinalEntry.
  split.
  { unfold writeSuccessWithdrawalsIndexValue in Hindex.
    rewrite writeSuccessWithdrawalsIntegerBytesRoundTrip in Hindex;
      [exact Hindex|apply writeSuccessWithdrawalIntegerBytesLength]. }
  split.
  { unfold writeSuccessWithdrawalsValidatorValue in Hvalidator.
    rewrite writeSuccessWithdrawalsIntegerBytesRoundTrip in Hvalidator;
      [exact Hvalidator|apply writeSuccessWithdrawalIntegerBytesLength]. }
  split; first exact Haddress.
  unfold writeSuccessWithdrawalsAmountValue in Hamount.
  rewrite writeSuccessWithdrawalsIntegerBytesRoundTrip in Hamount;
    [exact Hamount|apply writeSuccessWithdrawalIntegerBytesLength].
Qed.

Print Assumptions writeSuccessWithdrawalsAddressOutputGlobal.
Print Assumptions writeSuccessWithdrawalsIterationThroughFinalEncoder.

Lemma writeSuccessWithdrawalsIterationThroughFinalEncoderCovered args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state segments after :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 407 state segments after ->
  exists regs0 global0 regs1 global1 regs2 global2 outputRegs outputGlobal finalRegs finalGlobal,
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer = writeSuccess101d4Before regs0 global0 /\
    writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current withdrawal = writeSuccess15d10Before regs1 global1 /\
    writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal = writeSuccess15d10Before regs2 global2 /\
    writeSuccessWithdrawalsOutputEntry (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs) (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).2 (sp + BV 64 1768)%bv = writeSuccess10190Before outputRegs outputGlobal /\
    writeSuccess156d8After (writeSuccess156d4Regs (writeSuccess156d0Regs (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0)) (writeSuccessWithdrawalsAmountValue withdrawal))) outputGlobal = writeSuccess15d10Before finalRegs finalGlobal /\
    after =
      (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal),
       (writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal ++ writeSuccessWithdrawalsOutputRecordsExact outputGlobal (sp + BV 64 1768)%bv (BV 64 20)) ++ writeSuccessWithdrawalsEncoderIntRecords finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)) /\
    writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8) (writeSuccessWithdrawalIntegerBytes (observationWithdrawalIndex withdrawal)) (writeSuccessWithdrawalsEncoderIntRecords global1 sp (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)) /\
    writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8) (writeSuccessWithdrawalIntegerBytes (observationWithdrawalValidatorIndex withdrawal)) (writeSuccessWithdrawalsEncoderIntRecords global2 sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal)) /\
    writeSuccessOutputRecords (sp + BV 64 1768)%bv (BV 64 20) (writeSuccessWithdrawalAddressBytes withdrawal) (writeSuccessWithdrawalsOutputRecordsExact outputGlobal (sp + BV 64 1768)%bv (BV 64 20)) /\
    writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8) (writeSuccessWithdrawalIntegerBytes (observationWithdrawalAmount withdrawal)) (writeSuccessWithdrawalsEncoderIntRecords finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)).
Proof.
  intros Hinv Hrun.
  have Hrun389_18 : WriteSuccessWithdrawalsRecordedRun (389+18) state segments after by exact Hrun.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 389 18 state segments after Hrun389_18) as (g0 & state389 & tail18 & Hsegs0 & H0 & H18).
  destruct (writeSuccessWithdrawalsIterationThroughAddressOutputCovered args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state g0 state389 Hinv H0) as (regs0 & global0 & regs1 & global1 & regs2 & global2 & outputRegs & outputGlobal & Hp & He1 & He2 & Ho & Hstate389 & Haddress).
  rewrite Hstate389 in H18.
  have Hrun3_15 : WriteSuccessWithdrawalsRecordedRun (3+15)
      (writeSuccess101a0After (writeSuccessOutputRegs4 outputRegs) outputGlobal (Z_to_bv 64 0x156d0),
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal ++ writeSuccessWithdrawalsOutputRecordsExact outputGlobal (sp + BV 64 1768)%bv (BV 64 20)) tail18 after by exact H18.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 3 15 _ tail18 after Hrun3_15) as (g1 & state392 & g2 & Hsegs1 & H1 & H2).
  have Hglobal := writeSuccessWithdrawalsAddressOutputGlobal args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 outputRegs outputGlobal Hinv Hp He1 He2 Ho.
  have HoutInv := writeSuccessWithdrawals156c0OutputInv args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 Hinv Hp He1 He2. rewrite Ho in HoutInv.
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 Hinv Hp He1. rewrite He2 in Hinv2.
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2 by (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  destruct (writeSuccessEncoderIntCaller156c0 global2 Htable2) as (Ha2 & tr2 & Hc2).
  have Hx2end := writeSuccessWithdrawalsEncoderIntEndpointX2 regs2 global2 sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal) tr2 Ha2 Hc2.
  have Horeg := f_equal (fun machine => machine.1.(seq_regs)) Ho. cbn in Horeg.
  have Hx2 : outputRegs !! "x2" = Some (RVal_Bits sp).
  { rewrite <- Horeg. unfold writeSuccessWithdrawalsOutputEntry, writeSuccessWithdrawalsSecondEncoderEndpoint. cbn.
    rewrite writeSuccess156ccRegsLookupOther; try discriminate. rewrite writeSuccess156c8RegsLookupOther; try discriminate.
    rewrite writeSuccess156c4RegsLookupOther; try discriminate. rewrite writeSuccess156c0RegsLookupOther; try discriminate. exact Hx2end. }
  set (outLog := writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal).
  rewrite (writeSuccessWithdrawals156d0FinalEncoderCovered args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 outputRegs outputGlobal outLog (writeSuccessWithdrawalsIndexValue withdrawal) (writeSuccessWithdrawalsValidatorValue withdrawal) g1 state392 Hinv Hglobal Hx2 HoutInv H1) in H2.
  have HfinalInv := writeSuccessWithdrawals156d0FinalEncoderInv args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 outputRegs outputGlobal outLog (writeSuccessWithdrawalsIndexValue withdrawal) (writeSuccessWithdrawalsValidatorValue withdrawal) Hinv Hglobal eq_refl Hx2 HoutInv.
  destruct (block_encoder_int_recorded_covered_exact (writeSuccessWithdrawalsAmountValue withdrawal) sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsSecondEncoderScratch sp withdrawal) outputGlobal.(seq_mem) (outLog ++ writeSuccessWithdrawalsOutputRecordsExact outputGlobal (sp + BV 64 1768)%bv (BV 64 20)) _ g2 after HfinalInv H2) as (finalRegs & finalGlobal & HfinalEntry & Hafter).
  have Hrange : islaMemoryRange (bv_unsigned sp - 16) 16 by (unfold Inv_15694 in Hinv; unfold islaMemoryRange; pose proof (bv_unsigned_in_range 64 sp); lia).
  have Hindex := writeSuccessWithdrawalsEncoderIntRecordsSemantic global1 sp (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal) Hrange.
  have Hvalidator := writeSuccessWithdrawalsEncoderIntRecordsSemantic global2 sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal) Hrange.
  have Hamount := writeSuccessWithdrawalsEncoderIntRecordsSemantic finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal) Hrange.
  exists regs0, global0, regs1, global1, regs2, global2, outputRegs, outputGlobal, finalRegs, finalGlobal.
  split; first exact Hp. split; first exact He1. split; first exact He2. split; first exact Ho. split; first exact HfinalEntry. split; first (unfold outLog in Hafter; exact Hafter).
  split. { unfold writeSuccessWithdrawalsIndexValue in Hindex. rewrite writeSuccessWithdrawalsIntegerBytesRoundTrip in Hindex; [exact Hindex|apply writeSuccessWithdrawalIntegerBytesLength]. }
  split. { unfold writeSuccessWithdrawalsValidatorValue in Hvalidator. rewrite writeSuccessWithdrawalsIntegerBytesRoundTrip in Hvalidator; [exact Hvalidator|apply writeSuccessWithdrawalIntegerBytesLength]. }
  split; first exact Haddress.
  unfold writeSuccessWithdrawalsAmountValue in Hamount. rewrite writeSuccessWithdrawalsIntegerBytesRoundTrip in Hamount; [exact Hamount|apply writeSuccessWithdrawalIntegerBytesLength].
Qed.

Print Assumptions writeSuccessWithdrawalsIterationThroughFinalEncoderCovered.
