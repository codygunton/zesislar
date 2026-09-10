From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAmountRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIteration410.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIteration410Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationRecordsComposition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationSemantic.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsNonfinalIterationCovered args sp pointer base total
    processed r withdrawal nextWithdrawal allBytes prefix current nextCurrent
    nextSuffix scratch encoderScratch registerFrame memoryFrame priorLog state
    segments after :
  Inv_15694 args sp pointer base total processed (S (S r)) withdrawal
    allBytes prefix current (nextCurrent ++ nextSuffix) scratch encoderScratch
    registerFrame memoryFrame priorLog state ->
  nth_error (observationWithdrawals
    (successDecoded WriteSuccessObservation args)) (S processed) =
    Some nextWithdrawal ->
  length nextCurrent = 48%nat ->
  WriteSuccessWithdrawalsRecordedRun 410 state segments after ->
  exists records padding nextPadding regs0 global0 regs1 global1
      regs2 global2 outputRegs outputGlobal finalRegs finalGlobal,
    WriteSuccessWithdrawalsRecordedRun 410 state segments after /\
    after =
      (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
         pointer (S r) withdrawal,
       writeSuccessWithdrawalsIteration410Log priorLog global1 global2
         outputGlobal finalGlobal sp withdrawal) /\
    after.2 = priorLog ++ records /\
    writeSuccessWithdrawalIterationRecords sp withdrawal records /\
    length padding = 4%nat /\
    current = writeSuccessWithdrawalRawBytes withdrawal padding /\
    bv_unsigned (pointer + BV 64 48)%bv =
      base + 48 * Z.of_nat (S processed) /\
    allBytes = (prefix ++ current) ++ nextCurrent ++ nextSuffix /\
    length (prefix ++ current) = (48 * S processed)%nat /\
    skipn 48 (nextCurrent ++ nextSuffix) = nextSuffix /\
    length nextSuffix = (48 * r)%nat /\
    length nextPadding = 4%nat /\
    nextCurrent = writeSuccessWithdrawalRawBytes nextWithdrawal nextPadding /\
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs0 global0 /\
    writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer
      current withdrawal = writeSuccess15d10Before regs1 global1 /\
    writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal =
      writeSuccess15d10Before regs2 global2 /\
    writeSuccessWithdrawalsOutputEntry
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
        withdrawal).1.(seq_regs)
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
        withdrawal).2 (sp + BV 64 1768)%bv =
      writeSuccess10190Before outputRegs outputGlobal /\
    writeSuccess156d8After
      (writeSuccess156d4Regs
        (writeSuccess156d0Regs
          (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
          (writeSuccessWithdrawalsAmountValue withdrawal))) outputGlobal =
      writeSuccess15d10Before finalRegs finalGlobal.
Proof.
  intros Hinv Hnext HnextLength Hrun.
  destruct (writeSuccessWithdrawalsIteration410Covered args sp pointer base total
    processed (S r) withdrawal allBytes prefix current
    (nextCurrent ++ nextSuffix) scratch encoderScratch registerFrame memoryFrame
    priorLog state segments after Hinv Hrun) as
    (regs0 & global0 & regs1 & global1 & regs2 & global2 &
     outputRegs & outputGlobal & finalRegs & finalGlobal & Hafter & Hprefix &
     Hentry1 & Hentry2 & Houtput & HfinalEntry & Hindex & Hvalidator &
     Haddress & Hamount).
  destruct (writeSuccessWithdrawalsNonfinalSemanticTransition args sp pointer
    base total processed r withdrawal nextWithdrawal allBytes prefix current
    nextCurrent nextSuffix scratch encoderScratch registerFrame memoryFrame
    priorLog state Hinv Hnext HnextLength) as
    (padding & nextPadding & Hpadding & Hcurrent & Hpointer & Hall &
     HprefixLength & Hdrop & HsuffixLength & HnextPadding & HnextCurrent & _).
  set (records :=
    writeSuccessWithdrawalsEncoderIntRecords global1 sp
      (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal) ++
    writeSuccessWithdrawalsEncoderIntRecords global2 sp
      (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal) ++
    writeSuccessWithdrawalsOutputRecordsExact outputGlobal
      (sp + BV 64 1768)%bv (BV 64 20) ++
    writeSuccessWithdrawalsEncoderIntRecords finalGlobal sp
      (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)).
  have Hrecords : writeSuccessWithdrawalIterationRecords sp withdrawal records.
  { eapply writeSuccessWithdrawalIterationRecordsCompose; eassumption. }
  have HafterLog : after.2 = priorLog ++ records.
  { rewrite Hafter. unfold records, writeSuccessWithdrawalsIteration410Log,
      writeSuccessWithdrawalsSecondEncoderLog. cbn beta iota zeta.
    rewrite !app_assoc. reflexivity. }
  exists records, padding, nextPadding, regs0, global0, regs1, global1, regs2,
    global2, outputRegs, outputGlobal, finalRegs, finalGlobal.
  split; first exact Hrun.
  split; first exact Hafter.
  split; first exact HafterLog.
  split; first exact Hrecords.
  repeat split; assumption.
Qed.

Lemma writeSuccessWithdrawalsLastIterationCovered args sp pointer base total
    processed withdrawal allBytes prefix current scratch encoderScratch
    registerFrame memoryFrame priorLog state segments after :
  Inv_15694 args sp pointer base total processed 1 withdrawal allBytes prefix
    current [] scratch encoderScratch registerFrame memoryFrame priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 410 state segments after ->
  exists records padding regs0 global0 regs1 global1 regs2
      global2 outputRegs outputGlobal finalRegs finalGlobal,
    WriteSuccessWithdrawalsRecordedRun 410 state segments after /\
    after =
      (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
         pointer 0 withdrawal,
       writeSuccessWithdrawalsIteration410Log priorLog global1 global2
         outputGlobal finalGlobal sp withdrawal) /\
    after.2 = priorLog ++ records /\
    writeSuccessWithdrawalIterationRecords sp withdrawal records /\
    length padding = 4%nat /\
    current = writeSuccessWithdrawalRawBytes withdrawal padding /\
    allBytes = prefix ++ current /\
    length (prefix ++ current) = (48 * total)%nat /\
    bv_unsigned (pointer + BV 64 48)%bv =
      base + 48 * Z.of_nat total /\
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs0 global0 /\
    writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer
      current withdrawal = writeSuccess15d10Before regs1 global1 /\
    writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal =
      writeSuccess15d10Before regs2 global2 /\
    writeSuccessWithdrawalsOutputEntry
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
        withdrawal).1.(seq_regs)
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
        withdrawal).2 (sp + BV 64 1768)%bv =
      writeSuccess10190Before outputRegs outputGlobal /\
    writeSuccess156d8After
      (writeSuccess156d4Regs
        (writeSuccess156d0Regs
          (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
          (writeSuccessWithdrawalsAmountValue withdrawal))) outputGlobal =
      writeSuccess15d10Before finalRegs finalGlobal.
Proof.
  intros Hinv Hrun.
  destruct (writeSuccessWithdrawalsIteration410Covered args sp pointer base total
    processed 0 withdrawal allBytes prefix current [] scratch encoderScratch
    registerFrame memoryFrame priorLog state segments after Hinv Hrun) as
    (regs0 & global0 & regs1 & global1 & regs2 & global2 &
     outputRegs & outputGlobal & finalRegs & finalGlobal & Hafter & Hprefix &
     Hentry1 & Hentry2 & Houtput & HfinalEntry & Hindex & Hvalidator &
     Haddress & Hamount).
  destruct (writeSuccessWithdrawalsLastSemanticTransition args sp pointer base
    total processed withdrawal allBytes prefix current scratch encoderScratch
    registerFrame memoryFrame priorLog state Hinv) as
    (padding & Hpadding & Hcurrent & Hall & Hlength & Hpointer).
  set (records :=
    writeSuccessWithdrawalsEncoderIntRecords global1 sp
      (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal) ++
    writeSuccessWithdrawalsEncoderIntRecords global2 sp
      (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal) ++
    writeSuccessWithdrawalsOutputRecordsExact outputGlobal
      (sp + BV 64 1768)%bv (BV 64 20) ++
    writeSuccessWithdrawalsEncoderIntRecords finalGlobal sp
      (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)).
  have Hrecords : writeSuccessWithdrawalIterationRecords sp withdrawal records.
  { eapply writeSuccessWithdrawalIterationRecordsCompose; eassumption. }
  have HafterLog : after.2 = priorLog ++ records.
  { rewrite Hafter. unfold records, writeSuccessWithdrawalsIteration410Log,
      writeSuccessWithdrawalsSecondEncoderLog. cbn beta iota zeta.
    rewrite !app_assoc. reflexivity. }
  exists records, padding, regs0, global0, regs1, global1, regs2, global2,
    outputRegs, outputGlobal, finalRegs, finalGlobal.
  split; first exact Hrun.
  split; first exact Hafter.
  split; first exact HafterLog.
  split; first exact Hrecords.
  repeat split; assumption.
Qed.

Print Assumptions writeSuccessWithdrawalsNonfinalIterationCovered.
Print Assumptions writeSuccessWithdrawalsLastIterationCovered.
