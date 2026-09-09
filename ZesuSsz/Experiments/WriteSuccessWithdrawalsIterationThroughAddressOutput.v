From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRecorded.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputCoverageContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInvContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputRecordedContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationSecondEncoder.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationSecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedRunSplit.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Lemma writeSuccessWithdrawalsIterationThroughAddressOutput args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  exists segments regs0 global0 regs1 global1 regs2 global2 outputRegs outputGlobal,
    WriteSuccessWithdrawalsRecordedRun 389 state segments
      (writeSuccess101a0After (writeSuccessOutputRegs4 outputRegs) outputGlobal (Z_to_bv 64 0x156d0),
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal ++
       writeSuccessWithdrawalsOutputRecordsExact outputGlobal (sp + BV 64 1768)%bv (BV 64 20)) /\
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer = writeSuccess101d4Before regs0 global0 /\
    writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current withdrawal = writeSuccess15d10Before regs1 global1 /\
    writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal = writeSuccess15d10Before regs2 global2 /\
    writeSuccessWithdrawalsOutputEntry
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs)
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).2
      (sp + BV 64 1768)%bv = writeSuccess10190Before outputRegs outputGlobal /\
    writeSuccessOutputRecords (sp + BV 64 1768)%bv (BV 64 20)
      (writeSuccessWithdrawalAddressBytes withdrawal)
      (writeSuccessWithdrawalsOutputRecordsExact outputGlobal (sp + BV 64 1768)%bv (BV 64 20)).
Proof.
  intros Hinv.
  destruct (writeSuccessWithdrawalsIterationThroughSecondEncoder args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state Hinv) as (g0 & regs0 & global0 & regs1 & global1 & regs2 & global2 & H0 & Hprefix & Hentry1 & Hentry2).
  destruct (writeSuccessWithdrawals156c0OutputRecorded args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2) as (g1 & H1).
  have HoutInv := writeSuccessWithdrawals156c0OutputInv args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2.
  destruct (block_write_output_recorded (sp + BV 64 1768)%bv (BV 64 20) (Z_to_bv 64 0x156d0) (writeSuccessWithdrawalAddressBytes withdrawal) (writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal) _ HoutInv) as (g2 & outputRegs & outputGlobal & H2 & HoutputEntry & Hrecords).
  have H01 : WriteSuccessWithdrawalsRecordedRun 384 state (g0 ++ g1)
      (writeSuccessWithdrawalsOutputEntry
        (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs)
        (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).2
        (sp + BV 64 1768)%bv,
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal).
  { replace 384%nat with (380 + 4)%nat by reflexivity. eapply writeSuccessWithdrawalsRecordedRunApp; eassumption. }
  have H012 : WriteSuccessWithdrawalsRecordedRun 389 state ((g0 ++ g1) ++ g2)
      (writeSuccess101a0After (writeSuccessOutputRegs4 outputRegs) outputGlobal (Z_to_bv 64 0x156d0),
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal ++ writeSuccessWithdrawalsOutputRecordsExact outputGlobal (sp + BV 64 1768)%bv (BV 64 20)).
  { replace 389%nat with (384 + 5)%nat by reflexivity. eapply writeSuccessWithdrawalsRecordedRunApp; eassumption. }
  exists ((g0 ++ g1) ++ g2), regs0, global0, regs1, global1, regs2, global2, outputRegs, outputGlobal.
  split; first exact H012. split; first exact Hprefix.
  split; first exact Hentry1. split; first exact Hentry2.
  split; first exact HoutputEntry. exact Hrecords.
Qed.

Lemma writeSuccessWithdrawalsIterationThroughAddressOutputCovered args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state segments after :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 389 state segments after ->
  exists regs0 global0 regs1 global1 regs2 global2 outputRegs outputGlobal,
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer = writeSuccess101d4Before regs0 global0 /\
    writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current withdrawal = writeSuccess15d10Before regs1 global1 /\
    writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal = writeSuccess15d10Before regs2 global2 /\
    writeSuccessWithdrawalsOutputEntry
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs)
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).2
      (sp + BV 64 1768)%bv = writeSuccess10190Before outputRegs outputGlobal /\
    after =
      (writeSuccess101a0After (writeSuccessOutputRegs4 outputRegs) outputGlobal (Z_to_bv 64 0x156d0),
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal ++
       writeSuccessWithdrawalsOutputRecordsExact outputGlobal (sp + BV 64 1768)%bv (BV 64 20)) /\
    writeSuccessOutputRecords (sp + BV 64 1768)%bv (BV 64 20)
      (writeSuccessWithdrawalAddressBytes withdrawal)
      (writeSuccessWithdrawalsOutputRecordsExact outputGlobal (sp + BV 64 1768)%bv (BV 64 20)).
Proof.
  intros Hinv Hrun.
  have Hrun380_9 : WriteSuccessWithdrawalsRecordedRun (380 + 9) state segments after by exact Hrun.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 380 9 state segments after Hrun380_9) as (g0 & state380 & tail9 & Hsegments0 & H0 & H9).
  destruct (writeSuccessWithdrawalsIterationThroughSecondEncoderCoveredContext args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state g0 state380 Hinv H0) as (regs0 & global0 & regs1 & global1 & regs2 & global2 & Hprefix & Hentry1 & Hentry2 & Hstate380).
  rewrite Hstate380 in H9.
  have Hrun4_5 : WriteSuccessWithdrawalsRecordedRun (4 + 5)
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal,
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal)
      tail9 after by exact H9.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 4 5
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal,
     writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal)
    tail9 after Hrun4_5) as (g1 & state384 & g2 & Hsegments1 & H1 & H2).
  rewrite (writeSuccessWithdrawals156c0OutputCovered args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 g1 state384 Hinv Hprefix Hentry1 Hentry2 H1) in H2.
  have HoutInv := writeSuccessWithdrawals156c0OutputInv args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2.
  destruct (block_write_output_recorded_covered_exact (sp + BV 64 1768)%bv (BV 64 20) (Z_to_bv 64 0x156d0) (writeSuccessWithdrawalAddressBytes withdrawal) (writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal) _ g2 after HoutInv H2) as (outputRegs & outputGlobal & HoutputEntry & Hafter & Hrecords).
  exists regs0, global0, regs1, global1, regs2, global2, outputRegs, outputGlobal.
  split; first exact Hprefix. split; first exact Hentry1.
  split; first exact Hentry2. split; first exact HoutputEntry.
  split; first exact Hafter. exact Hrecords.
Qed.

Print Assumptions writeSuccessWithdrawalsIterationThroughAddressOutput.
Print Assumptions writeSuccessWithdrawalsIterationThroughAddressOutputCovered.
