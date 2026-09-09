From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationFirstEncoderCoverageContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedRunSplit.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Lemma writeSuccessWithdrawalsIterationThroughSecondEncoderCoveredContext args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state
    segments after :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 380 state segments after ->
  exists regs0 global0 regs1 global1 regs2 global2,
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs0 global0 /\
    writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
      withdrawal = writeSuccess15d10Before regs1 global1 /\
    writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal =
      writeSuccess15d10Before regs2 global2 /\
    after =
      (writeSuccessWithdrawalsEncoderIntEndpoint regs2 global2 sp
         (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal),
       (priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global1 sp
          (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)) ++
       writeSuccessWithdrawalsEncoderIntRecords global2 sp
         (Z_to_bv 64 0x156c0)
         (writeSuccessWithdrawalsValidatorValue withdrawal)).
Proof.
  intros Hinv Hrun.
  have Hrun362_18 : WriteSuccessWithdrawalsRecordedRun (362 + 18) state
      segments after by exact Hrun.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 362 18 state segments after
    Hrun362_18) as (g0 & state362 & tail18 & Hsegments0 & H0 & H18).
  destruct (writeSuccessWithdrawalsIterationThroughFirstEncoderCoveredContext
    args sp pointer base total processed remaining withdrawal allBytes prefix
    current suffix scratch encoderScratch registerFrame memoryFrame priorLog
    state g0 state362 Hinv H0) as
    (regs0 & global0 & regs1 & global1 & Hprefix & HfirstEntry & Hstate362).
  rewrite Hstate362 in H18.
  have Hrun3_15 : WriteSuccessWithdrawalsRecordedRun (3 + 15)
      (writeSuccessWithdrawalsEncoderIntEndpoint regs1 global1 sp
         (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal),
       priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global1 sp
         (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal))
      tail18 after by exact H18.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 3 15 _ tail18 after
    Hrun3_15) as (g1 & state365 & g2 & Hsegments1 & H1 & H2).
  rewrite (writeSuccessWithdrawals156b4SecondEncoderCovered args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 g1 state365 Hinv Hprefix HfirstEntry H1) in H2.
  have HsecondInv := writeSuccessWithdrawals156b4SecondEncoderInv args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 Hinv Hprefix HfirstEntry.
  set (firstLog := priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global1
    sp (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)).
  destruct (block_encoder_int_recorded_covered_exact
    (writeSuccessWithdrawalsValidatorValue withdrawal) sp
    (Z_to_bv 64 0x156c0)
    (writeSuccessWithdrawalsFirstEncoderScratch sp withdrawal)
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs1 global1 sp withdrawal).2.(seq_mem)
    firstLog
    (writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal,
     firstLog) g2 after HsecondInv H2) as
    (regs2 & global2 & HsecondEntry & Hafter).
  exists regs0, global0, regs1, global1, regs2, global2.
  unfold firstLog in HsecondEntry, Hafter.
  repeat split; assumption.
Qed.

Print Assumptions
  writeSuccessWithdrawalsIterationThroughSecondEncoderCoveredContext.
