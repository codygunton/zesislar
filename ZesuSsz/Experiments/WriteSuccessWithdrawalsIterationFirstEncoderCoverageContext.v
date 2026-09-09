From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationMemcpyCoverageJoin.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedRunSplit.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Lemma writeSuccessWithdrawalsIterationThroughFirstEncoderCoveredContext args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state
    segments after :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 362 state segments after ->
  exists regs0 global0 regs global,
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs0 global0 /\
    writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
      withdrawal = writeSuccess15d10Before regs global /\
    after =
      (writeSuccessWithdrawalsEncoderIntEndpoint regs global sp
         (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal),
       priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
         (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)).
Proof.
  intros Hinv Hrun.
  have Hrun5_357 : WriteSuccessWithdrawalsRecordedRun (5 + 357) state
      segments after by exact Hrun.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 5 357 state segments after
    Hrun5_357) as (g0 & state5 & tail357 & Hsegments0 & H0 & H357).
  rewrite (writeSuccessWithdrawalsPrefix15694RecordedCovered args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state g0 state5
    Hinv H0) in H357.
  have Hrun339_18 : WriteSuccessWithdrawalsRecordedRun (339 + 18)
      (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog)
      tail357 after by exact H357.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 339 18 _ tail357 after
    Hrun339_18) as (g1 & state344 & tail18 & Hsegments1 & H1 & H18).
  destruct (writeSuccessWithdrawalsIterationMemcpyRecordedCoveredJoin args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state g1
    state344 Hinv H1) as (regs0 & global0 & HprefixEntry & Hstate344).
  rewrite Hstate344 in H18.
  have Hrun3_15 : WriteSuccessWithdrawalsRecordedRun (3 + 15)
      (writeSuccessWithdrawals156a8State regs0 global0 sp pointer current,
       priorLog) tail18 after by exact H18.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 3 15 _ tail18 after
    Hrun3_15) as (g2 & state347 & g3 & Hsegments2 & H2 & H3).
  rewrite (writeSuccessWithdrawals156a8EncoderIntCovered args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 g2
    state347 Hinv HprefixEntry H2) in H3.
  have HencoderInv := writeSuccessWithdrawals156a8EncoderIntInv args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 Hinv HprefixEntry.
  destruct (block_encoder_int_recorded_covered_exact
    (writeSuccessWithdrawalsIndexValue withdrawal) sp (Z_to_bv 64 0x156b4)
    encoderScratch
    (writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer
      current withdrawal).2.(seq_mem)
    priorLog
    (writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer
      current withdrawal, priorLog) g3 after HencoderInv H3) as
    (regs & global & HencoderEntry & Hafter).
  exists regs0, global0, regs, global.
  repeat split; assumption.
Qed.

Print Assumptions
  writeSuccessWithdrawalsIterationThroughFirstEncoderCoveredContext.
