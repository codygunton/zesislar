From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d1c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d20.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d24.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d30.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessEncoderIntPrefixRecordsEmpty regs global value sp returnAddress
    mstatusBits satp mstatusBits2 satp2 result14 result18 :
  segmentRecords (writeSuccess15d10Before regs global)
    (flattenMicroObservations
      [writeSuccess15d10Observations regs global sp;
       writeSuccess15d14Observations (writeSuccessEncoderIntRegs1 regs sp) global
         mstatusBits (sp - BV 64 16)%bv satp returnAddress result14;
       writeSuccess15d18Observations (writeSuccessEncoderIntRegs2 regs sp)
         (writeSuccessEncoderIntGlobal1 global sp returnAddress) mstatusBits2
         (sp - BV 64 16)%bv satp2 value result18;
       writeSuccess15d1cObservations (writeSuccessEncoderIntRegs3 regs sp)
         (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
         (sp - BV 64 16)%bv;
       writeSuccess15d20Observations (writeSuccessEncoderIntRegs4 regs sp)
         (writeSuccessEncoderIntGlobal2 global sp returnAddress value);
       writeSuccess15d24Observations (writeSuccessEncoderIntRegs5 regs sp)
         (writeSuccessEncoderIntGlobal2 global sp returnAddress value);
       writeSuccess15d28Observations (writeSuccessEncoderIntRegs6 regs sp)
         (writeSuccessEncoderIntGlobal2 global sp returnAddress value)]) = [].
Proof. reflexivity. Qed.

Lemma writeSuccessEncoderIntSuffixRecords regs global sp returnAddress
    mstatusBits satp returnTrace :
  bv_extract 0 2 returnAddress = BV 2 0 ->
  global.(seq_instrs) !! returnAddress = Some returnTrace ->
  segmentRecords
    (writeSuccess15d2cBefore (writeSuccessEncoderIntAfterOutputRegs regs) global)
    (flattenMicroObservations
      [writeSuccess15d2cObservations
        (writeSuccessEncoderIntAfterOutputRegs regs) global mstatusBits
        (sp - BV 64 16)%bv satp returnAddress;
       writeSuccess15d30Observations
        (writeSuccess15d2cRegs (writeSuccessEncoderIntAfterOutputRegs regs)
          returnAddress) global (sp - BV 64 16)%bv;
       writeSuccess15d34Observations
        (writeSuccess15d30Regs
          (writeSuccess15d2cRegs (writeSuccessEncoderIntAfterOutputRegs regs)
          returnAddress) (sp - BV 64 16)%bv) global returnAddress]) =
  [].
Proof.
  intros Halign Hreturn.
  have Htarget := writeSuccessEncoderInt15d34TargetExact returnAddress Halign.
  unfold segmentRecords, flattenMicroObservations,
    writeSuccess15d2cObservations, writeSuccess15d2cPrefixObservations,
    writeSuccess15d30Observations, writeSuccess15d34Observations,
    writeSuccess15d34PrefixObservations, writeSuccess15d34DoneLabels.
  rewrite Htarget Hreturn. reflexivity.
Qed.

Print Assumptions writeSuccessEncoderIntPrefixRecordsEmpty.
Print Assumptions writeSuccessEncoderIntSuffixRecords.
