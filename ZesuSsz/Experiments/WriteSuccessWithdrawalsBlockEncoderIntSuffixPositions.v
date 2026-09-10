From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d30.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffixCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMachinePositionEdges.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessEncoderIntSuffixPositionsExact
    (regs : reg_map) (global : seq_global_state)
    (sp returnAddress : bv 64) segments after :
  regs !! "x2" = Some (RVal_Bits (sp - BV 64 16)%bv) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess15d28Link) ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  read_mem global.(seq_mem) (bv_unsigned sp - 8) 8%N =
    Some (bv_to_bvn returnAddress) ->
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  bv_unsigned sp `mod` 8 = 0 ->
  0x20000000 <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 0x40000000 ->
  bv_extract 0 2 returnAddress = BV 2 0 ->
  writeSuccessWithdrawalsInstructionTable global ->
  IslaInstructionRun 3
    (writeSuccess15d2cBefore (writeSuccessEncoderIntAfterOutputRegs regs) global)
    segments after ->
  exists mstatusBits satp states,
    after = writeSuccess15d34After
      (writeSuccess15d30Regs
        (writeSuccess15d2cRegs (writeSuccessEncoderIntAfterOutputRegs regs)
          returnAddress) (sp - BV 64 16)%bv) global returnAddress /\
    segments =
      [writeSuccess15d2cObservations
        (writeSuccessEncoderIntAfterOutputRegs regs) global mstatusBits
        (sp - BV 64 16)%bv satp returnAddress;
       writeSuccess15d30Observations
        (writeSuccess15d2cRegs (writeSuccessEncoderIntAfterOutputRegs regs)
          returnAddress) global (sp - BV 64 16)%bv;
       writeSuccess15d34Observations
        (writeSuccess15d30Regs
          (writeSuccess15d2cRegs (writeSuccessEncoderIntAfterOutputRegs regs)
            returnAddress) (sp - BV 64 16)%bv) global returnAddress] /\
    length states = 4%nat /\
    nth_error states 0 = Some
      (writeSuccess15d2cBefore (writeSuccessEncoderIntAfterOutputRegs regs) global) /\
    nth_error states 3 = Some after /\
    WriteSuccessWithdrawalsMachinePositionEdges segments states.
Proof.
  intros Hx2 Hx1 Hfacts Hread Hrange Halign Hlower Hupper HreturnAlign Htable Hrun.
  destruct (writeSuccessEncoderIntSuffixRunCovered regs global sp returnAddress
    segments after Hx2 Hx1 Hfacts Hread Hrange Halign Hlower Hupper HreturnAlign
    Htable Hrun) as (mstatusBits & satp & Hafter & Hsegments).
  destruct (writeSuccessWithdrawalsInstructionRunMachinePositionEdges 3
    (writeSuccess15d2cBefore (writeSuccessEncoderIntAfterOutputRegs regs) global)
    segments after Hrun) as (states & Hlength & Hstart & Hend & Hedges).
  exists mstatusBits, satp, states.
  repeat split; assumption.
Qed.

Print Assumptions writeSuccessEncoderIntSuffixPositionsExact.
