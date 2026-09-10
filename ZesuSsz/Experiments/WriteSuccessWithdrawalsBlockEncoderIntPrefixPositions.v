From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d1c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d20.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d24.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntPrefixCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMachinePositionEdges.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessEncoderIntPrefixPositionsExact
    (regs : reg_map) (global : seq_global_state)
    (value sp returnAddress : bv 64) scratch segments after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d10)) ->
  regs !! "x1" = Some (RVal_Bits returnAddress) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some (RVal_Bits value) ->
  read_mem_list global.(seq_mem) (bv_unsigned sp - 16) 16%N = Some scratch ->
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  bv_unsigned sp `mod` 8 = 0 ->
  0x20000000 <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 0x40000000 ->
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  IslaInstructionRun 7 (writeSuccess15d10Before regs global) segments after ->
  exists mstatusBits satp mstatusBits2 satp2 result14 result18 states,
    after = writeSuccess10190Before (writeSuccessEncoderIntRegs7 regs sp)
      (writeSuccessEncoderIntGlobal2 global sp returnAddress value) /\
    segments =
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
         (writeSuccessEncoderIntGlobal2 global sp returnAddress value)] /\
    length states = 8%nat /\
    nth_error states 0 = Some (writeSuccess15d10Before regs global) /\
    nth_error states 7 = Some after /\
    WriteSuccessWithdrawalsMachinePositionEdges segments states.
Proof.
  intros Hpc Hx1 Hx2 Hx10 Hscratch Hrange Halign Hlower Hupper Htable Hfacts Hrun.
  destruct (writeSuccessEncoderIntPrefixRunCovered regs global value sp
    returnAddress scratch segments after Hpc Hx1 Hx2 Hx10 Hscratch Hrange
    Halign Hlower Hupper Htable Hfacts Hrun) as
    (mstatusBits & satp & mstatusBits2 & satp2 & result14 & result18 &
     Hafter & Hsegments).
  destruct (writeSuccessWithdrawalsInstructionRunMachinePositionEdges 7
    (writeSuccess15d10Before regs global) segments after Hrun) as
    (states & Hlength & Hstart & Hend & Hedges).
  exists mstatusBits, satp, mstatusBits2, satp2, result14, result18, states.
  repeat split; assumption.
Qed.

Print Assumptions writeSuccessEncoderIntPrefixPositionsExact.
