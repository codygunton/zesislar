From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffixPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSilent.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d30.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34.

Import ListNotations.
Open Scope Z_scope.

Theorem writeSuccessEncoderIntSuffixRecordedPositionPath
    (regs : reg_map) (global : seq_global_state)
    (sp returnAddress : bv 64) (returnTrace : isla_trace)
    priorLog segments after :
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
  global.(seq_instrs) !! returnAddress = Some returnTrace ->
  writeSuccessWithdrawalsInstructionTable global ->
  WriteSuccessWithdrawalsRecordedRun 3
    (writeSuccess15d2cBefore (writeSuccessEncoderIntAfterOutputRegs regs) global,
      priorLog) segments after ->
  exists mstatusBits satp states,
    after =
      (writeSuccess15d34After
        (writeSuccess15d30Regs
          (writeSuccess15d2cRegs (writeSuccessEncoderIntAfterOutputRegs regs)
            returnAddress) (sp - BV 64 16)%bv) global returnAddress, priorLog) /\
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
      (writeSuccess15d2cBefore (writeSuccessEncoderIntAfterOutputRegs regs) global,
        priorLog) /\
    nth_error states 3 = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states.
Proof.
  intros Hx2 Hx1 Hfacts Hread Hrange Halign Hlower Hupper HreturnAlign Hreturn
    Htable Hrecorded.
  destruct Hrecorded as (Hrun & HafterLog).
  have Hrecorded : WriteSuccessWithdrawalsRecordedRun 3
      (writeSuccess15d2cBefore (writeSuccessEncoderIntAfterOutputRegs regs) global,
        priorLog) segments after by (split; assumption).
  destruct (writeSuccessEncoderIntSuffixPositionsExact regs global sp
    returnAddress segments after.1 Hx2 Hx1 Hfacts Hread Hrange Halign Hlower
    Hupper HreturnAlign Htable Hrun) as
    (mstatusBits & satp & machineStates & Hmachine & Hsegments & _).
  destruct (writeSuccessWithdrawalsRecordedRunPositionEdges 3
    (writeSuccess15d2cBefore (writeSuccessEncoderIntAfterOutputRegs regs) global,
      priorLog) segments after Hrecorded) as
    (states & Hlength & Hstart & Hend & Hedges).
  exists mstatusBits, satp, states.
  split.
  - destruct after as [afterMachine afterLog]. cbn in Hmachine, HafterLog |- *.
    subst afterMachine. rewrite HafterLog Hsegments.
    rewrite (writeSuccessEncoderIntSuffixRecords regs global sp returnAddress
      mstatusBits satp returnTrace HreturnAlign Hreturn).
    rewrite app_nil_r. reflexivity.
  - split; first exact Hsegments. repeat split; assumption.
Qed.

Print Assumptions writeSuccessEncoderIntSuffixRecordedPositionPath.
