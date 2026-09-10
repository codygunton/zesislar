From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessStoreOutcome.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10194.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.
Open Scope Z_scope.

Theorem writeSuccessOutputRecordedPositionPath
    (regs : reg_map) (global : seq_global_state)
    (data size returnAddress : bv 64) (returnTrace : isla_trace)
    priorLog segments after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10190)) ->
  regs !! "x1" = Some (RVal_Bits returnAddress) ->
  regs !! "x10" = Some (RVal_Bits data) ->
  regs !! "x11" = Some (RVal_Bits size) ->
  bv_extract 0 2 returnAddress = BV 2 0 ->
  global.(seq_instrs) !! returnAddress = Some returnTrace ->
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  set_Forall (fun address =>
    ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom global.(seq_mem)) ->
  WriteSuccessWithdrawalsRecordedRun 5
    (writeSuccess10190Before regs global, priorLog) segments after ->
  exists mstatusBits satp result98 result9c states,
    segments =
      [writeSuccess10190Observations regs global;
       writeSuccess10194Observations (writeSuccessOutputRegs1 regs) global
         writeSuccess10190Link;
       writeSuccess10198Observations (writeSuccessOutputRegs2 regs) global
         mstatusBits writeSuccessOutputPortBase satp data result98
         WriteSuccessStoreMmio;
       writeSuccess1019cObservations (writeSuccessOutputRegs3 regs) global
         mstatusBits writeSuccessOutputPortBase satp size result9c
         WriteSuccessStoreMmio;
       writeSuccess101a0Observations (writeSuccessOutputRegs4 regs) global
         returnAddress] /\
    after =
      (writeSuccess101a0After (writeSuccessOutputRegs4 regs) global
         returnAddress,
       priorLog ++
         [(SWriteMem (BV 64 0x2401a0c0) (bv_to_bvn data), global.(seq_mem));
          (SWriteMem (BV 64 0x2401a0c8) (bv_to_bvn size), global.(seq_mem))]) /\
    length states = 6%nat /\
    nth_error states 0 =
      Some (writeSuccess10190Before regs global, priorLog) /\
    nth_error states 5 = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states.
Proof.
  intros Hpc Hx1 Hx10 Hx11 Halign Hreturn Htable Hfacts Hdom Hrecorded.
  destruct Hrecorded as (Hrun & HafterLog).
  have Hrecorded : WriteSuccessWithdrawalsRecordedRun 5
      (writeSuccess10190Before regs global, priorLog) segments after by
    (split; assumption).
  destruct (writeSuccessOutputRunExact regs global data size returnAddress
    returnTrace segments after.1 Hpc Hx1 Hx10 Hx11 Halign Hreturn Htable
    Hfacts Hdom Hrun) as
    (mstatusBits & satp & result98 & result9c & Hsegments & Hmachine & Hrecords).
  destruct (writeSuccessWithdrawalsRecordedRunPositionEdges 5
    (writeSuccess10190Before regs global, priorLog) segments after Hrecorded) as
    (states & Hlength & Hstart & Hend & Hedges).
  exists mstatusBits, satp, result98, result9c, states.
  split; first exact Hsegments.
  split.
  - destruct after as [afterMachine afterLog]. cbn in Hmachine, HafterLog |- *.
    subst afterMachine. rewrite HafterLog Hrecords. reflexivity.
  - repeat split; assumption.
Qed.

Print Assumptions writeSuccessOutputRecordedPositionPath.
