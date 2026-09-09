From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessStoreOutcome.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputPhases.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRun.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10194.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessEncoderIntOutputExactRun
    (regs : reg_map) (global : seq_global_state)
    (data size returnAddress : bv 64) (bytes : list (bv 8))
    (priorLog : list WriteSuccessWithdrawalsRecord) (returnTrace : isla_trace) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10190)) ->
  regs !! "x1" = Some (RVal_Bits returnAddress) ->
  regs !! "x10" = Some (RVal_Bits data) ->
  regs !! "x11" = Some (RVal_Bits size) ->
  bv_extract 0 2 returnAddress = BV 2 0 ->
  global.(seq_instrs) !! returnAddress = Some returnTrace ->
  bv_unsigned size = Z.of_nat (length bytes) ->
  read_mem_list global.(seq_mem) (bv_unsigned data)
    (N.of_nat (length bytes)) = Some bytes ->
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  set_Forall (fun address =>
    ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom global.(seq_mem)) ->
  exists segments records,
    IslaInstructionRun 5 (writeSuccess10190Before regs global) segments
      (writeSuccess101a0After (writeSuccessOutputRegs4 regs) global
        returnAddress) /\
    writeSuccessOutputRecords data size bytes records.
Proof.
  intros Hpc Hx1 Hx10 Hx11 Halign Hreturn Hsize Hread Htable Hfacts Hdom.
  destruct (writeSuccessOutputPhases regs global data size returnAddress
    Hpc Hx1 Hx10 Hx11 Halign Htable Hfacts Hdom) as
    (mstatusBits & satp & Hseg90 & Hseg94 & Hseg98 & Hseg9c & Hsega0).
  destruct (writeSuccessOutputRecordedComposition regs global data size
    returnAddress bytes priorLog returnTrace Hpc Hx1 Hx10 Hx11 Halign Hreturn
    Hsize Hread Htable Hfacts Hdom) as
    (otherSegments & finalMachine & records & Hrecorded & HfinalPc & Hrecords).
  exists [writeSuccess10190Observations regs global;
    writeSuccess10194Observations (writeSuccessOutputRegs1 regs) global
      writeSuccess10190Link;
    writeSuccess10198Observations (writeSuccessOutputRegs2 regs) global
      mstatusBits writeSuccessOutputPortBase satp data false
      WriteSuccessStoreMmio;
    writeSuccess1019cObservations (writeSuccessOutputRegs3 regs) global
      mstatusBits writeSuccessOutputPortBase satp size false
      WriteSuccessStoreMmio;
    writeSuccess101a0Observations (writeSuccessOutputRegs4 regs) global
      returnAddress], records.
  split; last exact Hrecords.
  econstructor; [exact Hseg90|].
  econstructor; [exact Hseg94|].
  econstructor; [exact Hseg98|].
  econstructor; [exact Hseg9c|].
  econstructor; [exact Hsega0|]. constructor.
Qed.

Print Assumptions writeSuccessEncoderIntOutputExactRun.
