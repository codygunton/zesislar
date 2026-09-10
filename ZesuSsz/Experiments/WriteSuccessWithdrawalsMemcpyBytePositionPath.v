From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyBytePositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyByteRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyInduction.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.

Import ListNotations.

Definition writeSuccessMemcpyBytePositionStates (regs : reg_map)
    (global : seq_global_state) (source destination index length : bv 64)
    (byte : bv 8) (priorLog : list WriteSuccessWithdrawalsRecord) :
    list WriteSuccessWithdrawalsConcreteState :=
  [(writeSuccess101d8Before regs global, priorLog);
   (writeSuccessMemcpyByteState1 regs global, priorLog);
   (writeSuccessMemcpyByteState2 regs global source index, priorLog);
   (writeSuccessMemcpyByteState3 regs global source index byte, priorLog);
   (writeSuccessMemcpyByteState4 regs global source destination index byte,
    priorLog);
   (writeSuccessMemcpyByteState5 regs global source destination index byte,
    priorLog);
   (writeSuccessMemcpyByteState6 regs global source destination index byte,
    priorLog);
   (writeSuccessMemcpyByteAfter regs global source destination index byte,
    priorLog)].

Theorem writeSuccessMemcpyBytePositionPath regs global
    (source destination index length : bv 64) (byte : bv 8)
    priorLog segments after :
  writeSuccessMemcpyByteReady regs global source destination index length byte ->
  IslaInstructionRun 7 (writeSuccess101d8Before regs global) segments after ->
  after = writeSuccessMemcpyByteAfter regs global source destination index byte /\
  WriteSuccessWithdrawalsPositionEdges segments
    (writeSuccessMemcpyBytePositionStates regs global source destination index
      length byte priorLog).
Proof.
  intros Hready Hrun.
  unfold writeSuccessMemcpyByteReady in Hready.
  destruct Hready as
    (Hpc & Hx10 & Hx11 & Hx12 & Hx15 & Hne & Htable & Hfacts & Hread &
     HsourceLower & HsourceUpper & HdestinationLower & HdestinationUpper &
     Hbacked).
  destruct (writeSuccessMemcpyBytePositionsExact regs global source destination
    index length byte priorLog segments after Hpc Hx10 Hx11 Hx12 Hx15 Hne
    Htable Hfacts Hread HsourceLower HsourceUpper HdestinationLower
    HdestinationUpper Hbacked Hrun) as
    (observations0 & observations1 & observations2 & observations3 &
     observations4 & observations5 & observations6 & Hsegments & Hafter &
     Hrecords & Hedge0 & Hedge1 & Hedge2 & Hedge3 & Hedge4 & Hedge5 & Hedge6).
  subst segments after.
  split; first reflexivity.
  unfold writeSuccessMemcpyBytePositionStates.
  cbn [WriteSuccessWithdrawalsPositionEdges].
  split; first exact Hedge0.
  split; first exact Hedge1.
  split; first exact Hedge2.
  split; first exact Hedge3.
  split; first exact Hedge4.
  split; first exact Hedge5.
  split; first exact Hedge6.
  exact I.
Qed.

Print Assumptions writeSuccessMemcpyBytePositionPath.
