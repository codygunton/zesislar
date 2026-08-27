Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.OperationalBridge.
From IslaTraces.allocator_get Require Import instrs.

Definition allocatorInstrMap : gmap (bv 64) isla_trace :=
  <[Z_to_bv 64 0x14ce8 := a14ce8]>
  (<[Z_to_bv 64 0x14ce4 := a14ce4]>
  (<[Z_to_bv 64 0x14ce0 := a14ce0]>
  (<[Z_to_bv 64 0x14cdc := a14cdc]>
  (<[Z_to_bv 64 0x14cd8 := a14cd8]>
  (<[Z_to_bv 64 0x14cd4 := a14cd4]>
  (<[Z_to_bv 64 0x14cd0 := a14cd0]>
  (<[Z_to_bv 64 0x14ccc := a14ccc]> ∅))))))).

Definition allocatorAuipcInitialRegs (x10 x11 : bv 64) : reg_map :=
  <["mstatus" := RegVal_Struct [("bits", RVal_Bits (Z_to_bv 64 0))]]>
  (<["misa" := RegVal_Struct [("bits", RVal_Bits
      (Z_to_bv 64 0x8000000000001100))]]>
  (<["x11" := RVal_Bits x11]>
  (<["x10" := RVal_Bits x10]>
  (<["PC" := RVal_Bits (Z_to_bv 64 0x14ccc)]> ∅)))).

Definition allocatorSetPc (pc : Z) (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits (Z_to_bv 64 pc)]> regs.

Definition allocatorR1 regs : reg_map :=
  allocatorSetPc 0x14cd0
    (<["x10" := RVal_Bits (Z_to_bv 64 0x24019ccc)]> regs).
Definition allocatorR2 regs : reg_map :=
  allocatorSetPc 0x14cd4
    (<["x11" := RVal_Bits (Z_to_bv 64 0x17cd0)]> regs).
Definition allocatorR3 stack8 regs : reg_map :=
  allocatorSetPc 0x14cd8 (<["x13" := RVal_Bits stack8]> regs).
Definition allocatorR4 stack0 regs : reg_map :=
  allocatorSetPc 0x14cdc (<["x12" := RVal_Bits stack0]> regs).
Definition allocatorR5 regs : reg_map :=
  allocatorSetPc 0x14ce0
    (<["x10" := RVal_Bits (Z_to_bv 64 0x2401a0b0)]> regs).
Definition allocatorR6 regs : reg_map :=
  allocatorSetPc 0x14ce4
    (<["x11" := RVal_Bits (Z_to_bv 64 0x177a8)]> regs).
Definition allocatorR7 regs : reg_map := allocatorSetPc 0x14ce8 regs.
Definition allocatorR8 regs : reg_map := allocatorSetPc 0x14cec regs.

Definition allocatorState := operationalState allocatorInstrMap.

Ltac finish_allocator_trace :=
  repeat operational_trace_step;
  try apply readAccessorZToBv;
  try bv_solve;
  try constructor.

Lemma allocatorAuipc10Step x10 x11 mem :
  operationalInstructionStep 0
    (allocatorState (allocatorAuipcInitialRegs x10 x11) mem)
    (allocatorState
      (allocatorR1 (allocatorAuipcInitialRegs x10 x11)) mem).
Proof.
  operational_begin_instruction (Z_to_bv 64 0x14ccc) a14ccc.
  finish_allocator_trace.
  Unshelve. all: first [exact (Z_to_bv 64 0) | exact false].
Qed.

Lemma allocatorAuipc11Step x10 x11 mem :
  operationalInstructionStep 1
    (allocatorState
      (allocatorR1 (allocatorAuipcInitialRegs x10 x11)) mem)
    (allocatorState
      (allocatorR2 (allocatorR1
        (allocatorAuipcInitialRegs x10 x11))) mem).
Proof.
  operational_begin_instruction (Z_to_bv 64 0x14cd0) a14cd0.
  finish_allocator_trace.
  Unshelve. all: first [exact (Z_to_bv 64 0) | exact false].
Qed.
