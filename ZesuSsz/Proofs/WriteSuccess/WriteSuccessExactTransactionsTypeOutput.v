Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.
From Coq Require Import Lists.List.
From IslaTraces.write_success_34 Require Import instrs.
Local Existing Instance subsume_instr_pre_guard_inst | 0.

Definition transactionTypeOutputEntry `{!islaG Sigma} `{!threadG}
    (data old_ra old_x5 : bv 64) (kind : bv 8) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗
   "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x10" ↦ᵣ RVal_Bits data ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗ bv_unsigned data ↦ₘ∗ [kind] ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents data (BV 64 1) [kind] tail) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionTypeOutputEntry) := I.

Definition transactionTypeOutputPost `{!islaG Sigma} `{!threadG}
    (data : bv 64) (kind : bv 8) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x150f0) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗ "x10" ↦ᵣ RVal_Bits data ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗ bv_unsigned data ↦ₘ∗ [kind] ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionTypeOutputPost) := I.

Lemma transactions_type_output_correct `{!islaG Sigma} `{!threadG}
    data old_ra old_x5 kind tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_34.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 (writeOutputTraceSpec data (BV 64 1)
    (BV 64 0x150f0) [kind] tail P) -∗
  instr_body 0x150f0 (transactionTypeOutputPost data kind tail P) -∗
  instr_body 0x150e8 (transactionTypeOutputEntry data old_ra old_x5 kind tail P).
Proof. move => *. zesu_block. Qed.
Print Assumptions transactions_type_output_correct.
Lemma transactions_type_output_call_correct `{!islaG Sigma} `{!threadG}
    data oldra old5 kind tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_34.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x150e8
    (transactionTypeOutputEntry data oldra old5 kind tail P ∗
     instr_pre 0x150f0 (transactionTypeOutputPost data kind tail P) ∗ True).
Proof.
  iStartProof. iIntros "#Hcaller #Houtput".
  iAssert (□ instr_pre 0x10190
    (writeOutputTraceSpec data (BV 64 1) (BV 64 0x150f0) [kind] tail P))%I as "#Hcallee".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply write_output_trace_correct. iExact "Houtput". }
  iEval (rewrite /IslaTraces.write_success_34.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & _)". zesu_run.
  all: try (eexists; eexists; repeat split; reflexivity).
Qed.
Print Assumptions transactions_type_output_call_correct.
