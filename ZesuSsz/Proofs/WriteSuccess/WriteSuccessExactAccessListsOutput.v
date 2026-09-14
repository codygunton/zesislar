Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArraySlices.
Import SliceMatching.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.
From Coq Require Import Lists.List ZArith.ZArith.
From IslaTraces.write_success_55 Require Import instrs.
Local Existing Instance subsume_instr_pre_guard_inst | 0.

Definition accessListsOutputFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗
   bv_unsigned (sp + BV 64 1744)%bv ↦ₘ∗ take 16 bytes ∗
   (bv_unsigned (sp + BV 64 1744)%bv + 36) ↦ₘ∗ drop 36 bytes ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsOutputFrame) := I.

Definition accessListsOutputEntry `{!islaG Sigma} `{!threadG}
    (sp old_ra old5 old_data old_size : bv 64) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits old_ra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x10" ↦ᵣ RVal_Bits old_data ∗ "x11" ↦ᵣ RVal_Bits old_size ∗
   bv_unsigned (sp + BV 64 1744)%bv ↦ₘ∗ bytes ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp + BV 64 1760)%bv (BV 64 20)
     (take 20 (drop 16 bytes)) tail) ∗ ⌜length bytes = 40%nat⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1784 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsOutputEntry) := I.

Definition accessListsOutputPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15210) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1760)%bv ∗ "x11" ↦ᵣ RVal_Bits (BV 64 20) ∗
   bv_unsigned (sp + BV 64 1760)%bv ↦ₘ∗ take 20 (drop 16 bytes) ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
   accessListsOutputFrame sp bytes P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsOutputPost) := I.

Lemma access_lists_output_correct `{!islaG Sigma} `{!threadG}
    sp old_ra old5 old_data old_size bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_55.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 (writeOutputTraceSpec (sp + BV 64 1760)%bv (BV 64 20)
    (BV 64 0x15210) (take 20 (drop 16 bytes)) tail (accessListsOutputFrame sp bytes P)) -∗
  instr_body 0x15210 (accessListsOutputPost sp bytes tail P) -∗
  instr_body 0x15200 (accessListsOutputEntry sp old_ra old5 old_data old_size bytes tail P).
Proof.
  zesu_block.
  all: try (eexists; eexists; repeat split; reflexivity).
  all: try (unfold accessListsOutputPost; reflexivity).
  all: rewrite length_take length_drop; rewrite H0; reflexivity.
Qed.
Print Assumptions access_lists_output_correct.
