Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.
From Coq Require Import Lists.List.
From IslaTraces.write_success_61 Require Import instrs.
Local Existing Instance subsume_instr_pre_guard_inst | 0.

Definition storageKeysOutputEntry `{!islaG Sigma} `{!threadG}
    (sp old_ra old_x5 old_data old_size : bv 64) (payload : list (bv 8)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗
   "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x10" ↦ᵣ RVal_Bits old_data ∗
   "x11" ↦ᵣ RVal_Bits old_size ∗ bv_unsigned (sp + BV 64 1712)%bv ↦ₘ∗ payload ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp + BV 64 1712)%bv (BV 64 32) payload tail) ∗ ⌜length payload = 32%nat⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysOutputEntry) := I.

Definition storageKeysOutputPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (payload : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x153a8) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗ "x10" ↦ᵣ RVal_Bits (sp + BV 64 1712)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 32) ∗ bv_unsigned (sp + BV 64 1712)%bv ↦ₘ∗ payload ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
   ("x2" ↦ᵣ RVal_Bits sp ∗ P ∗ True) ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysOutputPost) := I.

Lemma storage_keys_output_correct `{!islaG Sigma} `{!threadG}
    sp old_ra old_x5 old_data old_size payload tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 20 IslaTraces.write_success_61.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 (writeOutputTraceSpec (sp + BV 64 1712)%bv (BV 64 32)
    (BV 64 0x153a8) payload tail ("x2" ↦ᵣ RVal_Bits sp ∗ P ∗ True)) -∗
  instr_body 0x153a8 (storageKeysOutputPost sp payload tail P) -∗
  instr_body 0x15398 (storageKeysOutputEntry sp old_ra old_x5 old_data old_size payload tail P).
Proof.
  zesu_block.
  all: try (eexists; eexists; repeat split; reflexivity).
  all: unfold storageKeysOutputPost; reflexivity.
Qed.
Print Assumptions storage_keys_output_correct.
