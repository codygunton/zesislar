Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.
From IslaTraces.write_success_106 Require Import instrs.
Local Existing Instance subsume_instr_pre_guard_inst | 0.

Definition suffixEmitFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixEmitFrame) := I.

Definition suffixEmitEntry `{!islaG Sigma} `{!threadG}
    (sp old_ra old5 old_data old_size : bv 64) (row : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗
   "x5" ↦ᵣ RVal_Bits old5 ∗ "x10" ↦ᵣ RVal_Bits old_data ∗
   "x11" ↦ᵣ RVal_Bits old_size ∗
   bv_unsigned (sp + BV 64 1744)%bv ↦ₘ∗ row ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 32) row tail) ∗
   ⌜length row = 32%nat⌝ ∗ suffixEmitFrame sp P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixEmitEntry) := I.

Definition suffixEmitPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (row : list (bv 8)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x158d4) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1744)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 32) ∗
   bv_unsigned (sp + BV 64 1744)%bv ↦ₘ∗ row ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ suffixEmitFrame sp P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixEmitPost) := I.

Lemma suffix_emit_correct `{!islaG Sigma} `{!threadG}
    sp old_ra old5 old_data old_size row tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 20 IslaTraces.write_success_106.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 (writeOutputTraceSpec (sp + BV 64 1744)%bv (BV 64 32)
    (BV 64 0x158d4) row tail (suffixEmitFrame sp P)) -∗
  instr_body 0x158d4 (suffixEmitPost sp row tail P) -∗
  instr_body 0x158c4 (suffixEmitEntry sp old_ra old5 old_data old_size row tail P).
Proof. zesu_block. Qed.
Print Assumptions suffix_emit_correct.
