Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.WordArrays.
Import WordMatching.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysEmit.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysResources.
From IslaTraces.write_success_69 Require Import instrs.
From IslaTraces.write_success_70 Require Import instrs.
Local Remove Hints IslaTraces.write_success_69.a15538_spec.a15538_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_69.a1553c_spec.a1553c_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_69.a15540_spec.a15540_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_69.a15544_spec.a15544_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_70.a15554_spec.a15554_spec_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_guard_inst | 0.

Definition blobEmitFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (key : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ "x12" ↦ᵣ RVal_Bits (storageKeyWord key 8) ∗
   "x13" ↦ᵣ RVal_Bits (storageKeyWord key 16) ∗
   "x14" ↦ᵣ RVal_Bits (storageKeyWord key 0) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobEmitFrame) := I.

Definition blobEmitEntry `{!islaG Sigma} `{!threadG}
    (sp old_ra old5 old_size a b c d : bv 64) (key : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗
   "x5" ↦ᵣ RVal_Bits old5 ∗ "x11" ↦ᵣ RVal_Bits old_size ∗
   "x10" ↦ᵣ RVal_Bits (storageKeyWord key 24) ∗
   blobEmitFrame sp key P ∗
   (bv_unsigned sp + 1680) ↦ₘ a ∗ (bv_unsigned sp + 1688) ↦ₘ b ∗
   (bv_unsigned sp + 1696) ↦ₘ c ∗ (bv_unsigned sp + 1704) ↦ₘ d ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp + BV 64 1680)%bv (BV 64 32) key tail) ∗
   ⌜length key = 32%nat⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1712 < (machineRamEnd defaultMap)⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@blobEmitEntry) := I.

Definition blobEmitPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (key : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15558) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1680)%bv ∗ "x11" ↦ᵣ RVal_Bits (BV 64 32) ∗
   bv_unsigned (sp + BV 64 1680)%bv ↦ₘ∗ key ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace tail ∗ blobEmitFrame sp key P ∗ True)%I.
Global Instance : LithiumUnfold (@blobEmitPost) := I.

Lemma blob_emit_correct `{!islaG Sigma} `{!threadG}
    sp old_ra old5 old_size a b c d key tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 17 IslaTraces.write_success_69.instrs.instr_map ++ IslaTraces.write_success_70.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 (writeOutputTraceSpec (sp + BV 64 1680)%bv (BV 64 32)
    (BV 64 0x15558) key tail (blobEmitFrame sp key P)) -∗
  instr_body 0x15558 (blobEmitPost sp key tail P) -∗
  instr_body 0x15538 (blobEmitEntry sp old_ra old5 old_size a b c d key tail P).
Proof.
  zesu_block.
  all: try (eexists; eexists; repeat split; reflexivity).
  all: try (unfold blobEmitPost; reflexivity).
Qed.
Print Assumptions blob_emit_correct.
