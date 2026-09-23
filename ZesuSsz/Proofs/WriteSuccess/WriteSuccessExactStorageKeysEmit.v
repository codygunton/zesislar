Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.WordArrays.
Import WordMatching.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysResources.
From IslaTraces.write_success_61 Require Import instrs.
Local Existing Instance subsume_instr_pre_guard_inst | 0.

Definition storageKeyWord (key : list (bv 8)) (offset : nat) : bv 64 :=
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop offset key))).

Definition storageKeysEmitFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (key : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ "x12" ↦ᵣ RVal_Bits (storageKeyWord key 8) ∗
   "x13" ↦ᵣ RVal_Bits (storageKeyWord key 16) ∗
   "x14" ↦ᵣ RVal_Bits (storageKeyWord key 0) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysEmitFrame) := I.

Definition storageKeysEmitEntry `{!islaG Sigma} `{!threadG}
    (sp old_ra old5 old_size a b c d : bv 64) (key : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗
   "x5" ↦ᵣ RVal_Bits old5 ∗ "x11" ↦ᵣ RVal_Bits old_size ∗
   "x10" ↦ᵣ RVal_Bits (storageKeyWord key 24) ∗
   storageKeysEmitFrame sp key P ∗
   (bv_unsigned sp + 1712) ↦ₘ a ∗ (bv_unsigned sp + 1720) ↦ₘ b ∗
   (bv_unsigned sp + 1728) ↦ₘ c ∗ (bv_unsigned sp + 1736) ↦ₘ d ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp + BV 64 1712)%bv (BV 64 32) key tail) ∗
   ⌜length key = 32%nat⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1744 < (machineRamEnd defaultMap)⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysEmitEntry) := I.

Definition storageKeysEmitPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (key : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x153a8) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1712)%bv ∗ "x11" ↦ᵣ RVal_Bits (BV 64 32) ∗
   bv_unsigned (sp + BV 64 1712)%bv ↦ₘ∗ key ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace tail ∗ storageKeysEmitFrame sp key P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysEmitPost) := I.

Lemma storage_keys_emit_correct `{!islaG Sigma} `{!threadG}
    sp old_ra old5 old_size a b c d key tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 8 (drop 16 IslaTraces.write_success_61.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 (writeOutputTraceSpec (sp + BV 64 1712)%bv (BV 64 32)
    (BV 64 0x153a8) key tail (storageKeysEmitFrame sp key P)) -∗
  instr_body 0x153a8 (storageKeysEmitPost sp key tail P) -∗
  instr_body 0x15388 (storageKeysEmitEntry sp old_ra old5 old_size a b c d key tail P).
Proof. move => *. zesu_block. Qed.
Print Assumptions storage_keys_emit_correct.
