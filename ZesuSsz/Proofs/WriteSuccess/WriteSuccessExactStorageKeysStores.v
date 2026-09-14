Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_61 Require Import instrs.

Definition storageKeysStoresEntry `{!islaG Sigma} `{!threadG}
    (sp a b c d old_a old_b old_c old_d : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x14" ↦ᵣ RVal_Bits a ∗ "x12" ↦ᵣ RVal_Bits b ∗
   "x13" ↦ᵣ RVal_Bits c ∗ "x10" ↦ᵣ RVal_Bits d ∗
   (bv_unsigned sp + 1712) ↦ₘ old_a ∗ (bv_unsigned sp + 1720) ↦ₘ old_b ∗
   (bv_unsigned sp + 1728) ↦ₘ old_c ∗ (bv_unsigned sp + 1736) ↦ₘ old_d ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1744 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysStoresEntry) := I.

Definition storageKeysStoresPost `{!islaG Sigma} `{!threadG}
    (sp a b c d : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x14" ↦ᵣ RVal_Bits a ∗ "x12" ↦ᵣ RVal_Bits b ∗
   "x13" ↦ᵣ RVal_Bits c ∗ "x10" ↦ᵣ RVal_Bits d ∗
   (bv_unsigned sp + 1712) ↦ₘ a ∗ (bv_unsigned sp + 1720) ↦ₘ b ∗
   (bv_unsigned sp + 1728) ↦ₘ c ∗ (bv_unsigned sp + 1736) ↦ₘ d ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1744 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysStoresPost) := I.

Lemma storage_keys_stores_correct `{!islaG Sigma} `{!threadG}
    sp a b c d old_a old_b old_c old_d (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 16 IslaTraces.write_success_61.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15398 (storageKeysStoresPost sp a b c d P) -∗
  instr_body 0x15388 (storageKeysStoresEntry sp a b c d old_a old_b old_c old_d P).
Proof. zesu_block. Qed.
Print Assumptions storage_keys_stores_correct.
