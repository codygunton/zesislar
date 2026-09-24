Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_29 Require Import instrs.

Definition transactionsRemainingWordLoadEntry `{!islaG Sigma} `{!threadG}
    (pointer sp : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x10" ↦ᵣ RVal_Bits pointer ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x11"; "x12"; "x13"; "x26"; "x8"]) ∗ (bv_unsigned sp + 272) ↦ₘ? 8 ∗
   bv_unsigned pointer ↦ₘ∗ bytes ∗ ⌜length bytes = 288%nat⌝ ∗
   ⌜bv_unsigned pointer `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned pointer⌝ ∗ ⌜bv_unsigned pointer + 288 < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 280 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionsRemainingWordLoadEntry) := I.

Definition transactionsRemainingWordLoadPost `{!islaG Sigma} `{!threadG}
    (pointer sp : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x10" ↦ᵣ RVal_Bits pointer ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 160 bytes)))) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 168 bytes)))) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 176 bytes)))) ∗
   "x26" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 184 bytes)))) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 192 bytes)))) ∗
   (bv_unsigned sp + 272) ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 176 bytes))) ∗
   bv_unsigned pointer ↦ₘ∗ bytes ∗ ⌜length bytes = 288%nat⌝ ∗
   ⌜bv_unsigned pointer `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned pointer⌝ ∗ ⌜bv_unsigned pointer + 288 < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 280 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionsRemainingWordLoadPost) := I.

Lemma transactions_remaining_word_loads_correct `{!islaG Sigma} `{!threadG}
    pointer sp bytes (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 6 (drop 15 IslaTraces.write_success_29.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x14f5c (transactionsRemainingWordLoadPost pointer sp bytes P) -∗
  instr_body 0x14f44 (transactionsRemainingWordLoadEntry pointer sp bytes P).
Proof. move => *. zesu_block. Qed.
Print Assumptions transactions_remaining_word_loads_correct.
