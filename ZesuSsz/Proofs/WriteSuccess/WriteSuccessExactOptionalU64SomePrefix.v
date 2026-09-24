Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
From IslaTraces.write_success_04 Require Import instrs.

Local Existing Instance subsume_instr_pre_guard_inst | 0.

Definition optionalU64SomeExactPrefixPost `{!islaG Sigma} `{!threadG}
    (pointer value sp ret old_x8 old_x11 : bv 64)
    (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15be4) ∗
   "x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
   "x8" ↦ᵣ RVal_Bits value ∗ "x10" ↦ᵣ RVal_Bits (BV 64 1) ∗
   "x11" ↦ᵣ RVal_Bits old_x11 ∗ bv_unsigned pointer ↦ₘ∗ bytes ∗
   (bv_unsigned sp - 32) ↦ₘ? 16 ∗
   (bv_unsigned sp - 16) ↦ₘ old_x8 ∗ (bv_unsigned sp - 8) ↦ₘ ret ∗
   P ∗ True)%I.

Definition optionalU64SomeExactPrefixEntry `{!islaG Sigma} `{!threadG}
    (pointer value sp ret old_x8 old_x11 : bv 64)
    (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x8" ↦ᵣ RVal_Bits old_x8 ∗ "x10" ↦ᵣ RVal_Bits pointer ∗
   "x11" ↦ᵣ RVal_Bits old_x11 ∗ bv_unsigned pointer ↦ₘ∗ bytes ∗
   (bv_unsigned sp - 32) ↦ₘ? 32 ∗
   ⌜value = Z_to_bv 64 (little_endian_to_bv 8 (take 8 bytes))⌝ ∗
   ⌜(8 <= length bytes)%nat⌝ ∗ ⌜bv_extract 0 3 pointer = BV 3 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned pointer⌝ ∗
   ⌜bv_unsigned pointer + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 32⌝ ∗ ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   P ∗
   instr_pre 0x15be8
     (optionalU64SomeExactPrefixPost pointer value sp ret old_x8 old_x11 bytes P) ∗ True)%I.

Global Instance : LithiumUnfold (@optionalU64SomeExactPrefixPost) := I.
Global Instance : LithiumUnfold (@optionalU64SomeExactPrefixEntry) := I.

Lemma optional_u64_some_exact_prefix `{!islaG Sigma} `{!threadG}
    (pointer value sp ret old_x8 old_x11 : bv 64)
    (bytes : list (bv 8)) (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 6 (drop 2 IslaTraces.write_success_04.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bd0
    (optionalU64SomeExactPrefixEntry pointer value sp ret old_x8 old_x11 bytes P).
Proof. move => *. zesu_block. Qed.

Print Assumptions optional_u64_some_exact_prefix.
