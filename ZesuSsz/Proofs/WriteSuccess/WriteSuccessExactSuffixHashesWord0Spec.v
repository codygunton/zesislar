Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Definition suffixWord0Entry `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (source : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗ "x9" ↦ᵣ RVal_Bits pointer ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x10";"x11";"x12";"x13";"x14";"x15";"x16"]) ∗
   base ↦ₘ∗ source ∗ (bv_unsigned sp + 1744) ↦ₘ? 8 ∗
   ⌜bv_unsigned pointer = (base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length source)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length source) < (machineRamEnd defaultMap))%Z⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜((mapRamBase defaultMap) <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1752 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixWord0Entry) := I.

Definition suffixWord0Post `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (source : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗ "x9" ↦ᵣ RVal_Bits pointer ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x10";"x11";"x12";"x13";"x14";"x15";"x16"]) ∗
   base ↦ₘ∗ source ∗ (bv_unsigned sp + 1744) ↦ₘ (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (index + 0)%nat source)))) ∗
   ⌜bv_unsigned pointer = (base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length source)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length source) < (machineRamEnd defaultMap))%Z⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜((mapRamBase defaultMap) <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1752 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixWord0Post) := I.


Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixHashesByte.

Definition suffixWord0Mid `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (source : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗ "x9" ↦ᵣ RVal_Bits pointer ∗
   "x10" ↦ᵣ RVal_Bits (bv_or (bv_shiftl (suffixWordByte source (index + 1)%nat) (BV 64 8)) (suffixWordByte source (index + 0)%nat)) ∗
   "x11" ↦ᵣ RVal_Bits (bv_or (bv_shiftl (suffixWordByte source (index + 3)%nat) (BV 64 24)) (bv_shiftl (suffixWordByte source (index + 2)%nat) (BV 64 16))) ∗
   "x12" ↦ᵣ RVal_Bits (suffixWordByte source (index + 5)%nat) ∗
   "x13" ↦ᵣ RVal_Bits (suffixWordByte source (index + 0)%nat) ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x14";"x15";"x16"]) ∗
   base ↦ₘ∗ source ∗ (bv_unsigned sp + 1744) ↦ₘ? 8 ∗
   ⌜bv_unsigned pointer = (base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length source)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length source) < (machineRamEnd defaultMap))%Z⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜((mapRamBase defaultMap) <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1752 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixWord0Mid) := I.
