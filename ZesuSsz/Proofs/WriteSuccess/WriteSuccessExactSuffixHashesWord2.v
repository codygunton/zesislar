Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_103 Require Import instrs.
From IslaTraces.write_success_104 Require Import instrs.
Local Remove Hints IslaTraces.write_success_104.a15808_spec.a15808_spec_inst : typeclass_instances.

Definition suffixWord2Entry `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (source : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗ "x9" ↦ᵣ RVal_Bits pointer ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x10";"x11";"x12";"x13";"x14";"x15";"x16"]) ∗
   base ↦ₘ∗ source ∗ (bv_unsigned sp + 1760) ↦ₘ? 8 ∗
   ⌜bv_unsigned pointer = (base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length source)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length source) < (machineRamEnd defaultMap))%Z⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜((mapRamBase defaultMap) <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1768 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixWord2Entry) := I.

Definition suffixWord2Post `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (source : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗ "x9" ↦ᵣ RVal_Bits pointer ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x10";"x11";"x12";"x13";"x14";"x15";"x16"]) ∗
   base ↦ₘ∗ source ∗ (bv_unsigned sp + 1760) ↦ₘ (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (index + 16)%nat source)))) ∗
   ⌜bv_unsigned pointer = (base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length source)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length source) < (machineRamEnd defaultMap))%Z⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜((mapRamBase defaultMap) <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1768 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixWord2Post) := I.

Lemma suffix_word2_correct `{!islaG Sigma} `{!threadG}
    sp pointer base source index (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 23 IslaTraces.write_success_103.instrs.instr_map ++ take 22 IslaTraces.write_success_104.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x1580c (suffixWord2Post sp pointer base source index P) -∗
  instr_body 0x157b0 (suffixWord2Entry sp pointer base source index P).
Proof. zesu_block. Qed.
Print Assumptions suffix_word2_correct.

