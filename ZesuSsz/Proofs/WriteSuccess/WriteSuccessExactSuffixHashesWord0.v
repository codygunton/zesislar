Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_105 Require Import instrs.
From IslaTraces.write_success_106 Require Import instrs.
Local Remove Hints IslaTraces.write_success_106.a158c0_spec.a158c0_spec_inst : typeclass_instances.

Definition suffixWord0Entry `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (source : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗ "x9" ↦ᵣ RVal_Bits pointer ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x10";"x11";"x12";"x13";"x14";"x15";"x16"]) ∗
   base ↦ₘ∗ source ∗ (bv_unsigned sp + 1744) ↦ₘ? 8 ∗
   ⌜bv_unsigned pointer = (base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length source)%nat⌝ ∗ ⌜(0x20000000 <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length source) < 0x40000000)%Z⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(0x20000000 <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1752 < 0x40000000)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixWord0Entry) := I.

Definition suffixWord0Post `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (source : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗ "x9" ↦ᵣ RVal_Bits pointer ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x10";"x11";"x12";"x13";"x14";"x15";"x16"]) ∗
   base ↦ₘ∗ source ∗ (bv_unsigned sp + 1744) ↦ₘ (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (index + 0)%nat source)))) ∗
   ⌜bv_unsigned pointer = (base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length source)%nat⌝ ∗ ⌜(0x20000000 <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length source) < 0x40000000)%Z⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(0x20000000 <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1752 < 0x40000000)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixWord0Post) := I.

Lemma suffix_word0_correct `{!islaG Sigma} `{!threadG}
    sp pointer base source index (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 21 IslaTraces.write_success_105.instrs.instr_map ++ take 20 IslaTraces.write_success_106.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x158c4 (suffixWord0Post sp pointer base source index P) -∗
  instr_body 0x15868 (suffixWord0Entry sp pointer base source index P).
Proof. zesu_block. Qed.
Print Assumptions suffix_word0_correct.

