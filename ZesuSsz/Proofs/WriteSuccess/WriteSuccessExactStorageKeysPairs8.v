Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_59 Require Import instrs.

Definition storageKeysPairs8Entry `{!islaG Sigma} `{!threadG}
    (a b c d e f g h : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x8" ↦ᵣ RVal_Bits (bv_zero_extend 64 a) ∗
   "x26" ↦ᵣ RVal_Bits (bv_zero_extend 64 b) ∗
   "x1" ↦ᵣ RVal_Bits (bv_zero_extend 64 c) ∗
   "x21" ↦ᵣ RVal_Bits (bv_zero_extend 64 d) ∗
   "x24" ↦ᵣ RVal_Bits (bv_zero_extend 64 e) ∗
   "x20" ↦ᵣ RVal_Bits (bv_zero_extend 64 f) ∗
   "x9" ↦ᵣ RVal_Bits (bv_zero_extend 64 g) ∗
   "x25" ↦ᵣ RVal_Bits (bv_zero_extend 64 h) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysPairs8Entry) := I.

Definition storageKeysPairs8Post `{!islaG Sigma} `{!threadG}
    (a b c d e f g h : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned a + bv_unsigned b * 256)) ∗
   "x26" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b * 256)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned c * 65536)) ∗
   "x21" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned c * 65536 + bv_unsigned d * 16777216)) ∗
   "x24" ↦ᵣ RVal_Bits (bv_zero_extend 64 e) ∗
   "x20" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned e + bv_unsigned f * 256)) ∗
   "x9" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned g * 65536 + bv_unsigned h * 16777216)) ∗
   "x25" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned h * 16777216)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysPairs8Post) := I.

Lemma storage_keys_pairs8_correct `{!islaG Sigma} `{!threadG}
    a b c d e f g h (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 10 (drop 11 IslaTraces.write_success_59.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x152dc (storageKeysPairs8Post a b c d e f g h P) -∗
  instr_body 0x152b4 (storageKeysPairs8Entry a b c d e f g h P).
Proof.
  zesu_block.
  all: first [apply array_byte_pair_shift_value | apply array_byte_pair_shift_value16].
Qed.
Print Assumptions storage_keys_pairs8_correct.
