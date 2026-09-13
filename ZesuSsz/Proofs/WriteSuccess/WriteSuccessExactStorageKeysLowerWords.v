Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_61 Require Import instrs.

Definition storageKeysLowerWordsEntry `{!islaG Sigma} `{!threadG}
    (a b c d e f g h i j k l m n o p : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x6", BitsShape 64)] ∗
   "x23" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned a + bv_unsigned b * 256)) ∗
   "x24" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned c * 65536 + bv_unsigned d * 16777216)) ∗
   "x15" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned e + bv_unsigned f * 256)) ∗
   "x29" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned g * 65536 + bv_unsigned h * 16777216)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned i + bv_unsigned j * 256)) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned k * 65536 + bv_unsigned l * 16777216)) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned m + bv_unsigned n * 256)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned o * 65536 + bv_unsigned p * 16777216)) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLowerWordsEntry) := I.

Definition storageKeysLowerWordsPost `{!islaG Sigma} `{!threadG}
    (a b c d e f g h i j k l m n o p : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [a;b;c;d])) ∗
   "x15" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [e;f;g;h])) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [i;j;k;l])) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [m;n;o;p])) ∗
   "x23" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned a + bv_unsigned b * 256)) ∗
   "x24" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned c * 65536 + bv_unsigned d * 16777216)) ∗
   "x29" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned g * 65536 + bv_unsigned h * 16777216)) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned k * 65536 + bv_unsigned l * 16777216)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned o * 65536 + bv_unsigned p * 16777216)) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLowerWordsPost) := I.

Lemma storage_keys_lower_words_correct `{!islaG Sigma} `{!threadG}
    a b c d e f g h i j k l m n o p (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 4 IslaTraces.write_success_61.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15368 (storageKeysLowerWordsPost a b c d e f g h i j k l m n o p P) -∗
  instr_body 0x15358 (storageKeysLowerWordsEntry a b c d e f g h i j k l m n o p P).
Proof. zesu_block. all: apply array_byte_four_value. Qed.
Print Assumptions storage_keys_lower_words_correct.
