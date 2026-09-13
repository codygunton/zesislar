Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_69 Require Import instrs.

Definition blobUpperWordsEntry `{!islaG Sigma} `{!threadG}
    (a b c d e f g h i j k l m n o p : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x13", BitsShape 64); (KindReg "x14", BitsShape 64); (KindReg "x17", BitsShape 64)] ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned a + bv_unsigned b * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned c * 65536 + bv_unsigned d * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned e + bv_unsigned f * 256)) ∗
   "x20" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned g * 65536 + bv_unsigned h * 16777216)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned i + bv_unsigned j * 256)) ∗
   "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned k * 65536 + bv_unsigned l * 16777216)) ∗
   "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned m + bv_unsigned n * 256)) ∗
   "x24" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned o * 65536 + bv_unsigned p * 16777216)) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@blobUpperWordsEntry) := I.

Definition blobUpperWordsPost `{!islaG Sigma} `{!threadG}
    (a b c d e f g h i j k l m n o p : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [a;b;c;d])) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [e;f;g;h])) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [i;j;k;l])) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [m;n;o;p])) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned a + bv_unsigned b * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned c * 65536 + bv_unsigned d * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned e + bv_unsigned f * 256)) ∗
   "x20" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned g * 65536 + bv_unsigned h * 16777216)) ∗
   "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned k * 65536 + bv_unsigned l * 16777216)) ∗
   "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned m + bv_unsigned n * 256)) ∗
   "x24" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned o * 65536 + bv_unsigned p * 16777216)) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@blobUpperWordsPost) := I.

Lemma blob_upper_words_correct `{!islaG Sigma} `{!threadG}
    a b c d e f g h i j k l m n o p (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 1 IslaTraces.write_success_69.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15508 (blobUpperWordsPost a b c d e f g h i j k l m n o p P) -∗
  instr_body 0x154f8 (blobUpperWordsEntry a b c d e f g h i j k l m n o p P).
Proof. zesu_block. all: apply array_byte_four_value. Qed.
Print Assumptions blob_upper_words_correct.
