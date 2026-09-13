Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From Coq Require Import Lists.List ZArith.ZArith.
From IslaTraces.write_success_32 Require Import instrs.

Definition transactionRecipientWordsEntry `{!islaG Sigma} `{!threadG}
    (a b c d e f g h i j k l : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned a + bv_unsigned b * 256)) ∗
   "x15" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned c * 65536 + bv_unsigned d * 16777216)) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned e + bv_unsigned f * 256)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned g * 65536 + bv_unsigned h * 16777216)) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned i + bv_unsigned j * 256)) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned k * 65536 + bv_unsigned l * 16777216)) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientWordsEntry) := I.

Definition transactionRecipientWordsPost `{!islaG Sigma} `{!threadG}
    (a b c d e f g h i j k l : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [a;b;c;d])) ∗
   "x15" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [e;f;g;h])) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned e + bv_unsigned f * 256)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned g * 65536 + bv_unsigned h * 16777216)) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned i + bv_unsigned j * 256)) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [i;j;k;l])) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientWordsPost) := I.

Lemma transactions_recipient_words_correct `{!islaG Sigma} `{!threadG}
    a b c d e f g h i j k l (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_32.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15044 (transactionRecipientWordsPost a b c d e f g h i j k l P) -∗
  instr_body 0x15038 (transactionRecipientWordsEntry a b c d e f g h i j k l P).
Proof. zesu_block. all: apply array_byte_four_value. Qed.
Print Assumptions transactions_recipient_words_correct.
