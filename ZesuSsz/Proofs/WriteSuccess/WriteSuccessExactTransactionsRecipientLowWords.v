Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From Coq Require Import Lists.List ZArith.ZArith.
From IslaTraces.write_success_32 Require Import instrs.

Definition transactionRecipientLowWordsEntry `{!islaG Sigma} `{!threadG}
    (a b c d e f g h : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col [(KindReg "x16", BitsShape 64)] ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned a + bv_unsigned b * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned c * 65536 + bv_unsigned d * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned e + bv_unsigned f * 256)) ∗
   "x5" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned g * 65536 + bv_unsigned h * 16777216)) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientLowWordsEntry) := I.

Definition transactionRecipientLowWordsPost `{!islaG Sigma} `{!threadG}
    (a b c d e f g h : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [a;b;c;d])) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [e;f;g;h])) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned c * 65536 + bv_unsigned d * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned e + bv_unsigned f * 256)) ∗
   "x5" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned g * 65536 + bv_unsigned h * 16777216)) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientLowWordsPost) := I.

Lemma transactions_recipient_low_words_correct `{!islaG Sigma} `{!threadG}
    a b c d e f g h (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_32.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15068 (transactionRecipientLowWordsPost a b c d e f g h P) -∗
  instr_body 0x15060 (transactionRecipientLowWordsEntry a b c d e f g h P).
Proof. zesu_block. all: apply array_byte_four_value. Qed.
Print Assumptions transactions_recipient_low_words_correct.
