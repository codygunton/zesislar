Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From Coq Require Import Lists.List ZArith.ZArith.
From IslaTraces.write_success_32 Require Import instrs.

Definition transactionRecipientWideEntry `{!islaG Sigma} `{!threadG}
    (a b c d e f g h i j k l m n o p : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [a;b;c;d])) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [e;f;g;h])) ∗
   "x15" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [i;j;k;l])) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [m;n;o;p])) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientWideEntry) := I.

Definition transactionRecipientWidePost `{!islaG Sigma} `{!threadG}
    (a b c d e f g h i j k l m n o p : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [a;b;c;d;e;f;g;h])) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64
     (little_endian_to_bv 8 [e;f;g;h] * 4294967296)) ∗
   "x15" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [i;j;k;l])) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [i;j;k;l;m;n;o;p])) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientWidePost) := I.

Lemma transactions_recipient_wide_correct `{!islaG Sigma} `{!threadG}
    a b c d e f g h i j k l m n o p (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_32.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15078 (transactionRecipientWidePost a b c d e f g h i j k l m n o p P) -∗
  instr_body 0x15068 (transactionRecipientWideEntry a b c d e f g h i j k l m n o p P).
Proof. zesu_block. all: apply array_byte_eight. Qed.
Print Assumptions transactions_recipient_wide_correct.
