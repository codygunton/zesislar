Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_61 Require Import instrs.

Definition storageKeysUpperWideEntry `{!islaG Sigma} `{!threadG}
    (a b c d e f g h i j k l m n o p : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x12", BitsShape 64)] ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [a;b;c;d])) ∗
   "x14" ↦ᵣ RVal_Bits (bv_shiftl (Z_to_bv 64 (little_endian_to_bv 8 [e;f;g;h])) (BV 64 32)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [i;j;k;l])) ∗
   "x5" ↦ᵣ RVal_Bits (bv_shiftl (Z_to_bv 64 (little_endian_to_bv 8 [m;n;o;p])) (BV 64 32)) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysUpperWideEntry) := I.

Definition storageKeysUpperWidePost `{!islaG Sigma} `{!threadG}
    (a b c d e f g h i j k l m n o p : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [a;b;c;d;e;f;g;h])) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [i;j;k;l;m;n;o;p])) ∗
   "x14" ↦ᵣ RVal_Bits (bv_shiftl (Z_to_bv 64 (little_endian_to_bv 8 [e;f;g;h])) (BV 64 32)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [i;j;k;l])) ∗
   "x5" ↦ᵣ RVal_Bits (bv_shiftl (Z_to_bv 64 (little_endian_to_bv 8 [m;n;o;p])) (BV 64 32)) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysUpperWidePost) := I.

Lemma storage_keys_upper_wide_correct `{!islaG Sigma} `{!threadG}
    a b c d e f g h i j k l m n o p (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 2 (drop 12 IslaTraces.write_success_61.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15380 (storageKeysUpperWidePost a b c d e f g h i j k l m n o p P) -∗
  instr_body 0x15378 (storageKeysUpperWideEntry a b c d e f g h i j k l m n o p P).
Proof. zesu_block. all: apply array_byte_eight. Qed.
Print Assumptions storage_keys_upper_wide_correct.
