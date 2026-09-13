Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_60 Require Import instrs.

Definition storageKeysLowPairsEntry `{!islaG Sigma} `{!threadG}
    (a b c d e f : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x24" ↦ᵣ RVal_Bits (bv_zero_extend 64 a) ∗
   "x25" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b * 256)) ∗
   "x26" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned c * 65536)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned d * 16777216)) ∗
   "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned e * 65536)) ∗
   "x23" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned f * 16777216)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLowPairsEntry) := I.

Definition storageKeysLowPairsPost `{!islaG Sigma} `{!threadG}
    (a b c d e f : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x24" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned c * 65536 + bv_unsigned d * 16777216)) ∗
   "x25" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b * 256)) ∗
   "x26" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned c * 65536)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned d * 16777216)) ∗
   "x18" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned e * 65536 + bv_unsigned f * 16777216)) ∗
   "x23" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned a + bv_unsigned b * 256)) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLowPairsPost) := I.

Lemma storage_keys_low_pairs_correct `{!islaG Sigma} `{!threadG}
    a b c d e f (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 3 (drop 15 IslaTraces.write_success_60.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15330 (storageKeysLowPairsPost a b c d e f P) -∗
  instr_body 0x15324 (storageKeysLowPairsEntry a b c d e f P).
Proof.
  zesu_block.
  all: first [apply array_byte_pair_value | apply array_byte_pair_value16].
Qed.
Print Assumptions storage_keys_low_pairs_correct.
