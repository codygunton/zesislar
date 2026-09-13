Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_68 Require Import instrs.
From IslaTraces.write_success_69 Require Import instrs.

Definition blobLowPairsEntry `{!islaG Sigma} `{!threadG}
    (b0 b1 b2 b3 b4 b5 b6 b7 b14 b15 b24 b25 b26 b27 b28 b29 b30 b31 : bv 8)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x24" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b14 * 65536)) ∗
   "x25" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b15 * 16777216)) ∗
   "x21" ↦ᵣ RVal_Bits (bv_zero_extend 64 b0) ∗
   "x22" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b1 * 256)) ∗
   "x23" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b2 * 65536)) ∗
   "x26" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b3 * 16777216)) ∗
   "x15" ↦ᵣ RVal_Bits (bv_zero_extend 64 b4) ∗
   "x31" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b5 * 256)) ∗
   "x30" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b6 * 65536)) ∗
   "x29" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b7 * 16777216)) ∗
   "x11" ↦ᵣ RVal_Bits (bv_zero_extend 64 b24) ∗
   "x5" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b25 * 256)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b26 * 65536)) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b27 * 16777216)) ∗
   "x10" ↦ᵣ RVal_Bits (bv_zero_extend 64 b28) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b29 * 256)) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b30 * 65536)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b31 * 16777216)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLowPairsEntry) := I.

Definition blobLowPairsPost `{!islaG Sigma} `{!threadG}
    (b0 b1 b2 b3 b4 b5 b6 b7 b14 b15 b24 b25 b26 b27 b28 b29 b30 b31 : bv 8)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x24" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b14 * 65536 + bv_unsigned b15 * 16777216)) ∗
   "x25" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b15 * 16777216)) ∗
   "x21" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b0 + bv_unsigned b1 * 256)) ∗
   "x22" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b2 * 65536 + bv_unsigned b3 * 16777216)) ∗
   "x23" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b2 * 65536)) ∗
   "x26" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b3 * 16777216)) ∗
   "x15" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b4 + bv_unsigned b5 * 256)) ∗
   "x31" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b5 * 256)) ∗
   "x30" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b6 * 65536)) ∗
   "x29" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b6 * 65536 + bv_unsigned b7 * 16777216)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b24 + bv_unsigned b25 * 256)) ∗
   "x5" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b25 * 256)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b26 * 65536)) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b26 * 65536 + bv_unsigned b27 * 16777216)) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b28 + bv_unsigned b29 * 256)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b29 * 256)) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b30 * 65536)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b30 * 65536 + bv_unsigned b31 * 16777216)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLowPairsPost) := I.

Lemma blob_low_pairs_correct `{!islaG Sigma} `{!threadG}
    b0 b1 b2 b3 b4 b5 b6 b7 b14 b15 b24 b25 b26 b27 b28 b29 b30 b31 (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 16 IslaTraces.write_success_68.instrs.instr_map ++
     take 1 IslaTraces.write_success_69.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x154f8 (blobLowPairsPost b0 b1 b2 b3 b4 b5 b6 b7 b14 b15 b24 b25 b26 b27 b28 b29 b30 b31 P) -∗
  instr_body 0x154d4 (blobLowPairsEntry b0 b1 b2 b3 b4 b5 b6 b7 b14 b15 b24 b25 b26 b27 b28 b29 b30 b31 P).
Proof.
  zesu_block.
  all: first [apply array_byte_pair_value | apply array_byte_pair_value16].
Qed.
Print Assumptions blob_low_pairs_correct.
