Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_31 Require Import instrs.

Definition transactionRecipientLowerPairsEntry `{!islaG Sigma} `{!threadG}
    (b279 b280 b265 b266 b267 b268 b269 b270 : bv 8)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b280 * 16777216)) ∗
   "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b279 * 65536)) ∗
   "x12" ↦ᵣ RVal_Bits (bv_zero_extend 64 b265) ∗
   "x19" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b266 * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b268 * 16777216)) ∗
   "x20" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b267 * 65536)) ∗
   "x28" ↦ᵣ RVal_Bits (bv_zero_extend 64 b269) ∗
   "x29" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b270 * 256)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientLowerPairsEntry) := I.

Definition transactionRecipientLowerPairsPost `{!islaG Sigma} `{!threadG}
    (b279 b280 b265 b266 b267 b268 b269 b270 : bv 8)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned b279 * 65536 + bv_unsigned b280 * 16777216)) ∗
   "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b279 * 65536)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b265 + bv_unsigned b266 * 256)) ∗
   "x19" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b266 * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned b267 * 65536 + bv_unsigned b268 * 16777216)) ∗
   "x20" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b267 * 65536)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b269 + bv_unsigned b270 * 256)) ∗
   "x29" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b270 * 256)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientLowerPairsPost) := I.

Lemma transactions_recipient_lower_pairs_correct `{!islaG Sigma} `{!threadG}
    b279 b280 b265 b266 b267 b268 b269 b270 (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_31.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15018
    (transactionRecipientLowerPairsPost b279 b280 b265 b266 b267 b268 b269 b270 P) -∗
  instr_body 0x15008
    (transactionRecipientLowerPairsEntry b279 b280 b265 b266 b267 b268 b269 b270 P).
Proof.
  zesu_block.
  all: first [apply array_byte_pair_value | apply array_byte_pair_value16].
Qed.
Print Assumptions transactions_recipient_lower_pairs_correct.
