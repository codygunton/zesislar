Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_30 Require Import instrs.

Definition transactionRecipientPairEntry `{!islaG Sigma} `{!threadG}
    (low high : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x14" ↦ᵣ RVal_Bits (bv_zero_extend 64 low) ∗
   "x15" ↦ᵣ RVal_Bits (bv_zero_extend 64 high) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientPairEntry) := I.

Definition transactionRecipientPairPost `{!islaG Sigma} `{!threadG}
    (low high : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [low; high])) ∗
   "x15" ↦ᵣ RVal_Bits (bv_shiftl (bv_zero_extend 64 high) (BV 64 8)) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientPairPost) := I.

Lemma transactions_recipient_pair_correct `{!islaG Sigma} `{!threadG}
    low high (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_30.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14fb0 (transactionRecipientPairPost low high P) -∗
  instr_body 0x14fa8 (transactionRecipientPairEntry low high P).
Proof. zesu_block. all: apply array_byte_pair. Qed.
Print Assumptions transactions_recipient_pair_correct.
