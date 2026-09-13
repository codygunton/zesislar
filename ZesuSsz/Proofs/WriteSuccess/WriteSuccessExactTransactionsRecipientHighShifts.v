Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_31 Require Import instrs.

Definition transactionRecipientHighShiftEntry `{!islaG Sigma} `{!threadG}
    (b276 b278 : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x29" ↦ᵣ RVal_Bits (bv_zero_extend 64 b276) ∗
   "x31" ↦ᵣ RVal_Bits (bv_zero_extend 64 b278) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientHighShiftEntry) := I.

Definition transactionRecipientHighShiftPost `{!islaG Sigma} `{!threadG}
    (b276 b278 : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x29" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b276 * 16777216)) ∗
   "x31" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b278 * 256)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientHighShiftPost) := I.

Lemma transactions_recipient_high_shifts_correct `{!islaG Sigma} `{!threadG}
    b276 b278 (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_31.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14fd0 (transactionRecipientHighShiftPost b276 b278 P) -∗
  instr_body 0x14fc8 (transactionRecipientHighShiftEntry b276 b278 P).
Proof. zesu_block. Qed.
Print Assumptions transactions_recipient_high_shifts_correct.
