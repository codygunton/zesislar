Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_30 Require Import instrs.

Definition transactionRecipientShiftEntry `{!islaG Sigma} `{!threadG}
    (b283 b284 b274 b275 : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x16" ↦ᵣ RVal_Bits (bv_zero_extend 64 b283) ∗
   "x17" ↦ᵣ RVal_Bits (bv_zero_extend 64 b284) ∗
   "x7" ↦ᵣ RVal_Bits (bv_zero_extend 64 b274) ∗
   "x28" ↦ᵣ RVal_Bits (bv_zero_extend 64 b275) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientShiftEntry) := I.

Definition transactionRecipientShiftPost `{!islaG Sigma} `{!threadG}
    (b283 b284 b274 b275 : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b283 * 65536)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b284 * 16777216)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b274 * 256)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b275 * 65536)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientShiftPost) := I.

Lemma transactions_recipient_shifts_correct `{!islaG Sigma} `{!threadG}
    b283 b284 b274 b275 (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_30.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14fc8 (transactionRecipientShiftPost b283 b284 b274 b275 P) -∗
  instr_body 0x14fb8 (transactionRecipientShiftEntry b283 b284 b274 b275 P).
Proof. zesu_block. Qed.
Print Assumptions transactions_recipient_shifts_correct.
