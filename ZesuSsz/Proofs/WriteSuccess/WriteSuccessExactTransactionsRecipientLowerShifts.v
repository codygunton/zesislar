Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_31 Require Import instrs.

Definition transactionRecipientLowerShiftEntry `{!islaG Sigma} `{!threadG}
    (b279 b280 b266 b267 b268 b270 : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x18" ↦ᵣ RVal_Bits (bv_zero_extend 64 b279) ∗
   "x13" ↦ᵣ RVal_Bits (bv_zero_extend 64 b280) ∗
   "x19" ↦ᵣ RVal_Bits (bv_zero_extend 64 b266) ∗
   "x20" ↦ᵣ RVal_Bits (bv_zero_extend 64 b267) ∗
   "x7" ↦ᵣ RVal_Bits (bv_zero_extend 64 b268) ∗
   "x29" ↦ᵣ RVal_Bits (bv_zero_extend 64 b270) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientLowerShiftEntry) := I.

Definition transactionRecipientLowerShiftPost `{!islaG Sigma} `{!threadG}
    (b279 b280 b266 b267 b268 b270 : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b279 * 65536)) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b280 * 16777216)) ∗
   "x19" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b266 * 256)) ∗
   "x20" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b267 * 65536)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b268 * 16777216)) ∗
   "x29" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b270 * 256)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientLowerShiftPost) := I.

Lemma transactions_recipient_lower_shifts_correct `{!islaG Sigma} `{!threadG}
    b279 b280 b266 b267 b268 b270 (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_31.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15008
    (transactionRecipientLowerShiftPost b279 b280 b266 b267 b268 b270 P) -∗
  instr_body 0x14ff0
    (transactionRecipientLowerShiftEntry b279 b280 b266 b267 b268 b270 P).
Proof. zesu_block. Qed.
Print Assumptions transactions_recipient_lower_shifts_correct.
