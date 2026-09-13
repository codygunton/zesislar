Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_60 Require Import instrs.

Definition storageKeysRemainingShiftsEntry `{!islaG Sigma} `{!threadG}
    (b14 b15 b1 b2 b3 b5 b6 b7 b25 b26 b27 b29 b30 b31 : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x18" ↦ᵣ RVal_Bits (bv_zero_extend 64 b14) ∗
   "x23" ↦ᵣ RVal_Bits (bv_zero_extend 64 b15) ∗
   "x25" ↦ᵣ RVal_Bits (bv_zero_extend 64 b1) ∗
   "x26" ↦ᵣ RVal_Bits (bv_zero_extend 64 b2) ∗
   "x1" ↦ᵣ RVal_Bits (bv_zero_extend 64 b3) ∗
   "x31" ↦ᵣ RVal_Bits (bv_zero_extend 64 b5) ∗
   "x30" ↦ᵣ RVal_Bits (bv_zero_extend 64 b6) ∗
   "x29" ↦ᵣ RVal_Bits (bv_zero_extend 64 b7) ∗
   "x5" ↦ᵣ RVal_Bits (bv_zero_extend 64 b25) ∗
   "x17" ↦ᵣ RVal_Bits (bv_zero_extend 64 b26) ∗
   "x16" ↦ᵣ RVal_Bits (bv_zero_extend 64 b27) ∗
   "x14" ↦ᵣ RVal_Bits (bv_zero_extend 64 b29) ∗
   "x13" ↦ᵣ RVal_Bits (bv_zero_extend 64 b30) ∗
   "x12" ↦ᵣ RVal_Bits (bv_zero_extend 64 b31) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysRemainingShiftsEntry) := I.

Definition storageKeysRemainingShiftsPost `{!islaG Sigma} `{!threadG}
    (b14 b15 b1 b2 b3 b5 b6 b7 b25 b26 b27 b29 b30 b31 : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b14 * 65536)) ∗
   "x23" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b15 * 16777216)) ∗
   "x25" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b1 * 256)) ∗
   "x26" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b2 * 65536)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b3 * 16777216)) ∗
   "x31" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b5 * 256)) ∗
   "x30" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b6 * 65536)) ∗
   "x29" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b7 * 16777216)) ∗
   "x5" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b25 * 256)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b26 * 65536)) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b27 * 16777216)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b29 * 256)) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b30 * 65536)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned b31 * 16777216)) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysRemainingShiftsPost) := I.

Lemma storage_keys_remaining_shifts_correct `{!islaG Sigma} `{!threadG}
    b14 b15 b1 b2 b3 b5 b6 b7 b25 b26 b27 b29 b30 b31 (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 14 (drop 1 IslaTraces.write_success_60.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15324 (storageKeysRemainingShiftsPost b14 b15 b1 b2 b3 b5 b6 b7 b25 b26 b27 b29 b30 b31 P) -∗
  instr_body 0x152ec (storageKeysRemainingShiftsEntry b14 b15 b1 b2 b3 b5 b6 b7 b25 b26 b27 b29 b30 b31 P).
Proof. zesu_block. Qed.
Print Assumptions storage_keys_remaining_shifts_correct.
