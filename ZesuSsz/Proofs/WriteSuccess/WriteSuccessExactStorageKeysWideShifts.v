Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_61 Require Import instrs.

Definition storageKeysWideShiftsEntry `{!islaG Sigma} `{!threadG}
    (a b c d : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x14" ↦ᵣ RVal_Bits a ∗
   "x5" ↦ᵣ RVal_Bits b ∗ "x15" ↦ᵣ RVal_Bits c ∗
   "x10" ↦ᵣ RVal_Bits d ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysWideShiftsEntry) := I.

Definition storageKeysWideShiftsPost `{!islaG Sigma} `{!threadG}
    (a b c d : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x14" ↦ᵣ RVal_Bits (bv_shiftl a (BV 64 32)) ∗
   "x5" ↦ᵣ RVal_Bits (bv_shiftl b (BV 64 32)) ∗
   "x15" ↦ᵣ RVal_Bits (bv_shiftl c (BV 64 32)) ∗
   "x10" ↦ᵣ RVal_Bits (bv_shiftl d (BV 64 32)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysWideShiftsPost) := I.

Lemma storage_keys_wide_shifts_correct `{!islaG Sigma} `{!threadG}
    a b c d (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 8 IslaTraces.write_success_61.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15378 (storageKeysWideShiftsPost a b c d P) -∗
  instr_body 0x15368 (storageKeysWideShiftsEntry a b c d P).
Proof. zesu_block. Qed.
Print Assumptions storage_keys_wide_shifts_correct.
