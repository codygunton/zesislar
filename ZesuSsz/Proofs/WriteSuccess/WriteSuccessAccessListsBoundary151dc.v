Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.

Definition writeSuccessAccessListsAt151dcSpec `{!islaG Sigma} `{!threadG}
    (x19 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (entry : writeSuccessAccessEntry)
      (entries processed remaining : list writeSuccessAccessEntry)
      (bytes prefix suffix : list (bv 8))
      (storedIndex savedX22 x22 x27 : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessAccessListsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x19" ↦ᵣ RVal_Bits x19 ∗
    "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (Z.of_nat (length entries))) ∗
    "x11" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (Z.of_nat (length processed))) ∗
    "x22" ↦ᵣ RVal_Bits x22 ∗ "x27" ↦ᵣ RVal_Bits x27 ∗
    base ↦ₘ∗ prefix ∗
    (base + 40 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
    writeSuccessAccessEntriesOwn processed ∗
    writeSuccessAccessEntriesOwn (entry :: remaining) ∗
    writeSuccessAccessListsScratch
      sp base (length entries) storedIndex savedX22 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeSuccessAccessListsEvents sp (entry :: remaining) tail) ∗ P ∗
    writeSuccessAccessListsInvariant sp base entries processed
      (entry :: remaining) bytes prefix suffix ∗
    instr_pre 0x153c0
      (writeSuccessAccessListsLoopExit
        sp base entries bytes tail x19 savedX22 P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAccessListsAt151dcSpec) := I.
