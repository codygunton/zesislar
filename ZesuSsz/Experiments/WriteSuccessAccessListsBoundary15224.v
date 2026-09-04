From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsSpec.

Definition writeSuccessAccessListsAt15224Spec `{!islaG Sigma} `{!threadG}
    (x19 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (entry : writeSuccessAccessEntry)
      (entries processed remaining : list writeSuccessAccessEntry)
      (bytes prefix suffix : list (bv 8))
      (savedX22 x10 x11 : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessAccessListsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits x10 ∗
    "x19" ↦ᵣ RVal_Bits x19 ∗
    "x11" ↦ᵣ RVal_Bits x11 ∗
    "x22" ↦ᵣ RVal_Bits (writeSuccessAccessEntryWord entry 0) ∗
    "x27" ↦ᵣ RVal_Bits (writeSuccessAccessEntryWord entry 8) ∗
    base ↦ₘ∗ prefix ∗
    (base + 40 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
    writeSuccessAccessEntriesOwn processed ∗
    writeSuccessAccessEntriesOwn (entry :: remaining) ∗
    writeSuccessAccessListsCopiedScratch
      sp base (length entries) (length processed) entry savedX22 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeSuccessAccessListsPhaseEvents
        AccessListsStorage sp entry remaining tail) ∗ P ∗
    writeSuccessAccessListsInvariant
      sp base entries processed (entry :: remaining) bytes prefix suffix ∗
    instr_pre 0x153c0
      (writeSuccessAccessListsLoopExit
        sp base entries bytes tail x19 savedX22 P) ∗
    True)%I.

Global Instance : LithiumUnfold (@writeSuccessAccessListsAt15224Spec) := I.
