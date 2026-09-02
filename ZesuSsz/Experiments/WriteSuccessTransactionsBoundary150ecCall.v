From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150ec.

Definition writeSuccessTransactions150ecCallFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessTransactionsOwn processed ∗
   writeSuccessTransactionOwn transaction ∗
   writeSuccessTransactionsOwn remaining ∗ P ∗
   writeSuccessTransactionsInvariant sp base transactions processed
     (transaction :: remaining) bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExit
       sp base transactions bytes tail P) ∗ True)%I.

Global Typeclasses Opaque writeSuccessTransactions150ecCallFrame.

Definition writeSuccessTransactionsAt150ecCallSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x100e8) ∗
    writeSuccessTransactionsMachine150e8Rest
      sp base transactions processed transaction ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 1)
        (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
          (writeSuccessTransactionsEvents sp remaining tail))) ∗
    writeSuccessTransactions150ecCallFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt150ecCallSpec) := I.
