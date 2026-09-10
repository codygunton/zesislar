Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150ecCall.

Definition writeSuccessTransactionsAt10190Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x150f0) ∗
    writeSuccessTransactionsMachine150e8Rest
      sp base transactions processed transaction ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 1)
        (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
          (writeSuccessTransactionsEvents sp remaining tail))) ∗
    writeSuccessTransactions150ecCallFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt10190Spec) := I.
