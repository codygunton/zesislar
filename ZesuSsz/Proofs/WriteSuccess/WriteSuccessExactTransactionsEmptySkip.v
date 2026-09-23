Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.WordArrays.
Require Import ZesuSsz.Automation.Resources.
Import WordMatching.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLiveSpec
  WriteSuccessExactTransactionsBranch.
From IslaTraces.write_success_28 Require Import instrs.

Definition transactionLiveEmptyFrame `{!islaG Sigma} `{!threadG}
    (sp base : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col writeSuccessTransactionsOtherRegShapes ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   transactionLiveScratch sp (bv_unsigned base) 0 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionLiveEmptyFrame) := I.

Definition transactionLiveEmptyEntry `{!islaG Sigma} `{!threadG}
    (sp base : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  exactTransactionsBranchState (BV 64 0) (BV 64 0)
    (transactionLiveEmptyFrame sp base tail P).
Global Instance : LithiumUnfold (@transactionLiveEmptyEntry) := I.

Lemma transactions_live_empty_skip_correct `{!islaG Sigma} `{!threadG}
    (sp base : bv 64) tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_28.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15668 (transactionLiveLoopExit sp (bv_unsigned base) [] [] tail P) -∗
  instr_body 0x14f04 (transactionLiveEmptyEntry sp base tail P).
Proof. move => *. zesu_block. Qed.
Print Assumptions transactions_live_empty_skip_correct.
