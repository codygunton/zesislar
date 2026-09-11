Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions10190MachineAdapter.

Import ListNotations.

Definition writeSuccessTransactions10190OpaqueMachineFrame
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z)
    (transaction : writeSuccessTransaction)
    (transactions processed : list writeSuccessTransaction) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x150f0) ∗
   writeSuccessTransactionsMachine150e8Rest
     sp base transactions processed transaction ∗ True)%I.

Lemma write_success_transactions_10190_machine_frame_pack
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z)
    (transaction : writeSuccessTransaction)
    (transactions processed : list writeSuccessTransaction) :
  reg_col zesu_ram_sys_regs -∗
  "x1" ↦ᵣ RVal_Bits (BV 64 0x150f0) -∗
  writeSuccessTransactionsMachine150e8Rest
    sp base transactions processed transaction -∗
  writeSuccessTransactions10190OpaqueMachineFrame
    sp base transaction transactions processed.
Proof.
  rewrite /writeSuccessTransactions10190OpaqueMachineFrame.
  iIntros "Hsys H1 Hmachine". iFrame.
Qed.

Lemma write_success_transactions_10190_machine_frame_unpack
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z)
    (transaction : writeSuccessTransaction)
    (transactions processed : list writeSuccessTransaction) :
  writeSuccessTransactions10190OpaqueMachineFrame
    sp base transaction transactions processed -∗
  reg_col zesu_ram_sys_regs ∗
  "x1" ↦ᵣ RVal_Bits (BV 64 0x150f0) ∗
  writeSuccessTransactionsMachine150e8Rest
    sp base transactions processed transaction ∗ True.
Proof.
  rewrite /writeSuccessTransactions10190OpaqueMachineFrame.
  iIntros "Hmachine". iExact "Hmachine".
Qed.

Global Typeclasses Opaque writeSuccessTransactions10190OpaqueMachineFrame.
Global Opaque writeSuccessTransactions10190OpaqueMachineFrame.

Definition writeSuccessTransactions10190ReturnBuilder
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z)
    (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (tail : spec) : iProp Sigma :=
  (writeSuccessTransactions10190MachineFrame
      sp base transaction transactions processed -∗
   instr_pre 0x150f0
     (zesu_c_call_ret 0
       [RVal_Bits (writeSuccessTransactionWord transaction 192);
        RVal_Bits (writeSuccessTransactionWord transaction 16);
        RVal_Bits (writeSuccessTransactionWord transaction 48);
        RVal_Bits (writeSuccessTransactionWord transaction 224);
        RVal_Bits (writeSuccessTransactionWord transaction 56);
        RVal_Bits (writeSuccessTransactionWord transaction 72);
        RVal_Bits (writeSuccessTransactionWord transaction 200);
        RVal_Bits (writeSuccessTransactionWord transaction 24);
        RVal_Bits (writeSuccessTransactionWord transaction 8);
        RVal_Bits (writeSuccessTransactionWord transaction 0);
        RVal_Bits (writeSuccessTransactionWord transaction 184);
        RVal_Bits
          (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32))]
       (BV 64 0x150f0) sp
       (fun _ =>
         mmio_range 0x2401a0c0 16 ∗
         spec_trace
           (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
             (writeSuccessTransactionsEvents sp remaining tail)) ∗ True)))%I.

Global Typeclasses Opaque writeSuccessTransactions10190ReturnBuilder.

Definition writeSuccessTransactionsAt10190PreparedBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (writeSuccessTransactions10190OpaqueMachineFrame
      sp base transaction transactions processed ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp < 0x40000000⌝ ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
     (writeOutputEventsAny (sp + BV 64 1744)%bv (BV 64 1)
       (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
         (writeSuccessTransactionsEvents sp remaining tail))) ∗
   writeSuccessTransactions10190ReturnBuilder
     sp base transaction transactions processed remaining tail ∗
   True)%I.

Lemma write_success_transactions_10190_prepared_pack
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactions10190OpaqueMachineFrame
      sp base transaction transactions processed -∗
  ⌜bv_unsigned sp `mod` 16 = 0⌝ -∗
  ⌜0x20000000 <= bv_unsigned sp⌝ -∗
  ⌜bv_unsigned sp < 0x40000000⌝ -∗
  mmio_range 0x2401a0c0 16 -∗
  spec_trace
    (writeOutputEventsAny (sp + BV 64 1744)%bv (BV 64 1)
      (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
        (writeSuccessTransactionsEvents sp remaining tail))) -∗
  writeSuccessTransactions10190ReturnBuilder
    sp base transaction transactions processed remaining tail -∗
  writeSuccessTransactionsAt10190PreparedBlock P sp base transaction
    transactions processed remaining bytes prefix suffix tail.
Proof.
  rewrite /writeSuccessTransactionsAt10190PreparedBlock.
  iIntros "Hmachine %Halign %Hmin %Hmax Hmmio Htrace Hreturn".
  iFrame.
  repeat iSplit; iPureIntro; assumption.
Qed.

Lemma write_success_transactions_10190_prepared_unpack
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactionsAt10190PreparedBlock P sp base transaction
    transactions processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactions10190OpaqueMachineFrame
      sp base transaction transactions processed ∗
  ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
  ⌜0x20000000 <= bv_unsigned sp⌝ ∗
  ⌜bv_unsigned sp < 0x40000000⌝ ∗
  mmio_range 0x2401a0c0 16 ∗
  spec_trace
    (writeOutputEventsAny (sp + BV 64 1744)%bv (BV 64 1)
      (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
        (writeSuccessTransactionsEvents sp remaining tail))) ∗
  writeSuccessTransactions10190ReturnBuilder
    sp base transaction transactions processed remaining tail ∗ True.
Proof.
  rewrite /writeSuccessTransactionsAt10190PreparedBlock.
  iIntros "Hprepared". iExact "Hprepared".
Qed.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt10190PreparedBlock) := I.
Global Opaque writeSuccessTransactionsAt10190PreparedBlock.
