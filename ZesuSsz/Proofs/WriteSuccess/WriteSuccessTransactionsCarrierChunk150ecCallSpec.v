Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState150ec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierCall150ec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.


Definition writeSuccessTransactionsAt150ecCarrierCallBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col (zip_with (fun register value => (KindReg register, ExactShape value))
     writeSuccessTransactions150ecCallerRegisters
     (writeSuccessTransactions150ecCallerValues transaction)) ∗
   reg_col (zip_with (fun register value => (KindReg register, ExactShape value))
     ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
      "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]
     (writeSuccessTransactions150ecSavedValues transaction)) ∗
   "x10" ↦ᵣ RVal_Bits (bv_add sp (BV 64 1744)) ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x100e8) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace
     (writeOutputEventsAny (sp + BV 64 1744)%bv (BV 64 1)
       (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
         (writeSuccessTransactionsEvents sp remaining
           (writeSuccessTransactionsCarrierOutputTail sp items tail)))) ∗
   writeSuccessTransactions150ecCarrierCallFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail
     first second third fourth items ∗ True)%I.

Definition writeSuccessTransactionsAt10190CarrierCallBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col (zip_with (fun register value => (KindReg register, ExactShape value))
     writeSuccessTransactions150ecCallerRegisters
     (writeSuccessTransactions150ecCallerValues transaction)) ∗
   reg_col (zip_with (fun register value => (KindReg register, ExactShape value))
     ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
      "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]
     (writeSuccessTransactions150ecSavedValues transaction)) ∗
   "x10" ↦ᵣ RVal_Bits (bv_add sp (BV 64 1744)) ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x150f0) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace
     (writeOutputEventsAny (sp + BV 64 1744)%bv (BV 64 1)
       (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
         (writeSuccessTransactionsEvents sp remaining
           (writeSuccessTransactionsCarrierOutputTail sp items tail)))) ∗
   writeSuccessTransactions150ecCarrierCallFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail
     first second third fourth items ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt150ecCarrierCallBlock) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt10190CarrierCallBlock) := I.
