From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierBoundary151b4.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary151c4.

(* The bytes encoder returns at 0x151c4.  It preserves the carrier scratch
   and the branch-independent event resources from 0x151b4. *)
Definition writeSuccessTransactions151c4CarrierScratch
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  writeSuccessTransactions151b4CarrierScratch
    sp base total processed transaction first second third fourth items.

Global Instance : LithiumUnfold
    (@writeSuccessTransactions151c4CarrierScratch) := I.
Global Typeclasses Opaque writeSuccessTransactions151c4CarrierScratch.

Definition writeSuccessTransactions151c4CarrierMachine `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed : list writeSuccessTransaction)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactions151c4OtherRegShapes ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x151c4) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
   "x10" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
   "x11" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 200) ∗
   "x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 48) ∗
   "x19" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 224) ∗
   "x20" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 56) ∗
   "x21" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 72) ∗
   "x22" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 200) ∗
   "x23" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 24) ∗
   "x24" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 8) ∗
   "x25" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 0) ∗
   "x26" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 184) ∗
   "x27" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32)) ∗
   writeSuccessTransactions151c4CarrierScratch
     sp base (length transactions) (length processed) transaction
     first second third fourth items ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactions151c4CarrierMachine) := I.

Lemma write_success_transactions_151c4_carrier_scratch_pack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions151b4CarrierScratch
    sp base total processed transaction first second third fourth items -∗
  writeSuccessTransactions151c4CarrierScratch
    sp base total processed transaction first second third fourth items.
Proof.
  iIntros "Hscratch".
  iExact "Hscratch".
Qed.

Lemma write_success_transactions_151c4_carrier_scratch_unpack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions151c4CarrierScratch
    sp base total processed transaction first second third fourth items -∗
  writeSuccessTransactions151b4CarrierScratch
    sp base total processed transaction first second third fourth items.
Proof.
  iIntros "Hscratch".
  iExact "Hscratch".
Qed.
