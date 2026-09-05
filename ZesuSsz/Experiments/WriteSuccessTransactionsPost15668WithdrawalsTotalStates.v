From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost1566c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15674WithdrawalsTotal.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPuncturedScratch.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsSpec.

Definition writeSuccessTransactionsPost15668WithdrawalsTotalFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (transactionBase withdrawalBase : Z)
    (transactions : list writeSuccessTransaction) (transactionBytes : list (bv 8))
    (count : nat) (withdrawalBytes : list (bv 8)) (tail : spec)
    (first second : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (transactionBase ↦ₘ∗ transactionBytes ∗
   writeSuccessTransactionsOwn transactions ∗
   writeSuccessTransactionsPuncturedScratch sp transactionBase
     (length transactions) ∗
   writeSuccessTransactionsLoopCarrierPayload sp first second pointer
     (Z_to_bv 64 (Z.of_nat count)) items ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
     (byteListItemEvents (sp - BV 64 32)%bv items
       (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
         (writeSuccessWithdrawalsEvents sp count tail)))) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
   writeSuccessTransactionsCarrierWithdrawalsTotalData P sp pointer
     transactionBase withdrawalBase transactions transactionBytes count
     withdrawalBytes tail first second items ∗ True)%I.

Definition writeSuccessTransactionsPost15668WithdrawalsTotalSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (transactionBase withdrawalBase : Z)
    (transactions : list writeSuccessTransaction) (transactionBytes : list (bv 8))
    (count : nat) (withdrawalBytes : list (bv 8)) (tail : spec)
    (first second : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   writeSuccessTransactionsPost15668WithdrawalsTotalFrame P sp pointer
     transactionBase withdrawalBase transactions transactionBytes count
     withdrawalBytes tail first second items)%I.

Definition writeSuccessTransactionsPost1566cWithdrawalsTotalSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (transactionBase withdrawalBase : Z)
    (transactions : list writeSuccessTransaction) (transactionBytes : list (bv 8))
    (count : nat) (withdrawalBytes : list (bv 8)) (tail : spec)
    (first second : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits first ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   writeSuccessTransactionsPost15668WithdrawalsTotalFrame P sp pointer
     transactionBase withdrawalBase transactions transactionBytes count
     withdrawalBytes tail first second items)%I.

Definition writeSuccessTransactionsPost15670WithdrawalsTotalSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (transactionBase withdrawalBase : Z)
    (transactions : list writeSuccessTransaction) (transactionBytes : list (bv 8))
    (count : nat) (withdrawalBytes : list (bv 8)) (tail : spec)
    (first second : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (∃ ra : bv 64,
   reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ra ∗
   reg_col writeSuccessTransactionsPostOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits first ∗
   "x11" ↦ᵣ RVal_Bits second ∗
   writeSuccessTransactionsPost15668WithdrawalsTotalFrame P sp pointer
     transactionBase withdrawalBase transactions transactionBytes count
     withdrawalBytes tail first second items)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15668WithdrawalsTotalFrame) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15668WithdrawalsTotalSpec) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost1566cWithdrawalsTotalSpec) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15670WithdrawalsTotalSpec) := I.
