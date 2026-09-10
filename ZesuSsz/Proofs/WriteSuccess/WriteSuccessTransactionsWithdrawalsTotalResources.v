Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsSpec.

Definition writeSuccessTransactionsPost15678PreservedScratch
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (transactionBase : Z) (transactionTotal : nat)
    (first second : bv 64) (items : list ByteListItem) : iProp Sigma :=
  ((bv_unsigned sp - 80) ↦ₘ? 32 ∗
   (bv_unsigned sp - 48) ↦ₘ? 32 ∗
   bv_unsigned sp ↦ₘ? 104 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 transactionBase ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat transactionTotal) ∗
   (bv_unsigned sp + 120) ↦ₘ? 984 ∗
   (bv_unsigned sp + 1104) ↦ₘ first ∗
   (bv_unsigned sp + 1112) ↦ₘ second ∗
   (bv_unsigned sp + 1136) ↦ₘ? 608 ∗
   (bv_unsigned sp + 1792) ↦ₘ? 104 ∗
   byteListItemResources (bv_unsigned first) items ∗
   ⌜writeSuccessTransactionsPost15674ByteListFacts sp first second items⌝ ∗
   True)%I.

Definition writeSuccessTransactionsWithdrawalsTotalResources
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (count : nat)
    (bytes : list (bv 8)) (tail : spec) : iProp Sigma :=
  (bv_unsigned pointer ↦ₘ∗ bytes ∗
   ⌜bv_unsigned pointer = base⌝ ∗
   ⌜length bytes = (48 * count)%nat⌝ ∗
   ⌜(count < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
   ⌜0x20000000 <= base⌝ ∗
   ⌜base + Z.of_nat (length bytes) < 0x40000000⌝ ∗
   instr_pre 0x156e8
     (writeSuccessWithdrawalsLoopExit sp base count bytes tail P) ∗
   P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15678PreservedScratch) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWithdrawalsTotalResources) := I.
