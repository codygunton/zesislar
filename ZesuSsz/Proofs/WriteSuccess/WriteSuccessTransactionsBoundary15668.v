Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

(**
   The transaction loop and the outer writer meet at [0x15668].  The outer
   writer reads the lower 104 bytes of the frame, the 1776-byte scratch
   region, and the 104-byte saved-register region.
*)
Definition writeSuccessTransactionsPostFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (bytes : list (bv 8)) (tail : spec) : iProp Sigma :=
  (writeSuccessTransactionsLoopExit sp base transactions bytes tail
     ((bv_unsigned sp) ↦ₘ? 104 ∗
      (bv_unsigned sp + 1896) ↦ₘ? 104 ∗
      ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
      ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
      ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
      ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPostFrame) := I.

Definition writeSuccessTransactionsPostAt15668Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
      (bytes : list (bv 8)) (tail : spec),
    writeSuccessTransactionsPostFrame P sp base transactions bytes tail)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPostAt15668Spec) := I.

Lemma write_success_transactions_post_handoff
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (bytes : list (bv 8)) (tail : spec) :
  writeSuccessTransactionsLoopExit sp base transactions bytes tail
      ((bv_unsigned sp) ↦ₘ? 104 ∗
       (bv_unsigned sp + 1896) ↦ₘ? 104 ∗
       ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
       ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
       ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
       ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P) -∗
  writeSuccessTransactionsPostAt15668Spec P.
Proof.
  iIntros "Hexit".
  iExists sp, base, transactions, bytes, tail.
  iFrame.
Qed.
