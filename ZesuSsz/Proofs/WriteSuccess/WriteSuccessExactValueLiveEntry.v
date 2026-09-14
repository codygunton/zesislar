Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import ZesuSsz.Automation.NatPowerGoals.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsSpec WriteSuccessExactValueSpec
  WriteSuccessExactTransactionsLiveSpec WriteSuccessExactValueLiveFacts.

Definition writeSuccessExactValueLiveFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes sourceBytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (bv_unsigned sp ↦ₘ? 104 ∗ (bv_unsigned sp + 120) ↦ₘ? 192 ∗
   (bv_unsigned sp + 312) ↦ₘ∗ sourceBytes ∗ (bv_unsigned sp + 1624) ↦ₘ? 272 ∗
   base ↦ₘ∗ transactionBytes ∗ writeSuccessTransactionsOwn transactions ∗
   ⌜transactionLoopSourceFacts sp base transactions [] transactions transactionBytes⌝ ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@writeSuccessExactValueLiveFrame) := I.

Definition writeSuccessExactValueLiveCaller `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) (payload sourceBytes : list (bv 8))
    (P : iProp Sigma) : iProp Sigma :=
  (bv_unsigned sp ↦ₘ? 104 ∗ (bv_unsigned sp + 280) ↦ₘ? 32 ∗
   (bv_unsigned sp + 312) ↦ₘ∗ sourceBytes ∗ writeSuccessExactValueMemory sp values ∗
   (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
   bv_unsigned (writeSuccessExactValueWord values 4) ↦ₘ∗ payload ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@writeSuccessExactValueLiveCaller) := I.

Lemma write_success_exact_value_live_entry `{!islaG Sigma} `{!threadG}
    sp base transactions transactionBytes sourceBytes values payload tail (P : iProp Sigma) :
  default (BV 64 0) (take 69 values !! 7%nat) = Z_to_bv 64 base ->
  default (BV 64 0) (take 69 values !! 8%nat) =
    Z_to_bv 64 (Z.of_nat (length transactions)) ->
  writeSuccessExactValuePost sp values payload
    (writeSuccessExactTransactionsEvents sp transactions tail)
    (writeSuccessExactValueLiveFrame sp base transactions transactionBytes sourceBytes P) -∗
  transactionLiveLoopState sp base transactions [] transactions transactionBytes tail
    (writeSuccessExactValueLiveCaller sp values payload sourceBytes P).
Proof.
  intros Hbase Hcount. iStartProof. iIntros "Hpost".
  iEval (unfold writeSuccessExactValuePost, writeSuccessExactValueMemory, writeSuccessExactValueLiveFrame) in "Hpost".
  zesu_open_resource_groups.
  rename select (transactionLoopSourceFacts _ _ _ _ _ _) into Hsource.
  pose proof (write_success_exact_value_live_stack_bound _ _ _ _ _ _ Hsource) as HstackHigh.
  unfold transactionLiveLoopState, transactionLiveScratch, writeSuccessExactValueLiveCaller.
  zesu_run_nat_safe.
  all: try (clear -HstackHigh; lia).

Qed.
Print Assumptions write_success_exact_value_live_entry.
