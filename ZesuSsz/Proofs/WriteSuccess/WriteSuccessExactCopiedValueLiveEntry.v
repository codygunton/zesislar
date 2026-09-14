Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import ZesuSsz.Automation.NatPowerGoals.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsSpec WriteSuccessExactValueSpec
  WriteSuccessExactTransactionsLiveSpec WriteSuccessExactValueLiveFacts.

Definition writeSuccessExactCopiedValueLiveFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes sourceBytes object : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (bv_unsigned sp ↦ₘ? 8 ∗ writeSuccessExactCopiedTailWords sp object ∗ (bv_unsigned sp + 120) ↦ₘ? 160 ∗
   (bv_unsigned sp + 312) ↦ₘ∗ sourceBytes ∗ (bv_unsigned sp + 1624) ↦ₘ? 272 ∗
   base ↦ₘ∗ transactionBytes ∗ writeSuccessTransactionsOwn transactions ∗
   ⌜transactionLoopSourceFacts sp base transactions [] transactions transactionBytes⌝ ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@writeSuccessExactCopiedValueLiveFrame) := I.

Definition writeSuccessExactCopiedValueLiveCaller `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) (payload sourceBytes object : list (bv 8))
    (P : iProp Sigma) : iProp Sigma :=
  (bv_unsigned sp ↦ₘ? 8 ∗ writeSuccessExactCopiedTailWords sp object ∗
   (bv_unsigned sp + 312) ↦ₘ∗ sourceBytes ∗ writeSuccessExactValueMemory sp values ∗
   (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
   bv_unsigned (writeSuccessExactValueWord values 4) ↦ₘ∗ payload ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@writeSuccessExactCopiedValueLiveCaller) := I.

Lemma write_success_exact_copied_value_live_entry `{!islaG Sigma} `{!threadG}
    sp base transactions transactionBytes sourceBytes object values payload tail (P : iProp Sigma) :
  default (BV 64 0) (take 69 values !! 7%nat) = Z_to_bv 64 base ->
  default (BV 64 0) (take 69 values !! 8%nat) =
    Z_to_bv 64 (Z.of_nat (length transactions)) ->
  writeSuccessExactValuePost sp values payload
    (writeSuccessExactTransactionsEvents sp transactions tail)
    (writeSuccessExactCopiedValueLiveFrame sp base transactions transactionBytes sourceBytes object P) -∗
  transactionLiveLoopState sp base transactions [] transactions transactionBytes tail
    (writeSuccessExactCopiedValueLiveCaller sp values payload sourceBytes object P).
Proof.
  intros Hbase Hcount. iStartProof. iIntros "Hpost".
  iEval (unfold writeSuccessExactValuePost, writeSuccessExactValueMemory, writeSuccessExactCopiedValueLiveFrame) in "Hpost".
  iEval (unfold writeSuccessExactCopiedTailWords) in "Hpost".
  zesu_open_resource_groups.
  rename select (transactionLoopSourceFacts _ _ _ _ _ _) into Hsource.
  pose proof (write_success_exact_value_live_stack_bound _ _ _ _ _ _ Hsource) as HstackHigh.
  unfold transactionLiveLoopState, transactionLiveScratch, writeSuccessExactCopiedValueLiveCaller.
  zesu_run_nat_safe.
  all: try (clear -HstackHigh; lia).

Qed.
Print Assumptions write_success_exact_copied_value_live_entry.
