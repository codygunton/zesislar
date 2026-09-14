Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import ZesuSsz.Automation.NatPowerGoals.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsSpec WriteSuccessExactTransactionsLiveSpec
  WriteSuccessExactTransactionsBackEdge.

Definition transactionLiveBackEdgeFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed : list writeSuccessTransaction)
    (transaction : writeSuccessTransaction) (rest : list writeSuccessTransaction)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col writeSuccessTransactionsOtherRegShapes ∗
   base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 120) ↦ₘ? 128 ∗
   (bv_unsigned sp + 256) ↦ₘ? 24 ∗
   (bv_unsigned sp + 1640) ↦ₘ? 256 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessExactTransactionsEvents sp rest tail) ∗
   ⌜transactionLoopSourceFacts sp base transactions processed (transaction :: rest) bytes⌝ ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionLiveBackEdgeFrame) := I.

Lemma transaction_live_source_facts_next sp base transactions processed transaction rest bytes :
  transactionLoopSourceFacts sp base transactions processed (transaction :: rest) bytes ->
  transactionLoopSourceFacts sp base transactions (processed ++ [transaction]) rest bytes.
Proof.
  unfold transactionLoopSourceFacts. intros [Hrelation Hfacts].
  split; last exact Hfacts. rewrite Hrelation -app_assoc. reflexivity.
Qed.

Lemma transactions_live_back_edge_handoff `{!islaG Sigma} `{!threadG}
    sp base transactions processed transaction rest bytes tail (P : iProp Sigma) :
  transactionBackEdgePost sp (Z_to_bv 64 (Z.of_nat (length processed)))
    (Z_to_bv 64 (Z.of_nat (length transactions)))
    (transactionLiveBackEdgeFrame sp base transactions processed transaction rest bytes tail P) -∗
  transactionLiveLoopState sp base transactions (processed ++ [transaction]) rest bytes tail P.
Proof.
  iStartProof. iIntros "Hpost".
  iEval (unfold transactionBackEdgePost, transactionLiveBackEdgeFrame) in "Hpost".
  zesu_open_resource_groups.
  unfold transactionLiveLoopState, transactionLiveScratch.
  zesu_run_nat_safe.
  - rewrite app_length Nat2Z.inj_add /=. bv_solve.
  - apply transaction_live_source_facts_next. assumption.
Qed.
Print Assumptions transactions_live_back_edge_handoff.
