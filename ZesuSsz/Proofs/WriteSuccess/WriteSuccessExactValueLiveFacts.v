Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessExactTransactionsLiveSpec.

Lemma write_success_exact_value_live_stack_bound sp base transactions processed remaining bytes :
  transactionLoopSourceFacts sp base transactions processed remaining bytes ->
  bv_unsigned sp + 1896 < 0x40000000.
Proof.
  intros (_ & _ & _ & _ & _ & _ & Hhigh & _). exact Hhigh.
Qed.
Print Assumptions write_success_exact_value_live_stack_bound.
