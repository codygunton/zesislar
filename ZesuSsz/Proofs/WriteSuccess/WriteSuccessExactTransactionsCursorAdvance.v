Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsLiveSpec.

Lemma transactions_live_cursor_advance sp base transactions processed transaction rest bytes :
  transactionLoopSourceFacts sp base transactions processed (transaction :: rest) bytes ->
  transactionLoopSourceFacts sp base transactions (processed ++ [transaction]) rest bytes /\
  (Z_to_bv 64 (Z.of_nat (length processed)) + BV 64 1)%bv =
    Z_to_bv 64 (Z.of_nat (length (processed ++ [transaction]))).
Proof.
  intros Hfacts. split.
  - destruct Hfacts as [Hrelation Hfacts]. split; [|exact Hfacts].
    rewrite Hrelation -app_assoc. reflexivity.
  - clear Hfacts. rewrite app_length /= Nat2Z.inj_add. bv_solve.
Qed.
Print Assumptions transactions_live_cursor_advance.
