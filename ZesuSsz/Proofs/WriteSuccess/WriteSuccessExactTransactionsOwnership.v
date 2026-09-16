Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma transactions_own_app `{!islaG Sigma} prefix suffix :
  writeSuccessTransactionsOwn (prefix ++ suffix) ⊣⊢
  writeSuccessTransactionsOwn prefix ∗ writeSuccessTransactionsOwn suffix ∗ True.
Proof.
  induction prefix as [|transaction prefix IH]; simpl.
  - by rewrite !bi.True_sep !bi.sep_True.
  - rewrite IH. by rewrite !bi.sep_assoc !bi.sep_True.
Qed.
Print Assumptions transactions_own_app.
