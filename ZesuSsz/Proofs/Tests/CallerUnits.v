Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.

Lemma test_caller_group_equivalence {Sigma : gFunctors} (A B C D : iProp Sigma) :
  A ∗ (B ∗ C ∗ D ∗ True) ∗ True ⊣⊢ A ∗ B ∗ C ∗ D ∗ True.
Proof. by rewrite -!bi.sep_assoc !bi.True_sep. Qed.
Print Assumptions test_caller_group_equivalence.
