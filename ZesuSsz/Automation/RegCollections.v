Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma zesu_reg_col_append `{!islaG Sigma} `{!threadG} left right :
  (reg_col left ∗ reg_col right ∗ True)%I -∗ reg_col (left ++ right).
Proof.
  rewrite /reg_col big_sepL_app. iIntros "[Hleft [Hright _]]". iFrame.
Qed.
Print Assumptions zesu_reg_col_append.
