Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.RegCollections.
Require Import isla.riscv64.riscv64.

Lemma reg_collection_append_keeps_frame `{!islaG Sigma} `{!threadG}
    left right (P : iProp Sigma) :
  (reg_col left ∗ reg_col right ∗ P ∗ True)%I -∗
  (reg_col (left ++ right) ∗ P ∗ True)%I.
Proof.
  iIntros "(Hleft & Hright & HP & _)". iFrame "HP".
  iApply (zesu_reg_col_append with "[$Hleft $Hright]").
Qed.
Print Assumptions reg_collection_append_keeps_frame.
