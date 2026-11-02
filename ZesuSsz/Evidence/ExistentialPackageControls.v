Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ResourceGroups.

Section existential_package_controls.
Context `{!islaG Sigma} `{!threadG}.

Definition nested_control_package (P : iProp Sigma) : iProp Sigma :=
  (∃ a : nat, ∃ b : bool, ∃ c : list nat, ∃ d : Z, P)%I.
#[local] Instance nested_control_package_unfold :
  LithiumUnfold (@nested_control_package) := I.

Lemma nested_depth_four_preserves (P K : iProp Sigma) :
  (nested_control_package P ∗ K) -∗ P ∗ K.
Proof.
  iIntros "H".
  zesu_open_nested_existential_packages.
  iFrame.
Qed.

Lemma nested_separation_preserves (P Q K : iProp Sigma) :
  ((P ∗ (∃ a : nat, ∃ b : bool, Q)) ∗ K) -∗ P ∗ Q ∗ K.
Proof.
  iIntros "H".
  zesu_open_nested_existential_packages.
  iFrame.
Qed.

Lemma package_refuses_no_existential (P K : iProp Sigma) :
  (P ∗ K) -∗ P ∗ K.
Proof.
  iIntros "H".
  Fail zesu_open_nested_existential_packages.
  iExact "H".
Qed.

Lemma package_refuses_universal (P K : iProp Sigma) :
  ((∀ a : nat, P) ∗ K) -∗ (∀ a : nat, P) ∗ K.
Proof.
  iIntros "H".
  Fail zesu_open_nested_existential_packages.
  iExact "H".
Qed.

Lemma package_refuses_wand (P Q K : iProp Sigma) :
  (((∃ a : nat, P) -∗ Q) ∗ K) -∗ ((∃ a : nat, P) -∗ Q) ∗ K.
Proof.
  iIntros "H".
  Fail zesu_open_nested_existential_packages.
  iExact "H".
Qed.

Lemma package_refuses_wrong_goal (P K : iProp Sigma) :
  ((∃ a : nat, P) ∗ K) -∗ P ∗ K.
Proof.
  iIntros "H".
  Fail ResourceGroups.zesu_open_requested_struct_sys_package.
  zesu_open_nested_existential_packages.
  iFrame.
Qed.
End existential_package_controls.

Print Assumptions nested_depth_four_preserves.
Print Assumptions nested_separation_preserves.
Print Assumptions package_refuses_no_existential.
Print Assumptions package_refuses_universal.
Print Assumptions package_refuses_wand.
Print Assumptions package_refuses_wrong_goal.
