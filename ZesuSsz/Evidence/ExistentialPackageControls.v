Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ResourceGroups.
Require Import ZesuSsz.Automation.All.

Section existential_package_controls.
Context `{!islaG Sigma} `{!threadG}.

Definition nested_control_package (P : iProp Sigma) : iProp Sigma :=
  (∃ a : bv 64, ∃ b : bv 64, ∃ c : bv 64, ∃ d : bv 64,
    "x10" ↦ᵣ RVal_Bits a ∗ "x11" ↦ᵣ RVal_Bits b ∗
    "x12" ↦ᵣ RVal_Bits c ∗ "x13" ↦ᵣ RVal_Bits d ∗ P)%I.
#[local] Instance nested_control_package_unfold :
  LithiumUnfold (@nested_control_package) := I.
Local Typeclasses Opaque nested_control_package.

Lemma nested_depth_four_preserves (P K : iProp Sigma) :
  (nested_control_package P ∗ K) -∗
  (∃ a : bv 64, ∃ b : bv 64, ∃ c : bv 64, ∃ d : bv 64,
    "x10" ↦ᵣ RVal_Bits a ∗ "x11" ↦ᵣ RVal_Bits b ∗
    "x12" ↦ᵣ RVal_Bits c ∗ "x13" ↦ᵣ RVal_Bits d ∗ P) ∗ K.
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
