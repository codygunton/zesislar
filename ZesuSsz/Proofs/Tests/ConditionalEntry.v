Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ResourceGroups.
Require Import isla.riscv64.riscv64.

Lemma entry_fallback_disabled `{!islaG Sigma} (condition : bool)
    (left right : iProp Sigma) :
  (if condition then left else right) -∗ (if condition then left else right).
Proof.
  iStartProof. assert_fails zesu_introduce_entry_resource.
  iIntros "Hresource". iAssumption.
Qed.
Print Assumptions entry_fallback_disabled.

Lemma tuple_dispatch_disabled `{!islaG Sigma} (resource : spec -> iProp Sigma)
    (tail : spec) :
  resource tail -∗ ∃ value : spec *ₗ unit, resource value.1ₗ.
Proof.
  iIntros "Hresource". assert_fails zesu_match_owned_tuple.
  iExists (tail, tt)ₗ. iAssumption.
Qed.
Print Assumptions tuple_dispatch_disabled.

Local Instance : ZesuStepCallOwnership := I.

Lemma conditional_resource_intact `{!islaG Sigma} (condition : bool)
    (left right : iProp Sigma) :
  (if condition then left else right) -∗ (if condition then left else right).
Proof.
  iStartProof. zesu_introduce_entry_resource. iAssumption.
Qed.
Print Assumptions conditional_resource_intact.

Lemma optional_resource_intact `{!islaG Sigma} {A : Type} (choice : option A)
    (some : A -> iProp Sigma) (none : iProp Sigma) :
  (match choice with Some value => some value | None => none end) -∗
  (match choice with Some value => some value | None => none end).
Proof.
  iStartProof. zesu_introduce_entry_resource. iAssumption.
Qed.
Print Assumptions optional_resource_intact.

Lemma conditional_resource_preserves_frame `{!islaG Sigma} (condition : bool)
    (left right frame : iProp Sigma) :
  frame -∗ (if condition then left else right) -∗
    frame ∗ (if condition then left else right).
Proof.
  iIntros "Hframe". zesu_introduce_entry_resource. iFrame.
Qed.
Print Assumptions conditional_resource_preserves_frame.

Definition folded_entry_package `{!islaG Sigma} (resource : iProp Sigma) := resource.
Global Opaque folded_entry_package.

Lemma folded_resource_intact `{!islaG Sigma} (resource : iProp Sigma) :
  folded_entry_package resource -∗ folded_entry_package resource.
Proof.
  iStartProof. zesu_introduce_entry_resource. iAssumption.
Qed.
Print Assumptions folded_resource_intact.

Definition unfolding_entry_package `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ value : bv 64, "x1" ↦ᵣ RVal_Bits value)%I.
Local Instance : LithiumUnfold (@unfolding_entry_package) := I.

Lemma entry_preserves_registered_unfolding `{!islaG Sigma} `{!threadG} :
  unfolding_entry_package -∗ ∃ value : bv 64, "x1" ↦ᵣ RVal_Bits value.
Proof.
  iStartProof. zesu_introduce_entry_resource.
  zesu_introduce_entry_resource. zesu_introduce_entry_resource.
  iExists value. iAssumption.
Qed.
Print Assumptions entry_preserves_registered_unfolding.
