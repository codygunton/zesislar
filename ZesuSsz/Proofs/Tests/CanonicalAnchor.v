Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.PureFactHints.

Definition canonical_anchor_target {Sigma} (R : iProp Sigma) : iProp Sigma :=
  (R ∗ True)%I.
#[local] Instance canonical_anchor_target_unfold :
  LithiumUnfold (@canonical_anchor_target) := I.
Global Typeclasses Opaque canonical_anchor_target.

Section Probe.
Context `{!islaG Sigma} `{!threadG}.
#[local] Instance canonical_anchor_registration (R : iProp Sigma) :
  ZesuCanonicalAnchor R (canonical_anchor_target R) R.
Proof.
  unfold ZesuCanonicalAnchor, ZesuPureFactAnchor, ZesuPureFactIntro,
    canonical_anchor_target. iIntros "HR". iFrame.
Qed.

Lemma canonical_anchor_off (R : iProp Sigma) : R ⊢ R ∗ True.
Proof.
  iIntros "HR". Fail zesu_pure_fact_hints_if_enabled. iFrame.
Qed.
End Probe.

Require Import ZesuSsz.Automation.Switches.CanonicalAnchor.

Section Enabled.
Context `{!islaG Sigma} `{!threadG}.
#[local] Instance canonical_anchor_registration_on (R : iProp Sigma) :
  ZesuCanonicalAnchor R (canonical_anchor_target R) R.
Proof.
  unfold ZesuCanonicalAnchor, ZesuPureFactAnchor, ZesuPureFactIntro,
    canonical_anchor_target. iIntros "HR". iFrame.
Qed.

Lemma canonical_anchor_expanded_on (R : iProp Sigma) : R ⊢ R ∗ True.
Proof. iIntros "HR". zesu_pure_fact_hints_if_enabled. iExact "HR". Qed.

Lemma canonical_anchor_folded_on (R : iProp Sigma) : R ⊢ canonical_anchor_target R.
Proof. iIntros "HR". zesu_pure_fact_hints_if_enabled. iExact "HR". Qed.

Lemma canonical_anchor_wrong_target (R : iProp Sigma) : True.
Proof.
  Fail let registered := constr:(_ : ZesuCanonicalAnchor R (canonical_anchor_target R) R) in
    let evidence := constr:(@zesu_canonical_anchor_intro _ R (canonical_anchor_target R) R registered) in
    let intro := constr:(@zesu_pure_fact_anchor_intro _ (canonical_anchor_target R) R R evidence : ZesuPureFactIntro (R ∗ R)%I R) in idtac.
  exact I.
Qed.
End Enabled.

Print Assumptions canonical_anchor_expanded_on.
Print Assumptions canonical_anchor_folded_on.
Print Assumptions canonical_anchor_wrong_target.
