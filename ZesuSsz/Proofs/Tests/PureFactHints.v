Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Section registered.
Context `{!islaG Sigma} `{!threadG}.
Context (P : Prop) (target source : iProp Sigma).
Context (HP : SimplAnd P True) (Hintro : ZesuPureFactIntro target source).

Lemma pure_hint_off : P -> P.
Proof. intros Howned. Fail zesu_pure_fact_hints_if_enabled. exact Howned. Qed.
Lemma intro_hint_off : source -∗ target.
Proof using Hintro Sigma source target.
  iStartProof. iIntros "H". Fail zesu_pure_fact_hints_if_enabled.
  iApply (@zesu_pure_fact_intro _ target source Hintro). iExact "H".
Qed.
End registered.


Section anchor_off.
Context {Sigma} (A : Type) (target : iProp Sigma) (R : A -> iProp Sigma).
Context (Anchor : forall value, @ZesuPureFactAnchor Sigma target (R value) (R value)).
#[local] Existing Instance Anchor.
Lemma anchor_hint_off (value : A) : R value -∗ target.
Proof using Anchor Sigma A target R.
  iStartProof. iIntros "HR". Fail zesu_pure_fact_hints_if_enabled.
  iApply (@zesu_pure_fact_intro Sigma target (R value)
    (@zesu_pure_fact_anchor_intro Sigma target (R value) (R value) (Anchor value))).
  iExact "HR".
Qed.
End anchor_off.

Require Import ZesuSsz.Automation.Switches.PureFactHints.

Section enabled.
Context `{!islaG Sigma} `{!threadG}.
Context (P : Prop) (target source : iProp Sigma).
Context (HP : SimplAnd P True) (Hintro : ZesuPureFactIntro target source).
#[local] Existing Instance HP.
#[local] Existing Instance Hintro.
Lemma pure_hint_on : P.
Proof using HP P. zesu_pure_fact_hints_if_enabled. Qed.
Lemma intro_hint_on : source -∗ target.
Proof using Hintro Sigma source target.
  iStartProof. iIntros "H". zesu_pure_fact_hints_if_enabled. iExact "H".
Qed.
Lemma unrelated_hint_on (Q : Prop) : Q -> Q.
Proof. intros Howned. Fail zesu_pure_fact_hints_if_enabled. exact Howned. Qed.
Lemma pure_hint_iris_conjunction (Q : Prop) (Howned : Q) (n : nat) :
  ⊢ (⌜P /\ Q /\ n = n⌝ : iProp Sigma).
Proof using HP P Sigma.
  iStartProof. zesu_pure_fact_hints_if_enabled.
Qed.
Lemma pure_hint_iris_unregistered (Q : Prop) (Howned : Q) :
  ⊢ (⌜Q⌝ : iProp Sigma).
Proof using Sigma.
  iStartProof. Fail zesu_pure_fact_hints_if_enabled.
  iPureIntro. exact Howned.
Qed.
End enabled.

Section indexed.
Context {Sigma} (A : Type) (P : A -> Prop) (R T : A -> iProp Sigma).
Context (Intro : forall value,
  @ZesuPureFactIntro Sigma (T value) (⌜P value⌝ ∗ R value)%I).
#[local] Existing Instance Intro.
Lemma intro_hint_indexed (value : A) : R value -∗ ⌜P value⌝ -∗ T value.
Proof using Intro Sigma A P R T.
  iStartProof. iIntros "HR HP".
  zesu_pure_fact_hints_if_enabled.
  iFrame.
Qed.
End indexed.
Print Assumptions pure_hint_on.
Print Assumptions intro_hint_on.
Print Assumptions intro_hint_indexed.

Section owned_source.
Context {Sigma} (A : Type) (target : iProp Sigma) (R : A -> iProp Sigma).
Context (Intro : forall value, @ZesuPureFactIntro Sigma target (R value)).
#[local] Existing Instance Intro.
Lemma intro_hint_owned_source (value : A) : R value -∗ target.
Proof using Intro Sigma A target R.
  iStartProof. iIntros "Hsource".
  zesu_pure_fact_hints_if_enabled. iExact "Hsource".
Qed.
End owned_source.
Print Assumptions intro_hint_owned_source.

Section anchored_source.
Context {Sigma} (A : Type) (target : iProp Sigma) (P : A -> Prop) (R : A -> iProp Sigma).
Context (Anchor : forall value,
  @ZesuPureFactAnchor Sigma target (R value) (⌜P value⌝ ∗ R value)%I).
#[local] Existing Instance Anchor.
Lemma anchor_hint_indexed (value : A) : R value -∗ ⌜P value⌝ -∗ target.
Proof using Anchor Sigma A target P R.
  iStartProof. iIntros "HR HP".
  zesu_pure_fact_hints_if_enabled.
  iSplitL "HP"; [iExact "HP" | iExact "HR"].
Qed.
Lemma anchor_hint_unregistered (unrelated : iProp Sigma) (value : A) :
  R value -∗ unrelated -∗ unrelated.
Proof.
  iStartProof. iIntros "HR HU".
  Fail zesu_pure_fact_hints_if_enabled. iExact "HU".
Qed.
End anchored_source.
Print Assumptions anchor_hint_off.
Print Assumptions anchor_hint_indexed.
