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
