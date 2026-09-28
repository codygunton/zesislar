Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ConjunctMatch.
Require Import ZesuSsz.Automation.Switches.ConjunctMatch.
Require Import isla.riscv64.riscv64.

Section conjunct_match_tests.
Context `{!islaG Sigma} `{!threadG}.

Lemma conjunct_match_named (P Q : iProp Sigma) : P -∗ Q -∗ P ∗ Q.
Proof.
  iIntros "HP HQ".
  zesu_conjunct_match_if_enabled.
  iExact "HQ".
Qed.

Lemma conjunct_match_anonymous (P Q : iProp Sigma) : P -∗ Q -∗ P ∗ Q ∗ True.
Proof.
  iIntros "? ?".
  repeat zesu_conjunct_match_if_enabled.
  done.
Qed.

Lemma conjunct_match_associated (P Q R : iProp Sigma) :
  P -∗ Q -∗ R -∗ (P ∗ Q) ∗ R.
Proof.
  iIntros "HP HQ HR".
  repeat zesu_conjunct_match_if_enabled.
  iExact "HR".
Qed.

Lemma conjunct_match_composite (P Q R : iProp Sigma) :
  (P ∗ Q) -∗ R -∗ (P ∗ Q) ∗ R.
Proof.
  iIntros "Hpair HR".
  zesu_conjunct_match_if_enabled.
  iExact "HR".
Qed.

Lemma conjunct_match_existing_name (P Q : iProp Sigma) : P -∗ Q -∗ P ∗ Q.
Proof.
  iIntros "HpwConjunct HQ".
  zesu_conjunct_match_if_enabled.
  iExact "HQ".
Qed.

Lemma conjunct_match_keeps_owned_bundle (P Q : iProp Sigma) :
  (P ∗ Q) -∗ P ∗ Q.
Proof.
  iIntros "Hpair".
  Fail zesu_conjunct_match_if_enabled.
  iExact "Hpair".
Qed.
End conjunct_match_tests.
Print Assumptions conjunct_match_named.
Print Assumptions conjunct_match_anonymous.
Print Assumptions conjunct_match_associated.
Print Assumptions conjunct_match_composite.
Print Assumptions conjunct_match_existing_name.
Print Assumptions conjunct_match_keeps_owned_bundle.
