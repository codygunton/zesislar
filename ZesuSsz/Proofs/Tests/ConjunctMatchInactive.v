Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ConjunctMatch.
Require Import isla.riscv64.riscv64.

Set Default Proof Using "Type".

Section conjunct_match_v1_test.
Context `{!islaG Sigma} `{!threadG}.
Local Instance conjunct_match_step_only : ZesuStepConjunctMatch := I.

Lemma conjunct_match_v1_inactive (P Q : iProp Sigma) : P -∗ Q -∗ P ∗ Q.
Proof.
  iIntros "HP HQ".
  Fail zesu_conjunct_match_if_enabled.
  iFrame.
Qed.
End conjunct_match_v1_test.

Require Import ZesuSsz.Automation.Sets.v2.
Section conjunct_match_switch_test.
Context `{!islaG Sigma} `{!threadG}.

Lemma conjunct_match_switch_inactive (P Q : iProp Sigma) :
  P -∗ Q -∗ P ∗ Q.
Proof.
  iIntros "HP HQ".
  Fail zesu_conjunct_match_if_enabled.
  iFrame.
Qed.
End conjunct_match_switch_test.
Print Assumptions conjunct_match_v1_inactive.
Print Assumptions conjunct_match_switch_inactive.
