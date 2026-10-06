Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma known_pair_opt_in : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepKnownPairWitness) in idtac.
  exact I.
Qed.

Lemma known_pair_disabled `{!islaG Sigma} `{!threadG}
    (A : Type) (P : A -> Prop) (R : A -> iProp Sigma) (value : A)
    (Howned : P value) :
  R value -∗ (∃ x : A *ₗ (), ⌜P x.1ₗ⌝ ∗ R x.1ₗ)%I.
Proof.
  iStartProof. iIntros "HR".
  Fail zesu_known_pair_witness_if_enabled.
  iExists (li_pair value tt). iFrame. done.
Qed.

Require Import ZesuSsz.Automation.Switches.KnownPairWitness.

Lemma known_pair_resources `{!islaG Sigma} `{!threadG}
    (A : Type) (P : A -> Prop) (R : A -> iProp Sigma) (value : A)
    (Howned : P value) :
  R value -∗ (∃ x : A *ₗ (), ⌜P x.1ₗ⌝ ∗ R x.1ₗ)%I.
Proof.
  iStartProof. iIntros "HR".
  zesu_known_pair_witness_if_enabled.
  iFrame. done.
Qed.


Lemma known_pair_structural_goal : True.
Proof.
  Fail zesu_known_pair_witness_if_enabled.
  exact I.
Qed.
