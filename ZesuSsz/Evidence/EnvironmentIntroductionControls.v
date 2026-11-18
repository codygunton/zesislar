Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.EnvironmentIntroduction.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import tactics.
Local Open Scope bi_scope.

Definition environment_test_target (Sigma : gFunctors)
    (resource : iProp Sigma) : iProp Sigma := resource.

#[local] Hint Extern 0
    (@ZesuPureFactIntro ?Sigma (environment_test_target ?Sigma ?resource)
      (environments.of_envs ?environment)) =>
  (apply EnvironmentIntroduction.zesu_environment_intro;
   unfold environment_test_target; solve [iFrame]) : typeclass_instances.

Lemma environment_intro_positive (Sigma : gFunctors) (resource : iProp Sigma) :
  resource ⊢ environment_test_target Sigma resource.
Proof.
  iIntros "Hresource".
  EnvironmentIntroduction.zesu_registered_environment_intro.
Qed.

Lemma environment_intro_pair (Sigma : gFunctors) (left right : iProp Sigma) :
  left ∗ right ⊢ environment_test_target Sigma (left ∗ right).
Proof.
  iIntros "[Hleft Hright]".
  EnvironmentIntroduction.zesu_registered_environment_intro.
Qed.

Lemma environment_intro_changed_resource_refuses
    (Sigma : gFunctors) (left right : iProp Sigma) : Coq.Init.Logic.True.
Proof.
  Fail assert (left ⊢ environment_test_target Sigma right) by
    (iIntros "Hleft";
     EnvironmentIntroduction.zesu_registered_environment_intro).
  exact I.
Qed.

Lemma environment_intro_missing_resource_refuses
    (Sigma : gFunctors) (resource : iProp Sigma) : Coq.Init.Logic.True.
Proof.
  Fail assert (True ⊢ environment_test_target Sigma resource) by
    (iIntros "_";
     EnvironmentIntroduction.zesu_registered_environment_intro).
  exact I.
Qed.
