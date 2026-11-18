Require Import ZesuSsz.Automation.Hooks.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import environments.

Lemma zesu_environment_intro (Sigma : gFunctors)
    (environment : environments.envs (iProp Sigma)) (target : iProp Sigma) :
  environments.envs_entails environment target ->
  ZesuPureFactIntro target (environments.of_envs environment).
Proof.
  unfold ZesuPureFactIntro.
  rewrite environments.envs_entails_unseal.
  intros proof. exact proof.
Qed.

Lemma zesu_environment_intro_apply (Sigma : gFunctors)
    (environment : environments.envs (iProp Sigma)) (target : iProp Sigma) :
  ZesuPureFactIntro target (environments.of_envs environment) ->
  environments.envs_entails environment target.
Proof.
  unfold ZesuPureFactIntro.
  rewrite environments.envs_entails_unseal.
  intros proof. exact proof.
Qed.

(* The source is fixed before registration lookup. No witness is guessed. *)
Ltac zesu_registered_environment_intro :=
  lazymatch goal with
  | |- environments.envs_entails ?environment ?target =>
      let introduction := constr:(_ :
        ZesuPureFactIntro target (environments.of_envs environment)) in
      exact (zesu_environment_intro_apply _ environment target introduction)
  end.
