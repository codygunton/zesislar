Require Import ZesuSsz.Automation.All.
From iris.proofmode Require Import environments.
From iris.base_logic.lib Require Import iprop.
From Coq Require Import ZArith.

Open Scope Z_scope.

Lemma final_pure_interval (value lower upper : Z) :
  lower <= value -> value < upper -> lower <= value <= upper - 1.
Proof.
  intros Hlower Hupper.
  zesu_finish_final_pure.
Qed.
Print Assumptions final_pure_interval.

Lemma final_pure_spatial_refusal (Sigma : gFunctors)
    (Delta : envs (iProp Sigma)) (Q : iProp Sigma) :
  envs_entails Delta Q -> envs_entails Delta Q.
Proof.
  intros Hentails.
  Fail zesu_final_pure_head_gate.
  Fail zesu_finish_final_pure.
  exact Hentails.
Qed.
Print Assumptions final_pure_spatial_refusal.
