Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
From Coq Require Import ZArith.
Set Printing Width 200.
Set Printing Depth 1000000.
Ltac chain_print_environment marker environment :=
  let environment := eval hnf in environment in
  lazymatch environment with
  | environments.Enil => idtac
  | environments.Esnoc ?rest ?name ?resource =>
      chain_print_environment marker rest;
      idtac marker resource "CHAIN-FIELD-END"
  end.
Ltac chain_print_goal phase :=
  idtac "CHAIN-GOAL-BEGIN" phase;
  try (multimatch goal with
    | Hlocal : ?T |- _ =>
      idtac "CHAIN-GOAL-LOCAL" Hlocal ":" T "CHAIN-FIELD-END";
      let S := type of T in
      idtac "CHAIN-GOAL-SORT" Hlocal ":" S "CHAIN-FIELD-END";
      try (multimatch goal with
        | Hdefinition := ?value : _ |- _ =>
          constr_eq Hdefinition Hlocal;
          idtac "CHAIN-GOAL-VALUE" Hlocal ":" value "CHAIN-FIELD-END"
        end);
      fail
    end);
  lazymatch goal with
  | |- envs_entails ?environment ?conclusion =>
      idtac "CHAIN-GOAL-ENV" "iris" "CHAIN-FIELD-END";
      let persistent := eval cbv [environments.env_intuitionistic] in
        (environments.env_intuitionistic environment) in
      let spatial := eval cbv [environments.env_spatial] in
        (environments.env_spatial environment) in
      chain_print_environment "CHAIN-GOAL-PERSISTENT" persistent;
      chain_print_environment "CHAIN-GOAL-SPATIAL" spatial;
      idtac "CHAIN-GOAL-CONCLUSION" conclusion "CHAIN-FIELD-END"
  | |- ?conclusion =>
      idtac "CHAIN-GOAL-ENV" "coq" "CHAIN-FIELD-END";
      idtac "CHAIN-GOAL-CONCLUSION" conclusion "CHAIN-FIELD-END"
  end.

Lemma recorder_folded_environment `{!islaG Sigma} `{!threadG}
    (pointer : Z) (value : bv 8) :
    (pointer ↦ₘ value ∗ mmio_range 604086464 16) -∗ True%I.
Proof.
  iIntros "(Howned & #Hmmio)".
  chain_print_goal "active"; idtac "CHAIN-GOAL-END".
  lazymatch goal with
  | |- envs_entails ?environment ?conclusion =>
      pose (foldedEnvironment := environment);
      change (envs_entails foldedEnvironment conclusion)
  end.
  chain_print_goal "active"; idtac "CHAIN-GOAL-END".
  iPureIntro. exact I.
Qed.
Print Assumptions recorder_folded_environment.
