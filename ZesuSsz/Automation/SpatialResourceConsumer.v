Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.ResourceGroups.
Require Import lithium.interpreter lithium.pure_definitions.
From iris.proofmode Require Import tactics environments.

(* Construct only tuple structure. Every data field remains a fresh metavariable. *)
Ltac zesu_owned_fresh_tuple T :=
  let exposed := eval hnf in T in
  lazymatch exposed with
  | li_prod ?A ?B =>
      let head := open_constr:(_ : A) in
      let tail := zesu_owned_fresh_tuple B in
      constr:(li_pair head tail)
  | unit => constr:(tt)
  | _ => open_constr:(_ : T)
  end.

Ltac zesu_spatial_open_owned fuel :=
  lazymatch fuel with
  | S ?remaining =>
      lazymatch goal with
      | |- environments.envs_entails _ (@bi_exist _ ?T ?body) =>
          assert_fails (has_evar T);
          let witness := zesu_owned_fresh_tuple T in
          notypeclasses refine (tac_ex_evar _ witness _ _); red_li_prod;
          zesu_spatial_open_owned remaining
      | _ => idtac
      end
  | O => fail 0 "The owned package exceeds its existential step bound."
  end.

(* Resource matching supplies data values. Both callbacks are delayed functions. *)
Ltac zesu_spatial_consume_owners expose_target finish :=
  ResourceGroups.zesu_open_resource_groups;
  zesu_spatial_open_owned constr:(16%nat);
  expose_target constr:(tt);
  try iFrame;
  finish constr:(tt).
