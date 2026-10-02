Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ResourceGroups.
Require Import ZesuSsz.Automation.ArrayLoadPriority.
Require Import ZesuSsz.Automation.TracePrefixTail.
From iris.proofmode Require Import environments.

(* Search only separation and three definition layers for an owned array. *)
Ltac zesu_contains_owned_payload_array requested body depth :=
  lazymatch body with
  | (?address ↦ₘ∗ _)%I => constr_eq address requested
  | (?leftPart ∗ ?rightPart)%I =>
      first [zesu_contains_owned_payload_array requested leftPart depth |
             zesu_contains_owned_payload_array requested rightPart depth]
  | _ =>
      lazymatch depth with
      | S ?remaining =>
          let head := get_head body in
          is_const head;
          let expanded := eval cbv beta zeta delta [head] in body in
          tryif constr_eq expanded body then fail else
            zesu_contains_owned_payload_array requested expanded remaining
      end
  end.

Ltac zesu_open_owned_array_fact_packages :=
  repeat iMatchHyp ltac:(fun H body =>
    let head := get_head body in
    is_const head;
    let expanded := eval cbv beta zeta delta [head] in body in
    lazymatch expanded with
    | ((_ ↦ₘ∗ _) ∗ ⌜_⌝)%I =>
        progress iEval (unfold head) in H;
        zesu_open_resource_groups
    end).

Ltac zesu_open_matching_payload_package :=
  let _ := constr:(_ : ZesuStepArrayLoadPriority) in
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ ?requestedGoal =>
      lazymatch requestedGoal with
      | @bi_exist _ (spec *ₗ list (bv 8) *ₗ ()) ?bodyFunction =>
          let inspected := eval cbv beta in (bodyFunction (snil, ([] : list (bv 8)), tt)ₗ) in
          lazymatch inspected with
          | context[(?address ↦ₘ∗ _)%I] =>
          iMatchHyp ltac:(fun H body =>
            let head := get_head body in
            is_const head;
            zesu_contains_owned_payload_array address body 3%nat;
            progress iEval (unfold head) in H;
            zesu_open_resource_groups;
            zesu_open_owned_array_fact_packages)
          end
      end
  end.

(* Fix both witnesses from the owned array and its complete event prefix. *)
Ltac zesu_choose_owned_payload_tail :=
  let _ := constr:(_ : ZesuStepTracePrefixTail) in
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (spec *ₗ list (bv 8) *ₗ ()) ?bodyFunction) =>
      let candidate := constr:(fun _ : list seq_label => False) in
      let inspected := eval cbv beta iota delta [li_fst li_snd] in
        (bodyFunction (candidate, ([] : list (bv 8)), tt)ₗ) in
      lazymatch inspected with
      | context[(?address ↦ₘ∗ _)%I] =>
          iMatchHyp ltac:(fun H body =>
            lazymatch body with
            | unseal mem_mapsto_array_aux ?ownedAddress (DfracOwn 1) ?bytes =>
                constr_eq ownedAddress address;
                let opened := eval cbv beta iota delta [li_fst li_snd] in
                  (bodyFunction (candidate, bytes, tt)ₗ) in
                lazymatch opened with
                | context[spec_trace ?generated] =>
                    iMatchHyp ltac:(fun Htrace traceBody =>
                      lazymatch traceBody with
                      | spec_trace ?declared =>
                          let tail := zesu_matching_trace_tail candidate generated declared in
                          iExists (tail, bytes, tt)ₗ
                      end)
                end
            end)
      end
  end.
