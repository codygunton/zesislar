(* Expose the instruction selector before Lithium resolves a call return.
   A failed existing array-load guard backtracks this entire alternative. *)
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.ResourceGroups.
Require Import ZesuSsz.Automation.ArrayLoadPriority.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.

(* Preserve explicit handoffs before selecting a raw array-load trace. *)
Ltac zesu_array_load_find_explicit_handoff address spatial :=
  lazymatch spatial with
  | Esnoc ?rest _ (instr_pre' ?later ?entry ?resources) =>
      first [unify entry address |
             zesu_array_load_find_explicit_handoff address rest]
  | Esnoc ?rest _ _ => zesu_array_load_find_explicit_handoff address rest
  | _ => fail 0 "The preselector found no explicit handoff."
  end.

Ltac zesu_array_load_no_explicit_handoff address :=
  assert_fails (has_evar address);
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails ?Delta _ =>
      let spatial := eval cbn [env_spatial] in (env_spatial Delta) in
      let persistent := eval cbn [env_intuitionistic] in (env_intuitionistic Delta) in
      assert_fails (idtac; zesu_array_load_find_explicit_handoff address spatial);
      assert_fails (idtac; zesu_array_load_find_explicit_handoff address persistent)
  end.

Ltac zesu_array_load_use_explicit_handoff :=
  let _ := constr:(_ : ZesuStepArrayLoadPriority) in
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindInstrKind ?address ?later) ?continuation) =>
      assert_fails (has_evar address);
      iMatchHyp ltac:(fun H body =>
        idtac; lazymatch body with
        | instr_pre' ?has_later ?entry ?resources =>
            unify entry address;
            lazymatch later with
            | true =>
                iApply (find_in_context_instr_kind_pre_true address continuation);
                iExists has_later, resources; iFrame H
            | false =>
                unify has_later false;
                iApply (find_in_context_instr_kind_pre_false address continuation);
                iExists resources; iFrame H
            end
        | _ => fail 0 "The resource is not an explicit handoff."
        end)
  end.

Ltac zesu_array_load_preselect_core later address resources :=
  assert_fails (has_evar address);
  assert_fails (has_evar resources);
  iApply (li_instr_pre later address resources);
  zesu_liAStep;
  first [zesu_array_load_use_explicit_handoff |
         zesu_array_load_no_explicit_handoff address; zesu_array_load_priority].

Ltac zesu_array_load_preselect :=
  let _ := constr:(_ : ZesuStepArrayLoadPriority) in
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ ((instr_pre' ?later ?address ?resources) ∗ True)%I =>
      iSplit; [zesu_array_load_preselect_core later address resources | done]
  | |- envs_entails _ (instr_pre' ?later ?address ?resources) =>
      zesu_array_load_preselect_core later address resources
  end.
