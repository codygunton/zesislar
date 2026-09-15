Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.

(* Pure extraction removes its persistent source. Separation keeps both children. *)
Ltac zesu_expose_environment_alias :=
  repeat match goal with
  | Hlocal := _ : envs (iPropI _) |- envs_entails ?current _ =>
      constr_eq Hlocal current; subst Hlocal
  end.

Ltac zesu_open_resource_groups :=
  repeat iMatchHyp ltac:(fun H body =>
    lazymatch body with
    | (_ ∗ _)%I => iDestruct H as "[? ?]"
    | (⌜_⌝)%I => iDestruct H as %?; try iClear H
    end).

(* Split an instruction bundle only when its first PC is requested. *)
Ltac zesu_open_requested_instr_bundle :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindInstrKind ?address _) _) =>
      iMatchHyp ltac:(fun H body =>
        lazymatch body with
        | (instr ?firstAddress _ ∗ _)%I =>
            constr_eq firstAddress address;
            iDestruct H as "[? ?]"
        end)
  end.

(* Unfold only a package whose first resource is the current goal resource. *)
Ltac zesu_open_matching_resource_package :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (?requested ∗ _)%I =>
      iMatchHyp ltac:(fun H body =>
        let head := get_head body in
        tryif first [constr_eq head constr:(@bi_sep) |
                     constr_eq head constr:(@bi_pure)] then fail else
          let expanded := eval cbv beta delta [head] in body in
          lazymatch expanded with
          | (?first ∗ _)%I =>
              constr_eq first requested;
              progress iEval (unfold head) in H;
              iDestruct H as "[? ?]"
          end)
  end.

Ltac zesu_is_pure_resource body :=
  lazymatch body with
  | (bi_pure _)%I => idtac
  | (?left ∗ ?right)%I =>
      zesu_is_pure_resource left; zesu_is_pure_resource right
  end.

Ltac zesu_promote_folded_pure_resources :=
  repeat iMatchHyp ltac:(fun H body =>
    let head := get_head body in
    tryif first [constr_eq head constr:(@bi_pure) |
                 constr_eq head constr:(@bi_sep)] then fail else
      let expanded := eval cbv beta delta [head] in body in
      zesu_is_pure_resource expanded;
      progress iEval (unfold head) in H;
      zesu_open_resource_groups).

Ltac zesu_finish_pure_resources :=
  lazymatch goal with
  | |- envs_entails _ ?body =>
      zesu_is_pure_resource body;
      solve [repeat first
        [solve [iPureIntro; assumption] | solve [done] | iSplit |
         solve [iPureIntro; first [lia | bv_solve]]]]
  end.
