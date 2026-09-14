Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.

(* Pure extraction removes its persistent source. Separation keeps both children. *)
Ltac zesu_open_resource_groups :=
  repeat iMatchHyp ltac:(fun H body =>
    lazymatch body with
    | (_ ∗ _)%I => iDestruct H as "[? ?]"
    | (⌜_⌝)%I => iDestruct H as %?; try iClear H
    end).

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
      solve [repeat iSplit; iPureIntro; first [assumption | done | lia | bv_solve]]
  end.
