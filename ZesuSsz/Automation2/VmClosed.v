From stdpp Require Import tactics bitvector.definitions.
From Coq Require Import ZArith.ZArith NArith.NArith.

(* Local definitions can hide unresolved evars from the outer term. *)
Ltac zesu_vm_has_unresolved term :=
  first [has_evar term |
    multimatch goal with
    | local := ?body : _ |- _ =>
        lazymatch term with
        | context[local] => zesu_vm_has_unresolved body
        end
    end].

(* Keep only the hypotheses the goal needs, then unfold the newest one in the
   goal. Only the goal needs the newest hypothesis, so each round removes it.
   A remaining hypothesis that is not a definition makes the goal open. *)
Ltac zesu_vm_closed_goal :=
  let keep := fresh in
  pose proof I as keep; clear - keep; clear keep;
  lazymatch goal with
  | local := _ |- _ => progress unfold local; zesu_vm_closed_goal
  | _ : _ |- _ => fail
  | _ => idtac
  end.

(* Accept the terms that stdpp `is_closed_term` accepts, without its
   `unfold H in *` per hypothesis (quadratic in the context size). *)
Ltac zesu_vm_closed_term term :=
  first [
    assert_succeeds (exfalso; change_no_check (const False term);
      zesu_vm_closed_goal) |
    fail 1 "The term" term "is not closed"].

Ltac zesu_vm_closed term :=
  assert_fails ltac:(zesu_vm_has_unresolved term);
  zesu_vm_closed_term term.

(* Check the full input before VM evaluation. *)
Ltac zesu_vm_eval_closed term :=
  let checked := constr:((ltac:(zesu_vm_closed term; exact I) : True)) in
  let value := eval vm_compute in term in
  constr:(value).

(* Check the decision before installing its conversion proof. *)
Ltac zesu_vm_closed_decide :=
  lazymatch goal with |- ?proposition =>
    lazymatch proposition with
    | @eq ?kind _ _ =>
        lazymatch kind with
        | Z => idtac | N => idtac | nat => idtac | bool => idtac
        | bv _ => idtac
        end
    | Z.le _ _ => idtac | Z.lt _ _ => idtac
    | N.le _ _ => idtac | N.lt _ _ => idtac
    | Coq.Init.Peano.le _ _ => idtac | Coq.Init.Peano.lt _ _ => idtac
    end;
    zesu_vm_closed proposition;
    let decision := constr:(_ : Decision proposition) in
    zesu_vm_closed decision;
    let result := eval vm_compute in (@bool_decide proposition decision) in
    constr_eq result true;
    refine (@bool_decide_eq_true_1 proposition decision _);
    vm_cast_no_check (eq_refl true)
  end.

Ltac zesu_vm_compute_closed :=
  lazymatch goal with |- ?proposition =>
    zesu_vm_closed proposition;
    vm_compute
  end.
