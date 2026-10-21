Require Import ZesuSsz.Automation.All.
From Coq Require Import BinNums ZArith.
Require Import ZesuSsz.Automation.Hooks.

(* Compare the production visitor with the original behavior. *)
Ltac stack_closed_original term :=
  tryif has_evar term then fail 0 else
  let expanded := eval cbv beta zeta in term in
  let rec visit current :=
    tryif is_var current then
      let body := eval unfold current in current in
      stack_closed_original body
    else lazymatch current with
    | (fun _ => _) => fail 0
    | (forall _, _) => fail 0
    | ?function ?argument => visit function; visit argument
    | _ => idtac
    end
  in visit expanded.



Ltac stack_closed_agree term :=
  tryif stack_closed_original term
  then zesu_stack_closed_term term
  else tryif zesu_stack_closed_term term
       then fail 1 "UNEXPECTED CLOSED TERM ACCEPTANCE"
       else idtac.
Lemma stackClosedTraversalAtoms : True.
Proof.
  stack_closed_agree constr:(BinNums.Z0).
  stack_closed_agree constr:((2 + 3)%Z).
  stack_closed_agree constr:((2 ^ 64)%Z).
  exact I.
Qed.
Print Assumptions stackClosedTraversalAtoms.
Lemma stackClosedTraversalSymbols (value : Z) : True.
Proof.
  stack_closed_agree value.
  Fail zesu_stack_closed_term value.
  stack_closed_agree constr:((3 + value)%Z).
  Fail zesu_stack_closed_term constr:((3 + value)%Z).
  exact I.
Qed.
Print Assumptions stackClosedTraversalSymbols.
Lemma stackClosedTraversalAliases (value : Z) : True.
Proof.
  pose (closed_alias := (2 + 3)%Z).
  stack_closed_agree closed_alias.
  zesu_stack_closed_term closed_alias.
  stack_closed_agree constr:((closed_alias + 7)%Z).
  pose (beta_alias := ((fun number : Z => (number + 1)%Z) 2%Z)).
  stack_closed_agree beta_alias.
  zesu_stack_closed_term beta_alias.
  pose (zeta_alias := (let number : Z := 2%Z in (number + 1)%Z)).
  stack_closed_agree zeta_alias.
  zesu_stack_closed_term zeta_alias.
  let unknown := open_constr:(_ : Z) in
  let alias := fresh "evar_alias" in
  pose (alias := unknown);
  tryif zesu_stack_closed_term alias then fail 1 "UNEXPECTED ALIAS EVAR ACCEPTANCE"
  else (has_evar unknown; unify unknown 7%Z).
  pose (symbolic_alias := (value + 3)%Z).
  stack_closed_agree symbolic_alias.
  Fail zesu_stack_closed_term symbolic_alias.
  exact I.
Qed.
Print Assumptions stackClosedTraversalAliases.
Lemma stackClosedTraversalBinders : True.
Proof.
  stack_closed_agree constr:((fun value : Z => value)).
  Fail zesu_stack_closed_term constr:((fun value : Z => value)).
  stack_closed_agree constr:((forall value : Z, value = value)).
  Fail zesu_stack_closed_term constr:((forall value : Z, value = value)).
  stack_closed_agree constr:((fun value : Z => (value + 1)%Z) 2%Z).
  stack_closed_agree constr:(match true with true => 2%Z | false => 3%Z end).
  exact I.
Qed.
Print Assumptions stackClosedTraversalBinders.
Lemma stackClosedTraversalEvars : True.
Proof.
  let unknown := open_constr:(_ : Z) in
  has_evar unknown;
  stack_closed_agree unknown;
  tryif zesu_stack_closed_term unknown then fail 1 "UNEXPECTED EVAR ACCEPTANCE"
  else (has_evar unknown; unify unknown 4%Z).
  let unknown := open_constr:(_ : Z) in
  let nested := constr:((2 + unknown)%Z) in
  has_evar nested;
  stack_closed_agree nested;
  tryif zesu_stack_closed_term nested then fail 1 "UNEXPECTED NESTED EVAR ACCEPTANCE"
  else (has_evar unknown; unify unknown 5%Z).
  exact I.
Qed.
Print Assumptions stackClosedTraversalEvars.
Lemma stackClosedTraversalArithmeticFallback (value : Z) :
  Z.le value (Z.add (2 ^ 4)%Z (2 + 3)%Z) -> Z.le value 21%Z.
Proof.
  pose (closed_alias := (2 + 3)%Z).
  change (Z.le value (Z.add (2 ^ 4)%Z closed_alias) -> Z.le value 21%Z).
  intros H.
  zesu_stack_normalize_hypothesis H.
  let statement := type of H in
  lazymatch statement with Z.le _ ?bound =>
    zesu_stack_integer_literal bound;
    constr_eq bound constr:(21%Z)
  end.
  exact H.
Qed.
Print Assumptions stackClosedTraversalArithmeticFallback.
