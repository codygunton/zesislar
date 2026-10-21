Require Import ZesuSsz.Automation.All.
From Coq Require Import BinNums ZArith.
Require Import ZesuSsz.Automation.Hooks.

Lemma stackLiteralClassifier : True.
Proof.
  zesu_stack_integer_literal constr:(BinNums.Z0).
  zesu_stack_integer_literal constr:(BinNums.Zpos BinNums.xH).
  zesu_stack_integer_literal constr:(BinNums.Zneg BinNums.xH).
  zesu_stack_integer_literal constr:(BinNums.Zpos (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO BinNums.xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
  Fail zesu_stack_integer_literal constr:(Z.add (BinNums.Zpos BinNums.xH) (BinNums.Zpos BinNums.xH)).
  Fail zesu_stack_integer_literal constr:(Z.pow (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinNums.Zpos (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO BinNums.xH)))))))).
  pose (alias := BinNums.Z0).
  Fail zesu_stack_integer_literal alias.
  let unknown := open_constr:(_ : Z) in
  has_evar unknown;
  tryif zesu_stack_integer_literal unknown then fail 1 "UNEXPECTED EVAR MATCH"
  else (has_evar unknown; unify unknown (BinNums.Zpos (BinNums.xI BinNums.xH))).
  exact I.
Qed.
Print Assumptions stackLiteralClassifier.

Ltac stack_check_normalized hypothesis expected :=
  let statement := type of hypothesis in
  lazymatch statement with
  | Z.le _ ?bound =>
    zesu_stack_integer_literal bound;
    constr_eq bound expected
  end.
Lemma stackAdditionFallback (x : Z) :
  Z.le x (Z.add (BinNums.Zpos BinNums.xH) (BinNums.Zpos BinNums.xH)) ->
  Z.le x (BinNums.Zpos (BinNums.xO BinNums.xH)).
Proof.
  intros H.
  zesu_stack_normalize_hypothesis H.
  stack_check_normalized H constr:(BinNums.Zpos (BinNums.xO BinNums.xH)).
  exact H.
Qed.
Print Assumptions stackAdditionFallback.
Lemma stackPowerFallback (x : Z) :
  Z.le x (Z.pow (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinNums.Zpos (BinNums.xO (BinNums.xO BinNums.xH)))) ->
  Z.le x (BinNums.Zpos (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO BinNums.xH))))).
Proof.
  intros H.
  zesu_stack_normalize_hypothesis H.
  stack_check_normalized H constr:(BinNums.Zpos (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO BinNums.xH))))).
  exact H.
Qed.
Print Assumptions stackPowerFallback.
Lemma stackAliasFallback (x : Z) :
  Z.le x (Z.add (BinNums.Zpos BinNums.xH) (BinNums.Zpos BinNums.xH)) ->
  Z.le x (BinNums.Zpos (BinNums.xO BinNums.xH)).
Proof.
  pose (alias := Z.add (BinNums.Zpos BinNums.xH) (BinNums.Zpos BinNums.xH)).
  change (Z.le x alias -> Z.le x (BinNums.Zpos (BinNums.xO BinNums.xH))).
  intros H.
  Fail zesu_stack_integer_literal alias.
  zesu_stack_normalize_hypothesis H.
  stack_check_normalized H constr:(BinNums.Zpos (BinNums.xO BinNums.xH)).
  exact H.
Qed.
Print Assumptions stackAliasFallback.

Lemma stackLiteralRejectsSymbolic (value : Z) : True.
Proof.
  Fail zesu_stack_integer_literal value.
  exact I.
Qed.
Print Assumptions stackLiteralRejectsSymbolic.

Lemma stackConstructorNestedRefusals (positive_value : positive) : True.
Proof.
  Fail zesu_stack_integer_literal constr:(BinNums.Zpos positive_value).
  pose (positive_alias := BinNums.xH).
  Fail zesu_stack_integer_literal constr:(BinNums.Zpos positive_alias).
  pose (integer_alias := BinNums.Zpos (BinNums.xO BinNums.xH)).
  Fail zesu_stack_integer_literal integer_alias.
  Fail zesu_stack_integer_literal constr:(O).
  Fail zesu_stack_integer_literal constr:(true).
  let unknown := open_constr:(_ : positive) in
  has_evar unknown;
  let value := constr:(BinNums.Zpos (BinNums.xO unknown)) in
  tryif zesu_stack_integer_literal value then fail 1 "UNEXPECTED NESTED EVAR MATCH"
  else (has_evar unknown; unify unknown BinNums.xH).
  exact I.
Qed.
Print Assumptions stackConstructorNestedRefusals.
