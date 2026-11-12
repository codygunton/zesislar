From Coq Require Import ZArith.ZArith.
From stdpp Require Import bitvector.definitions.
From lithium Require Import interpreter.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A branch fact `w = BV n z` or `w <> BV n z` enters the context through the
   Lithium intro. The intro keeps the fact and adds `bv_unsigned w = z` or
   `bv_unsigned w <> z`, so the successor guard's integer view closes by
   assumption (berlinGasCalc class K5). *)
Check ZesuSsz.Automation2.Hooks.zesu_bv_literal_unsigned_eq.
Check ZesuSsz.Automation2.Hooks.zesu_bv_literal_unsigned_neq.
Ltac check_view_tactic := ZesuSsz.Automation2.Hooks.zesu_bv_literal_unsigned_view_last.

Record literal_args := { literal_head : bv 64; literal_low : bv 64 }.

Lemma intro_views_disequality (word : bv 64) :
  word <> 0%bv -> bv_unsigned word <> 0.
Proof. liImpl. assumption. Qed.

Lemma intro_views_field_equality (args : literal_args) :
  literal_head args = 0%bv -> bv_unsigned (literal_head args) = 0.
Proof. liImpl. assumption. Qed.

(* The view keeps `bv_unsigned (bv_or ..)` unsimplified: a guard raised later
   states it in this form. *)
Lemma intro_views_or_disequality (args : literal_args) :
  bv_or (literal_head args) (literal_low args) <> 0%bv -> True.
Proof.
  liImpl.
  let expected := constr:(bv_unsigned (bv_or (literal_head args) (literal_low args)) <> 0) in
  match goal with view : ?statement |- _ => constr_eq statement expected; exact I end.
Qed.

(* A local definition is not substituted by the intro; its view follows it
   when it is unfolded. *)
Lemma intro_views_local_definition (args : literal_args) :
  let word := bv_or (literal_head args) (literal_low args) in word = 0%bv -> True.
Proof.
  intros word. liImpl. unfold word in *.
  let expected := constr:(bv_unsigned (bv_or (literal_head args) (literal_low args)) = 0) in
  match goal with view : ?statement |- _ => constr_eq statement expected; exact I end.
Qed.

Lemma intro_views_nonzero_literal (args : literal_args) :
  literal_head args <> 7%bv -> bv_unsigned (literal_head args) <> 7.
Proof. liImpl. assumption. Qed.

(* No view: a variable equal to a literal is substituted, and a comparison of
   two words has no literal side. Only the original fact is introduced. *)
Lemma intro_substitutes_variable (word : bv 64) :
  word = 0%bv -> True.
Proof.
  liImpl.
  tryif lazymatch goal with _ : bv_unsigned _ = _ |- _ => idtac end then fail else idtac.
  exact I.
Qed.

Lemma intro_keeps_word_comparison (left right : bv 64) :
  left <> right -> True.
Proof.
  liImpl.
  tryif lazymatch goal with _ : bv_unsigned left <> bv_unsigned right |- _ => idtac end
  then fail else idtac.
  exact I.
Qed.

(* A view already in the context is not added again. *)
Lemma intro_skips_present_view (args : literal_args) :
  bv_unsigned (literal_head args) <> 0 -> literal_head args <> 0%bv -> True.
Proof.
  liImpl. liImpl.
  tryif clear HbvUnsigned then fail else idtac.
  exact I.
Qed.
