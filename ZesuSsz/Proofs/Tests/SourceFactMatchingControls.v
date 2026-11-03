Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SourceFactMatching.
From Coq Require Import ZArith NArith.
From stdpp Require Import tactics decidable.
From stdpp.bitvector Require Import definitions.
Require Import ZesuSsz.Automation.All.
Local Open Scope Z_scope.

Definition source_named_and426 (left right : Prop) : Prop := left /\ right.
Definition source_nested_and426 (left middle right : Prop) : Prop :=
  source_named_and426 left (source_named_and426 middle right).
Definition source_named_or426 (left right : Prop) : Prop := left \/ right.
Definition source_named_exists426 (predicate : Z -> Prop) : Prop :=
  exists value, predicate value.

Lemma source_named_and_positive426 (P Q : Prop) (HP : P) (HQ : Q) :
  source_named_and426 P Q.
Proof. SourceFactMatching.zesu_source_fact. Qed.

Lemma source_nested_and_positive426 (P Q R : Prop)
    (HP : P) (HQ : Q) (HR : R) : source_nested_and426 P Q R.
Proof. SourceFactMatching.zesu_source_fact. Qed.

Lemma source_correlated_or_positive426 (P Q R : Prop)
    (HPQ : P \/ Q) (HR : R) : source_named_and426 (P \/ Q) R.
Proof. SourceFactMatching.zesu_source_fact. Qed.

Lemma source_boolean_preserved426 (left right : Z) (Hsame : left = right) :
  bool_decide (left = right) = true.
Proof. SourceFactMatching.zesu_source_fact. Qed.

Lemma source_missing_fact_refusal426 (P Q : Prop) (HP : P) : True.
Proof.
  Fail assert (Hunsupported : source_named_and426 P Q)
    by SourceFactMatching.zesu_source_fact.
  exact I.
Qed.

Lemma source_disjunction_refusal426 (P Q : Prop) (HP : P) : True.
Proof.
  Fail assert (Hunsupported : source_named_or426 P Q)
    by SourceFactMatching.zesu_source_fact.
  exact I.
Qed.

Lemma source_unresolved_head_refusal426 (P : Prop) (HP : P) (word : Z) : True.
Proof.
  let predicate := open_constr:(_ : Z -> Prop) in
  let before := eval cbv beta iota zeta in predicate in
  is_evar before;
  assert_fails (assert (Hunsupported : predicate word)
    by SourceFactMatching.zesu_source_fact);
  let after := eval cbv beta iota zeta in predicate in
  constr_eq_strict before after;
  is_evar after;
  unify after (fun _ : Z => False);
  exact I.
Qed.

Lemma source_symbolic_head_refusal426 (predicate : Z -> Prop)
    (left right : Z) (Hsource : predicate left) : True.
Proof.
  Fail assert (Hunsupported : predicate right)
    by SourceFactMatching.zesu_source_fact.
  exact I.
Qed.

Lemma source_existential_refusal426 (predicate : Z -> Prop)
    (Hsource : predicate 0) : True.
Proof.
  Fail assert (Hunsupported : source_named_exists426 predicate)
    by SourceFactMatching.zesu_source_fact.
  exact I.
Qed.

(* Proposed controls. B owns compilation after integrating the patch. *)
Lemma source_unsigned_nonnegative (width : N) (word : bv width) :
  (0 <= bv_unsigned word)%Z.
Proof. SourceFactMatching.zesu_source_fact. Qed.
Lemma source_unsigned_modulus (width : N) (word : bv width) :
  (bv_unsigned word < bv_modulus width)%Z.
Proof. SourceFactMatching.zesu_source_fact. Qed.
Lemma source_unsigned_power (width : N) (word : bv width) :
  (bv_unsigned word < 2 ^ Z.of_N width)%Z.
Proof. SourceFactMatching.zesu_source_fact. Qed.
Lemma source_unsigned_symbolic_refusal (width : N) (word : bv width) (bound : Z) : True.
Proof.
  Fail assert (Hunsupported : (bv_unsigned word < bound)%Z) by SourceFactMatching.zesu_source_fact.
  exact I.
Qed.

Lemma source_unsigned_wrong_closed_bound426 (width : N) (word : bv width) : True.
Proof.
  Fail assert (Hunsupported : (bv_unsigned word < 0)%Z)
    by SourceFactMatching.zesu_source_fact.
  exact I.
Qed.
