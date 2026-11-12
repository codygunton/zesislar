From Coq Require Import ZArith.ZArith.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A branch fact `w = BV n z` or `w <> BV n z` is in the context only in
   bit-vector form, while the successor guard states it over `bv_unsigned w`
   (berlinGasCalc class K5). The finisher closes the guard from the fact. *)
Check ZesuSsz.Automation2.Hooks.zesu_bv_literal_unsigned_eq.
Check ZesuSsz.Automation2.Hooks.zesu_bv_literal_unsigned_neq.

Record literal_args := { literal_head : bv 64; literal_low : bv 64 }.

Lemma finish_reads_disequality (word : bv 64) :
  word <> 0%bv -> bv_unsigned word <> 0%Z.
Proof. intros different. zesu_finish. Qed.

Lemma finish_reads_field_equality (args : literal_args) :
  literal_head args = 0%bv -> bv_unsigned (literal_head args) = 0%Z.
Proof. intros same. zesu_finish. Qed.

Lemma finish_reads_or_disequality (args : literal_args) :
  bv_or (literal_head args) (literal_low args) <> 0%bv ->
  bv_unsigned (bv_or (literal_head args) (literal_low args)) <> 0%Z.
Proof. intros different. zesu_finish. Qed.

Lemma finish_reads_nonzero_literal (args : literal_args) :
  literal_head args <> 7%bv -> bv_unsigned (literal_head args) <> 7%Z.
Proof. intros different. zesu_finish. Qed.

(* The closer adds no hypothesis: on a goal it cannot close it leaves the
   context unchanged, and a comparison of two words has no literal side. *)
Lemma closer_keeps_context (left right : bv 64) :
  left <> right -> bv_unsigned left <> 1%Z -> True.
Proof.
  intros different other.
  tryif ZesuSsz.Automation2.Hooks.zesu_bv_literal_unsigned_goal then fail else idtac.
  assert (bv_unsigned left <> bv_unsigned right) as view.
  { tryif ZesuSsz.Automation2.Hooks.zesu_bv_literal_unsigned_goal then fail else idtac.
    apply bv_neq. exact different. }
  exact I.
Qed.
