From Coq Require Import ZArith.ZArith.
From stdpp Require Import base tactics.
Require Import ZesuSsz.Automation2.All.

(* stdpp's `done` (redefined in Automation2/Hooks.v): a contradiction is
   first sought syntactically, then by Coq's `contradiction` under the
   failure memo keyed on the context. *)

(* Syntactic: `¬ A` and `A`. *)
Lemma done_syntactic_pair (x y : Z) (A : Prop) : ¬ A -> A -> x = y.
Proof. intros. done. Qed.

(* By conversion only: `2 + 2 = 4` is `4 = 4`, which the negation denies. *)
Lemma done_conversion_pair (x y : Z) : ¬ (2 + 2 = 4)%nat -> (4 = 4)%nat -> x = y.
Proof. intros. done. Qed.

(* A context without a contradiction fails, also when asked again with the
   same context (the memo); once the context changes, the contradiction it
   now holds (by conversion) is found. *)
Lemma done_memo_then_changed_context (x y : Z) (P : nat -> Prop) (a : nat) :
  ¬ P (2 + 2)%nat -> a = 4%nat -> P a -> x = y.
Proof.
  intros Ha Hn.
  Fail done.
  Fail done.
  subst a.
  done.
Qed.

Print Assumptions done_memo_then_changed_context.
