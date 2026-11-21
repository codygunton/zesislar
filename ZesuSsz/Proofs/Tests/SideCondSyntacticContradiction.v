Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* Lithium's side condition of `⌜P⌝ ∗ Q` (`liSideCond`, redefined in
   `Automation2/Hooks.v`): `done` with a syntactic contradiction. A
   contradiction that `contradiction` finds by the type of a hypothesis
   (`Empty_set`, an inductive type without constructors) no longer proves `P` there: `P` is
   shelved for the finishers. A syntactic one (`¬ A` and `A`, a hypothesis
   `a ≠ a`, `False`) still does, and so does an assumption. *)
Section sidecond.
Context `{!islaG Sigma} `{!threadG}.

Lemma sidecond_conversion_shelved (x : Z) (Q : iProp Sigma) :
  Empty_set -> Q -∗ ⌜x = 5⌝ ∗ Q.
Proof.
  iIntros (Hc) "HQ".
  liSideCond.
  (* The side condition went to the shelf; only `Q` is left in front. *)
  iExact "HQ".
  Unshelve.
  lazymatch goal with |- SHELVED_SIDECOND (x = 5) => idtac end.
  destruct Hc.
Qed.

Lemma sidecond_syntactic_pair (x : Z) (A : Prop) (Q : iProp Sigma) :
  ¬ A -> A -> Q -∗ ⌜x = 5⌝ ∗ Q.
Proof.
  iIntros (Hn Ha) "HQ".
  liSideCond.
  iExact "HQ".
Qed.

Lemma sidecond_syntactic_neq (x y : Z) (Q : iProp Sigma) :
  y ≠ y -> Q -∗ ⌜x = 5⌝ ∗ Q.
Proof.
  iIntros (Hc) "HQ".
  liSideCond.
  iExact "HQ".
Qed.

Lemma sidecond_false (x : Z) (Q : iProp Sigma) :
  False -> Q -∗ ⌜x = 5⌝ ∗ Q.
Proof.
  iIntros (Hc) "HQ".
  liSideCond.
  iExact "HQ".
Qed.

Lemma sidecond_assumption (x : Z) (Q : iProp Sigma) :
  x = 5 -> Q -∗ ⌜x = 5⌝ ∗ Q.
Proof.
  iIntros (Hc) "HQ".
  liSideCond.
  iExact "HQ".
Qed.
End sidecond.

Print Assumptions sidecond_conversion_shelved.
Print Assumptions sidecond_syntactic_pair.
