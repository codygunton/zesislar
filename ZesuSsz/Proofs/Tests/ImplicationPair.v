Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma implicationPairOnce (A B C : Prop) :
  A -> (A -> B) -> (B -> C) -> C.
Proof.
  intros HA HAB HBC.
  zesu_finish_implication_pair.
  Fail zesu_finish_implication_pair.
  assumption.
Qed.

Lemma implicationPairAbsent (A B C : Prop) :
  (A -> B) -> (B -> C) -> True.
Proof.
  intros HAB HBC.
  Fail zesu_finish_implication_pair.
  exact I.
Qed.

Lemma implicationPairPreservesEvar (P : nat -> Prop) (Q R : Prop) (n : nat) :
  P n -> (Q -> R) -> True.
Proof.
  intros Hsource Houter.
  let index := open_constr:(_ : nat) in
  has_evar index;
  assert (Hprobe : (P index -> Q) -> True);
  [ intro Hinner;
    tryif zesu_finish_implication_pair
    then fail 1 "the pair assigned an unresolved index" else idtac;
    has_evar index; unify index (S n); exact I
  | intros; exact I ].
Qed.

Print Assumptions implicationPairOnce.
Print Assumptions implicationPairAbsent.
Print Assumptions implicationPairPreservesEvar.

Lemma implicationPairNegatedGe (left right : Z) (Middle Result : Prop) :
  (left < right -> Middle)%Z -> (Middle -> Result) ->
  (~ (left >= right))%Z -> Result.
Proof.
  intros Hinner Houter Hnot.
  zesu_finish_negated_ge.
  zesu_finish_implication_pair.
  assumption.
Qed.

Lemma implicationPairKeepsSource (left right : Z) :
  (~ (left >= right))%Z -> True.
Proof.
  intro Hnot.
  zesu_finish_negated_ge.
  lazymatch goal with _ : (~ (left >= right))%Z |- _ => idtac end.
  Fail progress zesu_finish_negated_ge.
  exact I.
Qed.

Print Assumptions implicationPairNegatedGe.
Print Assumptions implicationPairKeepsSource.


Lemma forallLeafPresent (A : Type) (P Q : A -> Prop) (value : A) :
  (forall x, P x -> Q x) -> P value -> Q value.
Proof.
  intros Hrule Hpremise.
  zesu_finish_forall_leaf.
Qed.

Lemma forallLeafAbsent (A : Type) (P Q : A -> Prop) (value : A) :
  (forall x, P x -> Q x) -> True.
Proof.
  intro Hrule.
  Fail assert (Hmissing : Q value) by zesu_finish_forall_leaf.
  exact I.
Qed.

Lemma forallLeafPreservesGoalEvar (P : nat -> Prop) (n : nat) :
  P n -> (forall index, P index -> P index) -> True.
Proof.
  intros Hknown Hrule.
  let index := open_constr:(_ : nat) in
  assert (Hprobe : P index -> P index);
  [ intro Hpremise;
    tryif zesu_finish_forall_leaf
    then fail 1 "the forall closer assigned the goal index" else idtac;
    has_evar index; unify index (S n); exact Hpremise
  | exact I ].
Qed.

Print Assumptions forallLeafPresent.
Print Assumptions forallLeafAbsent.
Print Assumptions forallLeafPreservesGoalEvar.
