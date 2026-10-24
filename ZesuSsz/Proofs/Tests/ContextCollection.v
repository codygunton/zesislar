Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.
From Coq Require Import Lia.
Require Import ZesuSsz.Automation.ContextCollection.
Set Default Proof Mode "Classic".
Lemma scaling_collection_controls : True.
Proof.
  assert (Hunused : forall x y : nat, x = x).
  { intros x y. zesu_context_collect.
    Fail let value := constr:(y) in idtac.
    reflexivity. }
  clear Hunused.
  assert (Hlinked : forall x y : nat, x = y -> x = y).
  { intros x y H. zesu_context_collect. exact H. }
  clear Hlinked.
  assert (Hdefinition : forall x : nat, x = x).
  { intros x. pose (saved := x). change (saved = saved).
    zesu_context_collect. reflexivity. }
  clear Hdefinition.
  assert (Hfallback : forall n : Z, (n = 0)%Z -> (n < 0)%Z -> (0 = 1)%Z).
  { intros n Hzero Hnegative.
    Fail solve [zesu_context_prune_goal; Zify.zify; xlia Lia.zchecker].
    let preserved := constr:(Hzero) in idtac.
    let preserved := constr:(Hnegative) in idtac.
    zesu_context_filtered ltac:(Zify.zify; xlia Lia.zchecker). }
  clear Hfallback.
  assert (Hcase : forall n : nat, (match n with O => True | S _ => False end) -> True).
  { intros n H. Fail zesu_context_collect.
    let preserved := constr:(H) in idtac. exact I. }
  clear Hcase.
  assert (Hevar : exists n : nat, n = O).
  { eexists. Fail zesu_context_collect. reflexivity. }
  clear Hevar.
  assert (Honce : lithium.proof_state.SHELVED_SIDECOND True).
  { zesu_context_finish_once ltac:(idtac).
    zesu_context_finish_once ltac:(fail 1 "The finisher repeated an unchanged goal").
    exact I. }
  clear Honce.
  assert (Hdifferent : True).
  { zesu_context_finish_resolved constr:(True) ltac:(idtac).
    zesu_context_finish_resolved constr:(False) ltac:(pose proof I as Hsecond).
    exact Hsecond. }
  clear Hdifferent.
  exact I.
Qed.
