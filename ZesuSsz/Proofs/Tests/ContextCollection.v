Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.
From Coq Require Import Lia.
Require Import ZesuSsz.Automation.ContextCollection.
From stdpp Require Import bitvector.definitions.
From Ltac2 Require Import Ltac2.
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

Lemma collection_let_body (x y : Z) (Hxy : x = y) : True.
Proof.
pose (witness := Hxy).
zesu_context_collect.
let body := eval unfold witness in witness in constr_eq body Hxy.
let statement := type of Hxy in constr_eq statement (x = y).
exact I.
Qed.

Lemma collection_transitive (x irrelevant : Z) (Hx : x = 0%Z) (Hirrelevant : irrelevant = 9%Z) : True.
Proof.
pose (alias1 := x). pose (alias2 := alias1).
zesu_context_collect.
let statement := type of Hx in constr_eq statement (x = 0%Z).
let body := eval unfold alias2 in alias2 in constr_eq body alias1.
ltac2:(if List.exist (fun (name, _, _) => Ident.equal name @Hirrelevant) (Control.hyps ()) then Control.throw (Tactic_failure None) else ()).
exact I.
Qed.

Lemma collection_irrelevant (x : Z) (Hx : x = 0%Z) : True.
Proof.
zesu_context_collect.
ltac2:(if List.exist (fun (name, _, _) => Ident.equal name @Hx) (Control.hyps ()) then Control.throw (Tactic_failure None) else ()).
ltac2:(if List.exist (fun (name, _, _) => Ident.equal name @x) (Control.hyps ()) then Control.throw (Tactic_failure None) else ()).
exact I.
Qed.

Lemma collection_alignment (R : Prop) :
  let target : bv 64%N := bv_add (Z_to_bv 64%N 2148362608%Z) (BV 64%N 368%Z) in
  let aligned : bool := negb (bool_decide (bv_extract 1%N 1%N target = BV 1%N 1%Z)) in
  negb aligned = true -> R.
Proof.
intros target aligned Hfault.
zesu_context_collect.
let statement := type of Hfault in constr_eq statement (negb aligned = true).
unfold aligned, target in Hfault. vm_compute in Hfault. discriminate Hfault.
Qed.

