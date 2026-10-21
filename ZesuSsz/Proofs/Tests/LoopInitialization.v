Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Compliance.DecodeItemLoopInitialization.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
From lithium Require Import lvar simpl_classes.
Open Scope Z_scope.

Section tests.
Context {Sigma : gFunctors}.

Lemma loop_initial_index args n ps bytes :
  decodeItemByteFoldFacts args n 0 ps bytes ->
  @SimplExist Sigma (lvar "zesuLoopIndex" Z) (fun P => P 0).
Proof. intro Hinitial. typeclasses eauto. Qed.

Lemma loop_initial_count args n ps bytes :
  decodeItemByteFoldFacts args n 0 ps bytes ->
  @SimplExist Sigma (lvar "zesuLoopCount" Z) (fun P => P n).
Proof. intro Hinitial. typeclasses eauto. Qed.

Lemma loop_backedge_before_initial args n ps bytes i m cursor :
  decodeItemByteFoldFacts args n 0 ps bytes -> i<m ->
  (Z_to_bv 64 (cursor+i) + 1)%bv <> Z_to_bv 64 (cursor+m) ->
  @SimplExist Sigma (lvar "zesuLoopIndex" Z) (fun P => P (i+1)).
Proof. intros Hinitial Hguard Hbranch. typeclasses eauto. Qed.

Lemma loop_backedge_count_before_initial args n ps bytes i m cursor :
  decodeItemByteFoldFacts args n 0 ps bytes -> i<m ->
  (Z_to_bv 64 (cursor+i) + 1)%bv <> Z_to_bv 64 (cursor+m) ->
  @SimplExist Sigma (lvar "zesuLoopCount" Z) (fun P => P m).
Proof. intros Hinitial Hguard Hbranch. typeclasses eauto. Qed.

Lemma loop_two_initial_facts_refuse args n ps bytes :
  decodeItemByteFoldFacts args n 0 ps bytes ->
  decodeItemByteFoldFacts args n 0 ps bytes -> True.
Proof.
  intros Hinitial Hother.
  Fail decodeItem_loop_initial_witness ltac:(fun count => idtac).
  exact I.
Qed.

Lemma loop_initial_refuses_backedge args n ps bytes i m cursor :
  decodeItemByteFoldFacts args n 0 ps bytes -> i<m ->
  (Z_to_bv 64 (cursor+i) + 1)%bv <> Z_to_bv 64 (cursor+m) -> True.
Proof.
  intros Hinitial Hguard Hbranch.
  Fail decodeItem_loop_initial_witness ltac:(fun count => idtac).
  exact I.
Qed.
End tests.
