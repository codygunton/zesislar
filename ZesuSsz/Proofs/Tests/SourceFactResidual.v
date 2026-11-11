Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A merge-point entry can fix a meaning fact that no source closer proves.
   The block's residual lemma proves it from facts in context, so the
   fixed-fact check of a package passes without saturating the context. *)
Inductive source_residual_meaning (x : Z) : Prop :=
| source_residual_meaning_intro : 0 <= x -> source_residual_meaning x.

Lemma source_residual_meaning_of_range (x : Z) :
  0 <= x -> source_residual_meaning x.
Proof. intros Hx. constructor. exact Hx. Qed.
#[local] Hint Resolve source_residual_meaning_of_range : zesu_residual.

Lemma source_fact_uses_residual_lemma (x : Z) :
  0 <= x -> source_residual_meaning x.
Proof.
  intros Hx.
  ZesuSsz.Automation2.SourceFactMatching.zesu_source_fact.
Qed.

(* Without a residual lemma the closer still fails. *)
Goal forall x : Z, 0 <= x -> source_residual_meaning (x + 1) /\ True -> True.
Proof.
  intros x Hx _.
  assert_fails (idtac; assert (source_residual_meaning (x - 1)) by
    ZesuSsz.Automation2.SourceFactMatching.zesu_source_fact).
  exact I.
Qed.

Print Assumptions source_fact_uses_residual_lemma.
