Require Import ZesuSsz.Automation.All.
Require Import lithium.interpreter lithium.pure_definitions.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import tactics environments.
From Coq Require Import ZArith.
From stdpp Require Import bitvector.tactics decidable.
Local Open Scope Z_scope.
Require Import ZesuSsz.Automation.MemoryTupleConsumer.
Require Import ZesuSsz.Automation.SourceFactMatching.
Lemma unused_positive : forall (Sigma : gFunctors) (P : bv 64 -> Prop) (value : bv 64), P value -> ((emp : iProp Sigma) ⊢ ∃ x : li_prod (bv 64) (li_prod (bv 64) unit), ⌜P (li_fst x)⌝)%I.
Proof. intros Sigma P value Hvalue. iIntros "_". MemoryTupleConsumer.zesu_memory_open_tuple constr:(16%nat). iPureIntro. eassumption. Qed.

Lemma unused_absent : True.
Proof. let candidate := open_constr:(_ : bv 64) in let bare := eval cbv beta iota zeta in candidate in MemoryTupleConsumer.zesu_memory_default_unused bare constr:(True); tryif has_evar bare then fail 100 "unused value remained unresolved" else idtac. exact I. Qed.

Lemma unused_occurring_refuses : forall value : bv 64, True.
Proof. intro value. let candidate := open_constr:(_ : bv 64) in let bare := eval cbv beta iota zeta in candidate in tryif MemoryTupleConsumer.zesu_memory_witness_occurs bare constr:(bare = bare) then (MemoryTupleConsumer.zesu_memory_default_unused bare constr:(bare = bare); tryif has_evar bare then unify bare value else fail 100 "used value was defaulted") else fail 100 "occurrence was missed". exact I. Qed.

Lemma source_correlated :
  forall (Sigma : gFunctors) (P Q : bv 64 -> Prop) (a b : bv 64),
  P a -> Q a -> P b ->
  ((emp : iProp Sigma) ⊢ ∃ x : li_prod (bv 64) unit,
     ⌜P (li_fst x)⌝ ∗ ⌜Q (li_fst x)⌝)%I.
Proof.
  intros Sigma P Q a b Hpa Hqa Hpb. iIntros "_".
  MemoryTupleConsumer.zesu_memory_open_tuple constr:(16%nat).
  lazymatch goal with |- environments.envs_entails _ ?requested =>
    SourceFactMatching.zesu_source_match_tree requested ltac:(idtac)
  end.
  SourceFactMatching.zesu_source_finish_package.
Qed.
