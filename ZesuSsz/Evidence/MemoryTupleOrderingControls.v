Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.MemoryTupleConsumer.
Require Import ZesuSsz.Automation.SourceFactMatching.
Require Import isla.riscv64.riscv64.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import tactics environments.
From Coq Require Import ZArith.
Open Scope Z_scope.

Section Controls.
Context (Sigma : gFunctors) (G : islaG Sigma).
#[local] Existing Instance G.

Lemma memory_ordering_correlated (address : Z) (fraction : dfrac)
    (bytes : list (bv 8)) (K : iProp Sigma) (P Q : bv 64 -> Prop)
    (a b : bv 64) (Hpa : P a) (Hqa : Q a) (Hpb : P b) :
  ⊢ (address ↦ₘ{fraction}∗ bytes ∗ K -∗
    ∃ x : li_prod (bv 64) unit,
      mem_mapsto_array_def address fraction bytes ∗
      ⌜P (li_fst x)⌝ ∗ ⌜Q (li_fst x)⌝ ∗ K)%I.
Proof.
  iIntros "[Harray HK]".
  MemoryTupleConsumer.zesu_memory_tuple
    ltac:(fun requested => SourceFactMatching.zesu_source_check_fixed_tree requested;
      SourceFactMatching.zesu_source_match_tree requested ltac:(idtac))
    ltac:(fun _ => SourceFactMatching.zesu_source_finish_package).
Qed.

Lemma memory_ordering_missing_fixed (P : bv 64 -> Prop) (a : bv 64)
    (Hpa : P a) : True.
Proof.
  assert_fails ltac:(assert (Hbad : forall (address : Z) (bytes : list (bv 8)),
    ⊢ (address ↦ₘ∗ bytes -∗ ∃ x : li_prod (bv 64) unit,
      mem_mapsto_array_def address (DfracOwn 1) bytes ∗
      ⌜P (li_fst x)⌝ ∗ ⌜False⌝)%I) by
    (intros address bytes; iIntros "Harray";
     solve [MemoryTupleConsumer.zesu_memory_tuple
       ltac:(fun requested => SourceFactMatching.zesu_source_check_fixed_tree requested;
         SourceFactMatching.zesu_source_match_tree requested ltac:(idtac))
       ltac:(fun _ => SourceFactMatching.zesu_source_finish_package)])).
  exact I.
Qed.
End Controls.
