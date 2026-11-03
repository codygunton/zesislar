Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.MemoryTupleConsumer.
Require Import ZesuSsz.Automation.SourceFactMatching.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import tactics environments.
From Coq Require Import ZArith.
From stdpp Require Import list.
Local Open Scope Z_scope.

Section Controls.
Context (Sigma : gFunctors) (G : islaG Sigma) `{!threadG}.
#[local] Existing Instance G.

Definition memory_folded_package (address : Z) (fraction : dfrac)
    (low high : bv 64) (K : iProp Sigma) : iProp Sigma :=
  (∃ x : li_prod (bv 64) unit,
    "value" ↦ᵣ RVal_Bits (li_fst x) ∗
    mem_mapsto_array_def address fraction
      (bv_to_little_endian 8 8 (bv_unsigned low) ++
       bv_to_little_endian 8 8 (bv_unsigned high)) ∗
    ⌜li_fst x = low⌝ ∗ K)%I.
#[local] Instance memory_folded_package_unfold :
  LithiumUnfold memory_folded_package := I.
#[local] Instance memory_folded_package_intro address fraction low high K :
  Hooks.ZesuPureFactIntro (memory_folded_package address fraction low high K)
    (∃ x : li_prod (bv 64) unit,
      "value" ↦ᵣ RVal_Bits (li_fst x) ∗
      mem_mapsto_array_def address fraction
        (bv_to_little_endian 8 8 (bv_unsigned low) ++
         bv_to_little_endian 8 8 (bv_unsigned high)) ∗
      ⌜li_fst x = low⌝ ∗ K)%I.
Proof. unfold memory_folded_package. done. Qed.
#[local] Typeclasses Opaque memory_folded_package.

Ltac consume := MemoryTupleConsumer.zesu_memory_tuple
  ltac:(fun requested => SourceFactMatching.zesu_source_check_fixed_tree requested;
    SourceFactMatching.zesu_source_match_tree requested ltac:(idtac))
  ltac:(fun _ => SourceFactMatching.zesu_source_finish_package).

Lemma memory_folded_words (address : Z) (fraction : dfrac)
    (low high : bv 64) (K : iProp Sigma) :
  ⊢ ("value" ↦ᵣ RVal_Bits low ∗ address ↦ₘ{fraction} low ∗
    (address + 8) ↦ₘ{fraction} high ∗ K -∗
    memory_folded_package address fraction low high K)%I.
Proof. iIntros "(Hvalue & Hlow & Hhigh & HK)". consume. Qed.

Lemma memory_folded_words_anonymous (address : Z) (fraction : dfrac)
    (low high : bv 64) (K : iProp Sigma) :
  ⊢ ("value" ↦ᵣ RVal_Bits low ∗ address ↦ₘ{fraction} low ∗
    (address + 8) ↦ₘ{fraction} high ∗ K -∗
    memory_folded_package address fraction low high K)%I.
Proof. iIntros "(? & ? & ? & ?)". consume. Qed.

Lemma memory_adjacent_arrays (address : Z) (fraction : dfrac)
    (low high : bv 64) :
  ⊢ (address ↦ₘ{fraction}∗ bv_to_little_endian 8 8 (bv_unsigned low) ∗
    (address + 8) ↦ₘ{fraction}∗ bv_to_little_endian 8 8 (bv_unsigned high) -∗
    mem_mapsto_array_def address fraction
      (bv_to_little_endian 8 8 (bv_unsigned low) ++
       bv_to_little_endian 8 8 (bv_unsigned high)) ∗ ⌜True⌝)%I.
Proof. iIntros "[Hlow Hhigh]". consume. Qed.

Lemma memory_fraction_refuses (address : Z) (low high : bv 64) : True.
Proof.
  assert_fails ltac:(assert (Hbad :
    ⊢ (address ↦ₘ{DfracDiscarded} low ∗
      (address + 8) ↦ₘ{DfracDiscarded} high -∗
      mem_mapsto_array_def address (DfracOwn 1)
        (bv_to_little_endian 8 8 (bv_unsigned low) ++
         bv_to_little_endian 8 8 (bv_unsigned high)) ∗ ⌜True⌝)%I) by
    (iIntros "[Hlow Hhigh]"; solve [consume])).
  exact I.
Qed.
End Controls.
