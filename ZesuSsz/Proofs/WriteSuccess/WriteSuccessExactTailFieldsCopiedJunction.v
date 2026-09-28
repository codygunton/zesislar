Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
From Coq Require Import Lists.List.
Import ListNotations.
Open Scope Z_scope.

Lemma tail_fields_word_cons_equiv `{!islaG Sigma}
    (base : Z) (word : bv 64) (words : list (bv 64)) :
  (base ↦ₘ word ∗ (base + 8) ↦ₘ∗ words)%I ⊣⊢ base ↦ₘ∗ (word :: words).
Proof.
  iSplit.
  - iIntros "[Hword Hwords]"; iEval (rewrite -mem_mapsto_array_singleton) in "Hword"; iApply (mem_mapsto_array_app_combine 64 base (DfracOwn 1) [word] words with "Hword"); cbn; iExact "Hwords".
  - iIntros "Hwords"; iDestruct (mem_mapsto_array_app 64 base (DfracOwn 1) [word] words with "Hwords") as "[Hword Hwords]"; cbn; rewrite mem_mapsto_array_singleton; iFrame.
Qed.

Definition tailFieldsCopiedWords (decodedBytes : list (bv 8)) : list (bv 64) :=
  let words := writeSuccessPostTailWords decodedBytes in
  [writeSuccessPostWord words 1; writeSuccessPostWord words 0;
   writeSuccessPostWord words 3; writeSuccessPostWord words 2;
   writeSuccessPostWord words 5; writeSuccessPostWord words 4;
   writeSuccessPostWord words 6].

Definition tailFieldsCopiedUntouched `{!islaG Sigma}
    (sp : bv 64) (decodedBytes : list (bv 8)) : iProp Sigma :=
  let words := writeSuccessPostTailWords decodedBytes in
  ((bv_unsigned sp + 72) ↦ₘ writeSuccessPostWord words 7 ∗
   (bv_unsigned sp + 8) ↦ₘ writeSuccessPostWord words 8 ∗
   (bv_unsigned sp + 80) ↦ₘ writeSuccessPostWord words 9 ∗
   (bv_unsigned sp + 296) ↦ₘ writeSuccessPostWord words 10 ∗
   (bv_unsigned sp + 304) ↦ₘ writeSuccessPostWord words 11 ∗
   (bv_unsigned sp + 280) ↦ₘ writeSuccessPostWord words 12 ∗
   (bv_unsigned sp + 288) ↦ₘ writeSuccessPostWord words 13 ∗
   (bv_unsigned sp + 96) ↦ₘ writeSuccessPostWord words 14 ∗
   (bv_unsigned sp + 88) ↦ₘ writeSuccessPostWord words 15 ∗ True)%I.

Lemma tail_fields_copied_junction `{!islaG Sigma}
    (sp : bv 64) (decodedBytes : list (bv 8)) :
  writeSuccessExactCopiedTailWords sp decodedBytes ⊣⊢
  ((bv_unsigned sp + 16) ↦ₘ∗ tailFieldsCopiedWords decodedBytes ∗
   tailFieldsCopiedUntouched sp decodedBytes ∗ True)%I.
Proof.
  rewrite /writeSuccessExactCopiedTailWords /tailFieldsCopiedWords /tailFieldsCopiedUntouched /=.
  do 6 rewrite -tail_fields_word_cons_equiv.
  rewrite mem_mapsto_array_singleton -!Z.add_assoc /=.
  iSplit; [iIntros "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15)" | iIntros "((H1 & H0 & H3 & H2 & H5 & H4 & H6) & (H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & _) & _)"]; iFrame.
Qed.
Print Assumptions tail_fields_copied_junction.

Lemma tailFieldsCopiedUntouched_unfold `{!islaG Sigma}
    (sp : bv 64) (decodedBytes : list (bv 8)) :
  tailFieldsCopiedUntouched sp decodedBytes ⊣⊢
  let words := writeSuccessPostTailWords decodedBytes in
  ((bv_unsigned sp + 72) ↦ₘ writeSuccessPostWord words 7 ∗
   (bv_unsigned sp + 8) ↦ₘ writeSuccessPostWord words 8 ∗
   (bv_unsigned sp + 80) ↦ₘ writeSuccessPostWord words 9 ∗
   (bv_unsigned sp + 296) ↦ₘ writeSuccessPostWord words 10 ∗
   (bv_unsigned sp + 304) ↦ₘ writeSuccessPostWord words 11 ∗
   (bv_unsigned sp + 280) ↦ₘ writeSuccessPostWord words 12 ∗
   (bv_unsigned sp + 288) ↦ₘ writeSuccessPostWord words 13 ∗
   (bv_unsigned sp + 96) ↦ₘ writeSuccessPostWord words 14 ∗
   (bv_unsigned sp + 88) ↦ₘ writeSuccessPostWord words 15 ∗ True)%I.
Proof. done. Qed.
Global Opaque tailFieldsCopiedUntouched.
