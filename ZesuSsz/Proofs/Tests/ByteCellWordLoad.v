From Coq Require Import ZArith.ZArith.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The refusal checks below are `Fail` checks; this one makes sure the
   lemma they rely on exists, so they cannot pass for a missing name. *)
Check ZesuSsz.Automation2.ByteCellWords.zesu_byte_cells_to_array.

(* An opened 8-byte array: the saved word as eight single-byte cells in one
   hypothesis. A word lookup at its base folds the cells back into the
   byte array, which the array read rules accept. *)
Lemma byte_cells_word_lookup `{!islaG Sigma} `{!threadG} (base : Z) (word : bv 64) :
  ((base + Z.of_nat 0 * 1) ↦ₘ bv_extract 0 8 word ∗
   (base + Z.of_nat 1 * 1) ↦ₘ bv_extract 8 8 word ∗
   (base + Z.of_nat 2 * 1) ↦ₘ bv_extract 16 8 word ∗
   (base + Z.of_nat 3 * 1) ↦ₘ bv_extract 24 8 word ∗
   (base + Z.of_nat 4 * 1) ↦ₘ bv_extract 32 8 word ∗
   (base + Z.of_nat 5 * 1) ↦ₘ bv_extract 40 8 word ∗
   (base + Z.of_nat 6 * 1) ↦ₘ bv_extract 48 8 word ∗
   (base + Z.of_nat 7 * 1) ↦ₘ bv_extract 56 8 word ∗ emp) -∗
  find_in_context (FindMemMapsTo base) (fun _ => True%I).
Proof.
  iIntros "Hcells".
  liAStep.
  iApply find_in_context_mem_mapsto_semantic.
  iExists (MKArray 8%N base
    [bv_extract 0 8 word; bv_extract 8 8 word; bv_extract 16 8 word;
     bv_extract 24 8 word; bv_extract 32 8 word; bv_extract 40 8 word;
     bv_extract 48 8 word; bv_extract 56 8 word]).
  iSplitL "Hcells"; [rewrite /mem_mapsto_kind_prop; iExact "Hcells" | done].
Qed.

(* Positive pair for the refusals below: the fold closes the 8-cell lookup. *)
Check byte_cells_word_lookup.

(* Seven cells cannot hold a word: the fold refuses them. *)
Lemma byte_cells_short_refusal `{!islaG Sigma} `{!threadG} (base : Z) (word : bv 64) :
  ((base + Z.of_nat 0 * 1) ↦ₘ bv_extract 0 8 word ∗
   (base + Z.of_nat 1 * 1) ↦ₘ bv_extract 8 8 word ∗
   (base + Z.of_nat 2 * 1) ↦ₘ bv_extract 16 8 word ∗
   (base + Z.of_nat 3 * 1) ↦ₘ bv_extract 24 8 word ∗
   (base + Z.of_nat 4 * 1) ↦ₘ bv_extract 32 8 word ∗
   (base + Z.of_nat 5 * 1) ↦ₘ bv_extract 40 8 word ∗
   (base + Z.of_nat 6 * 1) ↦ₘ bv_extract 48 8 word ∗ emp) -∗
  find_in_context (FindMemMapsTo base) (fun _ => True%I).
Proof.
  iIntros "Hcells".
  Fail ZesuSsz.Automation2.ByteCellWords.zesu_byte_cells_fold.
  (* Same goal, closed by the plain lookup of cell 0. *)
  iApply find_in_context_mem_mapsto_semantic.
  iExists (MKMapsTo 8%N (bv_extract 0 8 word)).
  iDestruct "Hcells" as "[H0 _]".
  rewrite /mem_mapsto_kind_prop.
  replace (base + Z.of_nat 0 * 1) with base by lia.
  iSplitL "H0"; [iExact "H0" | done].
Qed.

(* A cell chain with a stride other than one byte is not a byte array. *)
Lemma byte_cells_stride_refusal `{!islaG Sigma} `{!threadG} (base : Z) (word : bv 64) :
  ((base + Z.of_nat 0 * 2) ↦ₘ bv_extract 0 8 word ∗
   (base + Z.of_nat 1 * 2) ↦ₘ bv_extract 8 8 word ∗
   (base + Z.of_nat 2 * 2) ↦ₘ bv_extract 16 8 word ∗
   (base + Z.of_nat 3 * 2) ↦ₘ bv_extract 24 8 word ∗
   (base + Z.of_nat 4 * 2) ↦ₘ bv_extract 32 8 word ∗
   (base + Z.of_nat 5 * 2) ↦ₘ bv_extract 40 8 word ∗
   (base + Z.of_nat 6 * 2) ↦ₘ bv_extract 48 8 word ∗
   (base + Z.of_nat 7 * 2) ↦ₘ bv_extract 56 8 word ∗ emp) -∗
  find_in_context (FindMemMapsTo base) (fun _ => True%I).
Proof.
  iIntros "Hcells".
  Fail ZesuSsz.Automation2.ByteCellWords.zesu_byte_cells_fold.
  (* Same goal, closed by the plain lookup of cell 0. *)
  iApply find_in_context_mem_mapsto_semantic.
  iExists (MKMapsTo 8%N (bv_extract 0 8 word)).
  iDestruct "Hcells" as "[H0 _]".
  rewrite /mem_mapsto_kind_prop.
  replace (base + Z.of_nat 0 * 2) with base by lia.
  iSplitL "H0"; [iExact "H0" | done].
Qed.

(* The loaded window of a saved frame (fp then ra bytes) is the saved word. *)
Lemma byte_cells_word_reload (base : Z) (saved returned : bv 64) :
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop
    (Z.to_nat (base + -64 + 56 - (base - 64 + 48)))
    [bv_extract 0 8 saved; bv_extract 8 8 saved; bv_extract 16 8 saved;
     bv_extract 24 8 saved; bv_extract 32 8 saved; bv_extract 40 8 saved;
     bv_extract 48 8 saved; bv_extract 56 8 saved;
     bv_extract 0 8 returned; bv_extract 8 8 returned; bv_extract 16 8 returned;
     bv_extract 24 8 returned; bv_extract 32 8 returned; bv_extract 40 8 returned;
     bv_extract 48 8 returned; bv_extract 56 8 returned]))) = returned.
Proof.
  ZesuSsz.Automation2.ByteWordReload.zesu_reload_byte_word_step.
  reflexivity.
Qed.

(* A window that is not the bytes of one word is not rewritten. *)
Lemma byte_cells_mixed_window_refusal (saved returned : bv 64) :
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat 4)
    [bv_extract 0 8 saved; bv_extract 8 8 saved; bv_extract 16 8 saved;
     bv_extract 24 8 saved; bv_extract 32 8 saved; bv_extract 40 8 saved;
     bv_extract 48 8 saved; bv_extract 56 8 saved;
     bv_extract 0 8 returned; bv_extract 8 8 returned; bv_extract 16 8 returned;
     bv_extract 24 8 returned]))) = returned -> True.
Proof.
  intros _.
  Fail ZesuSsz.Automation2.ByteWordReload.zesu_reload_byte_word_step.
  exact I.
Qed.

Print Assumptions byte_cells_word_lookup.
Print Assumptions byte_cells_word_reload.
