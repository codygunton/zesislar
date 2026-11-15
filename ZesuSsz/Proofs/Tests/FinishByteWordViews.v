From Coq Require Import ZArith.ZArith Lists.List NArith.NArith.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Import ListNotations.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A callee output word that a load reads as a little-endian window, stated
   by the successor as byte positions: the final pure step closes it. *)
Lemma byte_word_view_window (out : list (bv 8)) :
  Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop 8 out))) =
  bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32 (bv_concat 24
    (bv_concat 16 (nth 15 out (BV 8 0)) (nth 14 out (BV 8 0))) (nth 13 out (BV 8 0)))
    (nth 12 out (BV 8 0))) (nth 11 out (BV 8 0))) (nth 10 out (BV 8 0))) (nth 9 out (BV 8 0)))
    (nth 8 out (BV 8 0)).
Proof. zesu_finish_final_pure. Qed.

(* A branch fact on a window whose start is a word offset chain, and a goal on
   the same window at the literal start. *)
Lemma byte_word_view_branch_fact (out : list (bv 8)) (sp : bv 64) :
  bv_unsigned sp = 4096 ->
  bv_zero_extend 64 (Z_to_bv 16 (little_endian_to_bv 8 (take (N.to_nat 2)
    (drop (Z.to_nat (bv_unsigned (sp + BV 64 96) - (bv_unsigned sp + 64))) out)))) <> BV 64 0 ->
  bv_zero_extend 64 (Z_to_bv 16 (little_endian_to_bv 8 (take (N.to_nat 2) (drop 32 out)))) <> BV 64 0.
Proof. intros. zesu_finish_final_pure. Qed.

(* One bit of a word that a mask fact zeroes. *)
Lemma byte_word_view_single_bit (status : bv 64) :
  bv_and status (BV 64 131072) = BV 64 0 ->
  bv_extract 17 1 status <> BV 1 1 /\ bv_unsigned (bv_extract 17 1 status) <> 1.
Proof.
  intros. split.
  - zesu_finish_byte_word_views.
  - zesu_finish_byte_word_views.
Qed.

(* Another bit is not zeroed by the mask: the step fails. *)
Lemma byte_word_view_other_bit (status : bv 64) :
  bv_and status (BV 64 131072) = BV 64 0 ->
  bv_extract 18 1 status = bv_extract 18 1 status.
Proof.
  intros. Fail zesu_finish_byte_word_views. reflexivity.
Qed.
