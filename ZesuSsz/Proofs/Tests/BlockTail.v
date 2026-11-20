From Coq Require Import ZArith.ZArith Lists.List NArith.NArith.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* Each goal below is one shape that `zesu_block_tail_one` closes after the
   other tiers of `zesu_block2` have run. *)

(* A pure equation between two spellings of a loaded word. *)
Goal forall (bytes : list (bv 8)),
  Z_to_bv 16 (little_endian_to_bv 8 (take (N.to_nat 2) (drop 32 bytes))) =
  bv_concat 16 (nth 33 bytes (BV 8 0)) (nth 32 bytes (BV 8 0)).
Proof. intros bytes. zesu_block_tail_one. Qed.

(* A branch fact stated on the window while the goal reads byte positions. *)
Goal forall (bytes : list (bv 8)),
  bv_zero_extend 64 (Z_to_bv 16 (little_endian_to_bv 8 (take (N.to_nat 2) (drop 32 bytes)))) <> BV 64 0 ->
  bv_zero_extend 64 (bv_concat 16 (nth 33 bytes (BV 8 0)) (nth 32 bytes (BV 8 0))) <> BV 64 0.
Proof. intros bytes Hfact. zesu_block_tail_one. Qed.

(* The length of a list built from pieces of known length. *)
Goal forall (head tail : list (bv 8)),
  length head = 3%nat -> length tail = 5%nat -> length (head ++ tail) = 8%nat.
Proof. intros head tail Hhead Htail. zesu_block_tail_one. Qed.

(* A pure existential whose conjuncts are hypotheses, up to the round trip of
   an in-range integer. *)
Goal forall (P : Z -> Prop) (Q : bv 64 -> Prop) (z : Z),
  0 <= z < 4096 -> P (bv_unsigned (Z_to_bv 64 z)) -> Q (Z_to_bv 64 z) ->
  exists w, Q w /\ P z.
Proof.
  intros P Q z Hz HP HQ.
  zesu_block_tail_one.
Qed.

(* A pure existential whose last conjunct follows only from a folded
   precondition: the plain attempt fails, the folded fact is opened, and the
   conjunct is one of its parts. *)
Definition block_tail_folded_domain (z : Z) : Prop := 0 <= z /\ z < 4096.

Goal forall (P : Z -> Prop) (z : Z),
  block_tail_folded_domain z -> P z -> exists w, P w /\ 0 <= w.
Proof.
  intros P z Hdomain HP.
  zesu_block_tail_one.
Qed.

(* Nothing folded: the plain attempt closes the goal and the opening is not
   tried; with no folded fact the opening alone fails at once. *)
Goal forall (P : Z -> Prop) (z : Z),
  0 <= z -> P z -> exists w, P w /\ 0 <= w.
Proof.
  intros P z Hz HP.
  Fail ZesuSsz.Automation2.Hooks.zesu_open_folded_facts.
  zesu_block_tail_one.
Qed.

(* An edge premise: a boolean disjunction of branch guards. *)
Goal forall (w : bv 64),
  bv_unsigned w <> 0 ->
  orb (bool_decide (bv_unsigned w = 0)) (bool_decide (0 < bv_unsigned w)) = true.
Proof. intros w Hw. zesu_block_tail_one. Qed.

(* An edge premise: the fold over a zero-length window. *)
Goal forall (bytes : list (bv 8)) (start : nat) (count : Z),
  count = 0 ->
  bv_unsigned (BV 64 0) = ZesuSsz.Automation2.ByteWindowFold.zesu_byte_window_fold bytes start (Z.to_nat count).
Proof. intros bytes start count Hcount. zesu_block_tail_one. Qed.

(* Entering a loop head: the index starts at 0 and every invariant conjunct is
   an order fact of the context. *)
Lemma block_tail_loop_entry `{!islaG Σ} `{!threadG} (K : iProp Σ) (cursor bound : bv 64) :
  bv_unsigned cursor < bv_unsigned bound ->
  K ⊢ ∃ i : lvar "zesuLoopIndex" Z *ₗ (),
    ⌜(bv_unsigned cursor = bv_unsigned cursor + li_fst i)%Z⌝ ∗
    ⌜(0 <= li_fst i /\ bv_unsigned cursor < bv_unsigned bound)%Z⌝ ∗ K.
Proof. intros Hlt. iIntros "HK". zesu_block_tail_one. Qed.

(* Guard: an existential over a binder that is not the loop index is not a
   loop entry; the tail commits no witness for it. *)
Lemma block_tail_not_loop_entry `{!islaG Σ} `{!threadG} (K : iProp Σ) (cursor : bv 64) :
  K ⊢ ∃ i : lvar "otherIndex" Z *ₗ (), ⌜bv_unsigned cursor = li_fst i⌝ ∗ K.
Proof.
  iIntros "HK".
  Fail zesu_tail_loop_entry.
  iExists (li_pair (bv_unsigned cursor) tt). iSplit; [iPureIntro; reflexivity | iFrame].
Qed.

(* Guard: a boolean premise is split only when it is a disjunction or a
   negation; any other boolean equation is left to the other tiers. *)
Goal forall (w : bv 64), bv_unsigned w = 0 -> bool_decide (bv_unsigned w = 0) = true.
Proof.
  intros w Hw.
  Fail zesu_tail_bool_disj.
  apply bool_decide_eq_true_2. exact Hw.
Qed.

Print Assumptions block_tail_loop_entry.
