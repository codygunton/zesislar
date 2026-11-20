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

(* An edge premise: a branch disjunction in `Prop` form. The context decides
   no disjunct directly; a case split on the goal's equations does, and the
   last case closes by a branch fact stated on the window. *)
Lemma block_tail_prop_disj (x y : bv 64) (bytes : list (bv 8)) :
  ~ (8 >= bv_unsigned (Z_to_bv 16 (little_endian_to_bv 8 (take (N.to_nat 2) (drop 32 bytes)))))%Z ->
  bv_unsigned x <> 0 \/
  (bv_unsigned x = 0 /\ bv_unsigned y <> 0) \/
  (bv_unsigned x = 0 /\ bv_unsigned y = 0 /\
   8 < bv_unsigned (bv_concat 16 (nth 33 bytes (BV 8 0)) (nth 32 bytes (BV 8 0)))).
Proof. intros Hwin. zesu_block_tail_one. Qed.

(* Guard: a disjunct the context decides closes without a case split; a
   disjunction no case decides is left untouched. *)
Goal forall (x y : bv 64), bv_unsigned y <> 0 -> bv_unsigned x = 0 \/ bv_unsigned y <> 0.
Proof. intros x y Hy. zesu_tail_prop_disj. Qed.
Goal forall (x y : bv 64), bv_unsigned x = 0 \/ bv_unsigned y = 0 \/ True.
Proof.
  intros x y.
  Fail zesu_tail_prop_disj.
  right; right; exact I.
Qed.

(* Entering a loop head whose invariant states the loop guard as a boolean:
   the context holds the guard in `Prop` form. *)
Lemma block_tail_loop_entry_guard `{!islaG Σ} `{!threadG} (K : iProp Σ) (w : bv 64) :
  w <> BV 64 0 ->
  K ⊢ ∃ i : lvar "zesuLoopIndex" Z *ₗ (),
    ⌜(0 <= li_fst i)%Z⌝ ∗ ⌜negb (bool_decide (w = BV 64 0)) = true⌝ ∗ K.
Proof. intros Hw. iIntros "HK". zesu_block_tail_one. Qed.

(* Guard: without the guard fact the conjunct stays open after the loop
   entry. *)
Lemma block_tail_loop_entry_guard_open `{!islaG Σ} `{!threadG} (K : iProp Σ) (P : bv 64 -> Prop) (w : bv 64) :
  (forall v, P v -> v <> BV 64 0) -> P w ->
  K ⊢ ∃ i : lvar "zesuLoopIndex" Z *ₗ (),
    ⌜negb (bool_decide (w = BV 64 0)) = true⌝ ∗ K.
Proof.
  intros Himp HP. iIntros "HK".
  zesu_tail_loop_entry.
  lazymatch goal with |- negb (bool_decide _) = true => idtac end.
  rewrite negb_true_iff; apply bool_decide_eq_false; exact (Himp w HP).
Qed.

(* A call record the call step wrote with integer words and the lent window,
   against the successor's record with the words as loaded and the whole
   array (nextUint64 0000 at the return to 0044). *)
Local Notation loaded_word z :=
  (bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32 (bv_concat 24 (bv_concat 16
     (Z_to_bv 8 (z ≫ (8 * 7%nat))) (Z_to_bv 8 (z ≫ (8 * 6%nat))))
     (Z_to_bv 8 (z ≫ (8 * 5%nat)))) (Z_to_bv 8 (z ≫ (8 * 4%nat))))
     (Z_to_bv 8 (z ≫ (8 * 3%nat)))) (Z_to_bv 8 (z ≫ (8 * 2%nat))))
     (Z_to_bv 8 (z ≫ (8 * 1%nat)))) (Z_to_bv 8 (z ≫ (8 * 0%nat)))).

Lemma block_tail_call_record (D : list (bv 64) -> list (bv 8) -> Prop)
    (M : list (bv 64) -> list (bv 8) -> Z -> Prop) (p : Z) (bytes : list (bv 8)) (x : bv 64) (r : Z) :
  0 <= p -> p + Z.of_nat (length bytes) < 18446744073709551616 ->
  D [Z_to_bv 64 p; Z_to_bv 64 (Z.of_nat (length bytes)); x]
    (take (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (length bytes)))))
       (drop (Z.to_nat (bv_unsigned (Z_to_bv 64 p) - p)) bytes)) ->
  M [Z_to_bv 64 p; Z_to_bv 64 (Z.of_nat (length bytes)); x]
    (take (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (length bytes)))))
       (drop (Z.to_nat (bv_unsigned (Z_to_bv 64 p) - p)) bytes)) r ->
  exists y : bv 64,
    D [loaded_word p; loaded_word (Z.of_nat (length bytes)); y] bytes /\
    M [loaded_word p; loaded_word (Z.of_nat (length bytes)); y] bytes r.
Proof.
  intros Hp Hfit HD HM.
  Fail solve [ZesuSsz.Automation2.BlockTail.zesu_tail_exists_conj_core].
  zesu_block_tail_one.
Qed.

(* Guards: a word whose bytes come from two integers is not rewritten; a
   window that does not start at the array's base is not the array; a window
   over an array the goal does not name is not touched. *)
Goal forall (Q : bv 16 -> Prop) (a b : Z),
  Q (bv_concat 16 (Z_to_bv 8 (b ≫ 8)) (Z_to_bv 8 (a ≫ 0))) ->
  Q (bv_concat 16 (Z_to_bv 8 (b ≫ 8)) (Z_to_bv 8 (a ≫ 0))).
Proof.
  intros Q a b HQ.
  Fail ZesuSsz.Automation2.BlockTail.zesu_tail_word_views.
  exact HQ.
Qed.
Goal forall (Q : bv 16 -> Prop) (a : Z),
  Q (Z_to_bv 16 a) -> Q (bv_concat 16 (Z_to_bv 8 (a ≫ 8)) (Z_to_bv 8 (a ≫ 0))).
Proof.
  intros Q a HQ.
  ZesuSsz.Automation2.BlockTail.zesu_tail_word_views.
  exact HQ.
Qed.
Goal forall (P : list (bv 8) -> Prop) (p : Z) (bytes : list (bv 8)),
  1 <= p -> p + Z.of_nat (length bytes) < 18446744073709551616 ->
  P (take (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (length bytes)))))
       (drop (Z.to_nat (bv_unsigned (Z_to_bv 64 p) - (p - 1))) bytes)) ->
  P bytes -> P bytes.
Proof.
  intros P p bytes Hp Hfit HP HQ.
  Fail ZesuSsz.Automation2.BlockTail.zesu_tail_whole_slice_views.
  exact HQ.
Qed.
Goal forall (P : list (bv 8) -> Prop) (p : Z) (bytes other : list (bv 8)),
  0 <= p -> p + Z.of_nat (length bytes) < 18446744073709551616 ->
  P (take (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (length bytes)))))
       (drop (Z.to_nat (bv_unsigned (Z_to_bv 64 p) - p)) bytes)) ->
  P other -> P other.
Proof.
  intros P p bytes other Hp Hfit HP HQ.
  Fail ZesuSsz.Automation2.BlockTail.zesu_tail_whole_slice_views.
  exact HQ.
Qed.

Print Assumptions block_tail_loop_entry.

(* A callee interface's derived payload window has a strict upper premise
   `a < k`: the forward step proves both premises from the branch facts and
   keeps the window; without it the window stays an implication. *)
Lemma block_tail_forward_strict_window (w : bv 64) (p q : Z) :
  bv_unsigned w <> 0 -> 8 >= bv_unsigned w ->
  (0 < bv_unsigned w -> bv_unsigned w < 18446744073709551607 -> p <= q /\ q <= p + 5) ->
  p <= q.
Proof.
  intros Hnonzero Hsmall Hwindow.
  zesu_tail_forward_window_facts.
  assumption.
Qed.

Print Assumptions block_tail_forward_strict_window.

(* A loop-entry window conjunct `W0 < W0 + W8` (bit-vector sum): the sum is
   exact only through a callee's derived length fact, a conjunction
   `n = len /\ p + n < m`, which the order-fact selection keeps as its two
   parts. *)
Lemma block_tail_lia_conj_fact (w0 w8 : bv 64) (k n len : Z) :
  bv_unsigned w8 <> 0 ->
  bv_unsigned w0 + bv_unsigned w8 <= k + len ->
  (n = len /\ k + n < 18446744073709551616) ->
  bv_unsigned w0 < bv_unsigned (bv_add w0 w8).
Proof.
  intros Hnonzero Hwindow Hlen.
  solve [zesu_tail_add_exact_rewrite; zesu_tail_lia_select].
Qed.

(* Guard: a conjunction with a part outside linear order facts (`mod`) is not
   kept, neither whole nor in parts. *)
Goal forall (n len : Z), (n = len /\ n mod 2 = 0) -> n <= len.
Proof.
  intros n len Hlen.
  Fail solve [zesu_tail_lia_select].
  destruct Hlen as [-> _]. lia.
Qed.

Print Assumptions block_tail_lia_conj_fact.
