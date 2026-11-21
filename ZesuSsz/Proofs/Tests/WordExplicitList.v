From Coq Require Import ZArith.ZArith Lists.List NArith.NArith.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A pointer word stored byte by byte and read back as a call argument: the
   explicit byte list is the word it came from. *)
Lemma word_explicit_list_pointer (z : Z) :
  Z_to_bv 64 (little_endian_to_bv 8
    [Z_to_bv 8 (z ≫ (8 * 0%nat)); Z_to_bv 8 (z ≫ (8 * 1%nat));
     Z_to_bv 8 (z ≫ (8 * 2%nat)); Z_to_bv 8 (z ≫ (8 * 3%nat));
     Z_to_bv 8 (z ≫ (8 * 4%nat)); Z_to_bv 8 (z ≫ (8 * 5%nat));
     Z_to_bv 8 (z ≫ (8 * 6%nat)); Z_to_bv 8 (z ≫ (8 * 7%nat))]) = Z_to_bv 64 z.
Proof. ZesuSsz.Automation2.WrappedWord.zesu_word_explicit_list_rewrite. reflexivity. Qed.

(* The same word under a binder of the goal, as in a call spec's
   existential. *)
Lemma word_explicit_list_under_binder (P : bv 16 -> Z -> Prop) (z : Z) :
  (forall x, P (Z_to_bv 16 z) x) ->
  forall x, P (Z_to_bv 16 (little_endian_to_bv 8
    [Z_to_bv 8 (z ≫ (8 * 0%nat)); Z_to_bv 8 (z ≫ (8 * 1%nat))])) x.
Proof.
  intros HP x.
  ZesuSsz.Automation2.WrappedWord.zesu_word_explicit_list_rewrite.
  apply HP.
Qed.

(* Guard: bytes not taken in order from one word are left alone. *)
Goal forall (z : Z),
  Z_to_bv 16 (little_endian_to_bv 8 [Z_to_bv 8 (z ≫ (8 * 1%nat)); Z_to_bv 8 (z ≫ (8 * 0%nat))]) =
  Z_to_bv 16 (little_endian_to_bv 8 [Z_to_bv 8 (z ≫ (8 * 1%nat)); Z_to_bv 8 (z ≫ (8 * 0%nat))]).
Proof.
  intros z.
  Fail ZesuSsz.Automation2.WrappedWord.zesu_word_explicit_list_rewrite.
  reflexivity.
Qed.

Print Assumptions word_explicit_list_pointer.

(* The word read back by an 8-byte load: `bv_concat` of the bytes of one
   integer. `bv_solve` closes it (WrappedWord.zesu_word_concat_bytes_eq). *)
Lemma word_concat_bytes (z : Z) :
  bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32 (bv_concat 24
    (bv_concat 16 (Z_to_bv 8 (z ≫ (8 * 7%nat))) (Z_to_bv 8 (z ≫ (8 * 6%nat))))
    (Z_to_bv 8 (z ≫ (8 * 5%nat)))) (Z_to_bv 8 (z ≫ (8 * 4%nat))))
    (Z_to_bv 8 (z ≫ (8 * 3%nat)))) (Z_to_bv 8 (z ≫ (8 * 2%nat))))
    (Z_to_bv 8 (z ≫ (8 * 1%nat)))) (Z_to_bv 8 (z ≫ (8 * 0%nat))) = Z_to_bv 64 z.
Proof. bv_solve. Qed.

(* Guard: a byte of another integer is refused. *)
Goal forall (z y : Z),
  bv_concat 16 (Z_to_bv 8 (y ≫ (8 * 1%nat))) (Z_to_bv 8 (z ≫ (8 * 0%nat))) = Z_to_bv 16 z ->
  bv_concat 16 (Z_to_bv 8 (y ≫ (8 * 1%nat))) (Z_to_bv 8 (z ≫ (8 * 0%nat))) = Z_to_bv 16 z.
Proof.
  intros z y H.
  Fail ZesuSsz.Automation2.WrappedWord.zesu_word_concat_bytes_eq.
  exact H.
Qed.

(* The rule proves the equation from its statement alone, in a context
   cleared of hypotheses: with a contradictory fact in the context, a word whose
   bytes are shifted wrongly is still refused (before the clear, bitblast's lia
   calls used the fact and proved it), and a right word still closes. *)
Goal forall (z : Z), (0 < 0)%Z ->
  bv_concat 16 (Z_to_bv 8 (z ≫ (8 * 0%nat))) (Z_to_bv 8 (z ≫ (8 * 1%nat))) = Z_to_bv 16 z.
Proof.
  intros z Hfalse.
  Fail ZesuSsz.Automation2.WrappedWord.zesu_word_concat_bytes_eq.
  lia.
Qed.
Goal forall (z : Z), (0 < 0)%Z ->
  bv_concat 16 (Z_to_bv 8 (z ≫ (8 * 1%nat))) (Z_to_bv 8 (z ≫ (8 * 0%nat))) = Z_to_bv 16 z.
Proof.
  intros z Hfalse.
  ZesuSsz.Automation2.WrappedWord.zesu_word_concat_bytes_eq.
Qed.

Print Assumptions word_concat_bytes.
