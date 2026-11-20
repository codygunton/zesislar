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
