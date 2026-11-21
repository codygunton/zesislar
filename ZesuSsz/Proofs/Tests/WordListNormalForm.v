From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* decodeParentHeader 046c/04f8: the stored eight bytes of a word, as a list
   equation with three spellings of the same bytes: a `take`/`drop` count
   that is a frame offset (literal 0), a byte written by a store as
   `Z_to_bv 8 (Z.land (… ≫ 8) (Z.ones 8))` of the word's value, and the word
   itself as a load window `take 8 (drop 24 l)` against `bv_concat` of
   `nth k l`. One word normal form (WrappedWord.zesu_word_list_counts,
   WrappedWord.zesu_word_byte_extract_rewrite, the window rewrite of
   BytePositionEquations) makes both sides the same list; the list closer of
   the finisher (Finish.zesu_finish_known_list_shape) proves it. *)

(* The count spelling: a frame offset becomes its literal. *)
Lemma test_word_list_count (sp : bv 64) (l : list (bv 8)) :
  2684354560 <= bv_unsigned sp < 3221225472 ->
  take (Z.to_nat (bv_unsigned (sp + BV 64 18446744073709551216 + BV 64 400) - (bv_unsigned sp - 400 + 400))) l
  ++ drop (Z.to_nat (bv_unsigned (sp + BV 64 18446744073709551216 + BV 64 400) - (bv_unsigned sp - 400 + 400)) + N.to_nat 0) l
  = l.
Proof. intros Hsp. ZesuSsz.Automation2.WrappedWord.zesu_word_list_counts. reflexivity. Qed.

(* The same count in a context above the project lia's node budget (a
   block's context, decodeParentHeader 046c/04f8): `zesu_lia` refuses there,
   and the index is proved over the root's value alone. *)
Ltac test_doubled t n :=
  lazymatch n with O => t | S ?m => test_doubled constr:((t + t)%Z) m end.
Lemma test_word_list_count_large_context (sp : bv 64) (l : list (bv 8)) (x : Z) :
  2684354560 <= bv_unsigned sp < 3221225472 ->
  take (Z.to_nat (bv_unsigned (sp + BV 64 18446744073709551216 + BV 64 400) - (bv_unsigned sp - 400 + 400))) l
  ++ drop (Z.to_nat (bv_unsigned (sp + BV 64 18446744073709551216 + BV 64 400) - (bv_unsigned sp - 400 + 400)) + N.to_nat 0) l
  = l.
Proof.
  intros Hsp.
  let t := test_doubled x 16%nat in
  assert (Hbig : bv_unsigned (sp + BV 64 8) + t = bv_unsigned (sp + BV 64 8) + t) by reflexivity.
  assert_fails (assert (bv_unsigned (sp + BV 64 8) + 0 = bv_unsigned (sp + BV 64 8)) by zesu_lia).
  ZesuSsz.Automation2.WrappedWord.zesu_word_list_counts. reflexivity.
Qed.

(* An index that keeps a variable is not a literal: left alone. *)
Lemma test_word_list_count_variable (z : Z) (l : list (bv 8)) :
  take (Z.to_nat z) l = take (Z.to_nat z) l.
Proof.
  ZesuSsz.Automation2.WrappedWord.zesu_word_list_counts.
  lazymatch goal with |- take (Z.to_nat z) l = _ => reflexivity end.
Qed.

(* The byte spelling: mask and nested shifts of a word's value, as its extract. *)
Lemma test_word_byte_extract (x : bv 64) :
  [Z_to_bv 8 (Z.land (bv_unsigned x) (Z.ones 8));
   Z_to_bv 8 (Z.land ((bv_unsigned x ≫ 8) ≫ 8) (Z.ones 8))] =
  [bv_extract 0 8 x; bv_extract 16 8 x].
Proof.
  ZesuSsz.Automation2.WrappedWord.zesu_word_byte_extract_rewrite.
  lazymatch goal with |- [bv_extract 0 8 x; bv_extract 16 8 x] = _ => reflexivity end.
Qed.

(* A byte's own value is not an extract of a wider word: left alone. *)
Lemma test_word_byte_extract_byte (b : bv 8) :
  Z_to_bv 8 (bv_unsigned b) = Z_to_bv 8 (bv_unsigned b).
Proof.
  assert_fails (progress ZesuSsz.Automation2.WrappedWord.zesu_word_byte_extract_rewrite).
  reflexivity.
Qed.

Notation extracts v :=
  [bv_extract 0 8 v; bv_extract 8 8 v; bv_extract 16 8 v; bv_extract 24 8 v;
   bv_extract 32 8 v; bv_extract 40 8 v; bv_extract 48 8 v; bv_extract 56 8 v].
Notation value_bytes x :=
  [Z_to_bv 8 (Z.land (bv_unsigned x) (Z.ones 8));
   Z_to_bv 8 (Z.land (bv_unsigned x ≫ 8) (Z.ones 8));
   Z_to_bv 8 (Z.land ((bv_unsigned x ≫ 8) ≫ 8) (Z.ones 8));
   Z_to_bv 8 (Z.land (((bv_unsigned x ≫ 8) ≫ 8) ≫ 8) (Z.ones 8));
   Z_to_bv 8 (Z.land ((((bv_unsigned x ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8));
   Z_to_bv 8 (Z.land (((((bv_unsigned x ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8));
   Z_to_bv 8 (Z.land ((((((bv_unsigned x ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8));
   Z_to_bv 8 (Z.land (((((((bv_unsigned x ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8))].

(* The whole equation of 046c (04f8 has the same shape). *)
Lemma test_word_list_normal_form (sp v w : bv 64) (after : list (bv 8)) :
  2684354560 + 512 <= bv_unsigned sp < 3221225472 ->
  take (Z.to_nat (bv_unsigned (sp + BV 64 18446744073709551216 + BV 64 400 + BV 64 18446744073709551264) -
                  (bv_unsigned sp - 400 + 48))) (extracts v) ++
  value_bytes (bv_add w (Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop 24 after))))) ++
  drop (Z.to_nat (bv_unsigned (sp + BV 64 18446744073709551216 + BV 64 400 + BV 64 18446744073709551264) -
                  (bv_unsigned sp - 400 + 48)) + N.to_nat 8) (extracts v) =
  extracts (bv_add w (bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32 (bv_concat 24
              (bv_concat 16 (nth 31 after (BV 8 0)) (nth 30 after (BV 8 0))) (nth 29 after (BV 8 0)))
              (nth 28 after (BV 8 0))) (nth 27 after (BV 8 0))) (nth 26 after (BV 8 0)))
              (nth 25 after (BV 8 0))) (nth 24 after (BV 8 0)))).
Proof. intros Hsp. ZesuSsz.Automation2.Finish.zesu_finish_known_list_shape. Qed.
