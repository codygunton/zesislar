From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Automation2.InteriorByteSlice.
Import ListNotations.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The consumed count at bytes 24..31, in the load form the block generator
   renders. *)
Notation listWord64At24 bytes :=
  (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N
    (bv_concat 16%N (List.nth 31%nat bytes (BV 8%N 0%Z)) (List.nth 30%nat bytes (BV 8%N 0%Z)))
    (List.nth 29%nat bytes (BV 8%N 0%Z))) (List.nth 28%nat bytes (BV 8%N 0%Z)))
    (List.nth 27%nat bytes (BV 8%N 0%Z))) (List.nth 26%nat bytes (BV 8%N 0%Z)))
    (List.nth 25%nat bytes (BV 8%N 0%Z))) (List.nth 24%nat bytes (BV 8%N 0%Z))) (only parsing).

(* A caller hands a callee the rest of an input slice after the bytes an
   earlier call consumed: start and size are symbolic. The bounds follow from
   the earlier call's sealed domain and post (its consumed count) by the
   derived facts that decodeItem's interface registers. *)
Section bounds.
Context (base cursor remaining a0 r3 r4 r5 r6 r7 sp : bv 64) (inputEnd : Z).
Context (bytes before after : list byte).
Context (Hdomain : decodeItemCallDomain
  (decodeItemCallDataArgs [a0; cursor; remaining; r3; r4; r5; r6; r7] sp inputEnd
    (take (Z.to_nat (bv_unsigned remaining))
       (drop (Z.to_nat (bv_unsigned cursor - bv_unsigned base)) bytes)) before)).
Context (Hpost : decodeItemCallMeaning
  (decodeItemCallDataArgs [a0; cursor; remaining; r3; r4; r5; r6; r7] sp inputEnd
    (take (Z.to_nat (bv_unsigned remaining))
       (drop (Z.to_nat (bv_unsigned cursor - bv_unsigned base)) bytes)) before) after).
Context (Hlow : bv_unsigned base <= bv_unsigned cursor)
  (Hhigh : bv_unsigned cursor <= bv_unsigned base + Z.of_nat (length bytes)).

Lemma test_interior_byte_slice_symbolic_start :
  bv_unsigned base +
    Z.of_nat (Z.to_nat (bv_unsigned (cursor + listWord64At24 after) - bv_unsigned base)) =
  bv_unsigned (cursor + listWord64At24 after).
Proof using All. zesu_byte_slice_bound_arith. Qed.

Lemma test_interior_byte_slice_symbolic_bounds :
  (Z.to_nat (bv_unsigned (cursor + listWord64At24 after) - bv_unsigned base) +
   Z.to_nat (bv_unsigned (remaining - listWord64At24 after)) <= length bytes)%nat.
Proof using All. zesu_byte_slice_bound_arith. Qed.
End bounds.

(* The slice size is a word read from a callee's output bytes: its count is
   `Z.to_nat` of the word, equal to the size because the word is unsigned. *)
Section word_size.
Context `{!islaG Sigma} `{!threadG}.
Lemma test_interior_byte_slice_word_size (base start : Z) (bytes out : list byte) :
  0 <= start ->
  start + bv_unsigned (bv_concat 16 (List.nth 1 out (BV 8 0)) (List.nth 0 out (BV 8 0))) <=
    Z.of_nat (length bytes) ->
  base ↦ₘ∗ bytes -∗
  ∃ x : list byte *ₗ (),
    (base + start) ↦ₘ∗ x.1ₗ ∗
    ⌜bv_unsigned (bv_concat 16 (List.nth 1 out (BV 8 0)) (List.nth 0 out (BV 8 0))) =
       Z.of_nat (length x.1ₗ)⌝ ∗ True.
Proof.
  iIntros (Hstart Hfits) "Harray".
  zesu_lend_interior_byte_slice.
  cbn [li_fst]. iFrame. iPureIntro. zesu_byte_slice_bound_arith.
Qed.
End word_size.
