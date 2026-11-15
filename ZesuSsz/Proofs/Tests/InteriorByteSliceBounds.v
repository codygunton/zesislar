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

(* The words bytes 0..7 and 8..15 of a callee output, in the load form. *)
Notation outWord0 bytes :=
  (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N
    (bv_concat 16%N (List.nth 7%nat bytes (BV 8%N 0%Z)) (List.nth 6%nat bytes (BV 8%N 0%Z)))
    (List.nth 5%nat bytes (BV 8%N 0%Z))) (List.nth 4%nat bytes (BV 8%N 0%Z)))
    (List.nth 3%nat bytes (BV 8%N 0%Z))) (List.nth 2%nat bytes (BV 8%N 0%Z)))
    (List.nth 1%nat bytes (BV 8%N 0%Z))) (List.nth 0%nat bytes (BV 8%N 0%Z))) (only parsing).
Notation outWord8 bytes :=
  (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N
    (bv_concat 16%N (List.nth 15%nat bytes (BV 8%N 0%Z)) (List.nth 14%nat bytes (BV 8%N 0%Z)))
    (List.nth 13%nat bytes (BV 8%N 0%Z))) (List.nth 12%nat bytes (BV 8%N 0%Z)))
    (List.nth 11%nat bytes (BV 8%N 0%Z))) (List.nth 10%nat bytes (BV 8%N 0%Z)))
    (List.nth 9%nat bytes (BV 8%N 0%Z))) (List.nth 8%nat bytes (BV 8%N 0%Z))) (only parsing).

(* A caller decodes its input, keeps the payload pointer and length under
   names, decodes the payload, then hands the next callee the payload's rest
   after the bytes the second call consumed. The payload lies in the input
   only under the interface's premise that its length is below 2^64 - 9,
   which follows from the input's own range: the input pointer's lower bound
   sits folded in the caller's precondition, with a named constant. *)
Record CursorArgs := { cursorInput : bv 64; cursorLength : bv 64; cursorBytes : list byte }.
Definition cursorInputLow : Z := 4096.
Definition cursorWellFormed (args : CursorArgs) : Prop :=
  Z.of_nat (length (cursorBytes args)) = bv_unsigned (cursorLength args) /\
  cursorInputLow <= bv_unsigned (cursorInput args).

Section kept_cursor.
Context (args : CursorArgs) (kept_ptr kept_len a0 b0 r3 r4 r5 r6 r7 sp : bv 64) (inputEnd : Z).
Context (before before0 first second : list byte).
Context (Hwf : cursorWellFormed args).
Context (Hdomain1 : decodeItemCallDomain
  (decodeItemCallDataArgs [a0; cursorInput args; cursorLength args; r3; r4; r5; r6; r7] sp inputEnd
    (cursorBytes args) before)).
Context (Hpost1 : decodeItemCallMeaning
  (decodeItemCallDataArgs [a0; cursorInput args; cursorLength args; r3; r4; r5; r6; r7] sp inputEnd
    (cursorBytes args) before) first).
Context (Hptr : zesu_named_eq kept_ptr (outWord0 first))
  (Hlen : zesu_named_eq kept_len (outWord8 first))
  (Hnonempty : bv_unsigned (outWord8 first) <> 0).
Context (Hdomain2 : decodeItemCallDomain
  (decodeItemCallDataArgs [b0; kept_ptr; kept_len; r3; r4; r5; r6; r7] sp inputEnd
    (take (Z.to_nat (bv_unsigned kept_len))
       (drop (Z.to_nat (bv_unsigned kept_ptr - bv_unsigned (cursorInput args))) (cursorBytes args)))
    before0)).
Context (Hpost2 : decodeItemCallMeaning
  (decodeItemCallDataArgs [b0; kept_ptr; kept_len; r3; r4; r5; r6; r7] sp inputEnd
    (take (Z.to_nat (bv_unsigned kept_len))
       (drop (Z.to_nat (bv_unsigned kept_ptr - bv_unsigned (cursorInput args))) (cursorBytes args)))
    before0) second).

Lemma test_interior_byte_slice_kept_cursor_start :
  bv_unsigned (cursorInput args) +
    Z.of_nat (Z.to_nat (bv_unsigned (kept_ptr + listWord64At24 second) -
      bv_unsigned (cursorInput args))) =
  bv_unsigned (kept_ptr + listWord64At24 second).
Proof using All.
  Fail zesu_byte_slice_bound_arith.
  zesu_byte_slice_bound_arith_at (bv_unsigned (cursorInput args)).
Qed.

Lemma test_interior_byte_slice_kept_cursor_bounds :
  (Z.to_nat (bv_unsigned (kept_ptr + listWord64At24 second) - bv_unsigned (cursorInput args)) +
   Z.to_nat (bv_unsigned (kept_len - listWord64At24 second)) <= length (cursorBytes args))%nat.
Proof using All. zesu_byte_slice_bound_arith_at (bv_unsigned (cursorInput args)). Qed.
End kept_cursor.

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
