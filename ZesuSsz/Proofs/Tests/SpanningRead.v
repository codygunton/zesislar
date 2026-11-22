From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* SpanningRead.zesu_read_span (decodeParentHeader 0514): an 8-byte read whose
   first byte is the last byte of a held 9-byte array (a word and a flag) and
   whose other seven bytes are the uninitialised region right after it. *)
Notation nine b0 b1 b2 b3 b4 b5 b6 b7 b8 := [b0; b1; b2; b3; b4; b5; b6; b7; b8].

Lemma test_read_span `{!islaG Sigma} `{!threadG} (B : Z) (b0 b1 b2 b3 b4 b5 b6 b7 b8 : bv 8)
    kind tag ann es (v : bv 64) :
  2684354560 <= B -> B + 32 <= 3221225472 ->
  B ↦ₘ∗ nine b0 b1 b2 b3 b4 b5 b6 b7 b8 -∗ (B + 9) ↦ₘ? 7 -∗
  (∀ values : list (bv 8), ⌜Z.of_nat (length values) = 7⌝ -∗
     ⌜v = Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8)
            (drop (Z.to_nat 8) (nine b0 b1 b2 b3 b4 b5 b6 b7 b8 ++ values))))⌝ -∗
     B ↦ₘ∗ nine b0 b1 b2 b3 b4 b5 b6 b7 b8 -∗ (B + 9) ↦ₘ? 7 -∗ WPasm es) -∗
  WPasm (ReadMem (RVal_Bits (@bv_to_bvn 64 v)) kind
    (RVal_Bits (@bv_to_bvn 64 (Z_to_bv 64 (B + 8)))) 8 tag ann :t: es).
Proof.
  intros HB HB'. iIntros "Hl Hu HK".
  ZesuSsz.Automation2.SpanningRead.zesu_read_span.
  iExact "HK".
Qed.

Print Assumptions test_read_span.

(* The read address is a local definition over another one (the `LET`
   binders of a trace): the root under them is found. *)
Lemma test_read_span_let_address `{!islaG Sigma} `{!threadG} (B : Z) (b0 b1 b2 b3 b4 b5 b6 b7 b8 : bv 8)
    kind tag ann es (v : bv 64) :
  2684354560 <= B -> B + 32 <= 3221225472 ->
  B ↦ₘ∗ nine b0 b1 b2 b3 b4 b5 b6 b7 b8 -∗ (B + 9) ↦ₘ? 7 -∗
  (∀ values : list (bv 8), ⌜Z.of_nat (length values) = 7⌝ -∗
     ⌜v = Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8)
            (drop (Z.to_nat 8) (nine b0 b1 b2 b3 b4 b5 b6 b7 b8 ++ values))))⌝ -∗
     B ↦ₘ∗ nine b0 b1 b2 b3 b4 b5 b6 b7 b8 -∗ (B + 9) ↦ₘ? 7 -∗ WPasm es) -∗
  WPasm (ReadMem (RVal_Bits (@bv_to_bvn 64 v)) kind
    (RVal_Bits (@bv_to_bvn 64 (bv_add (Z_to_bv 64 B) (BV 64 8)))) 8 tag ann :t: es).
Proof.
  intros HB HB'. iIntros "Hl Hu HK".
  set (LET0 := Z_to_bv 64 B). set (LET1 := bv_add LET0 (BV 64 8)).
  ZesuSsz.Automation2.SpanningRead.zesu_read_span.
  iExact "HK".
Qed.

(* Refused: a gap between the array and the region; no region after the
   array (the next piece is an array); a read that fits in the array; a
   one-byte read. *)
Lemma test_read_span_gap `{!islaG Sigma} `{!threadG} (B : Z) (l : list (bv 8))
    kind tag ann es (v : bv 64) :
  2684354560 <= B -> B + 32 <= 3221225472 -> length l = 9%nat ->
  let G := WPasm (ReadMem (RVal_Bits (@bv_to_bvn 64 v)) kind
    (RVal_Bits (@bv_to_bvn 64 (Z_to_bv 64 (B + 8)))) 8 tag ann :t: es) in
  G -∗ B ↦ₘ∗ l -∗ (B + 10) ↦ₘ? 7 -∗ G.
Proof.
  intros HB HB' Hlen G. iIntros "HG Hl Hu". unfold G.
  assert_fails (idtac; ZesuSsz.Automation2.SpanningRead.zesu_read_span).
  iExact "HG".
Qed.

Lemma test_read_span_next_array `{!islaG Sigma} `{!threadG} (B : Z) (l r : list (bv 8))
    kind tag ann es (v : bv 64) :
  2684354560 <= B -> B + 32 <= 3221225472 -> length l = 9%nat -> length r = 7%nat ->
  let G := WPasm (ReadMem (RVal_Bits (@bv_to_bvn 64 v)) kind
    (RVal_Bits (@bv_to_bvn 64 (Z_to_bv 64 (B + 8)))) 8 tag ann :t: es) in
  G -∗ B ↦ₘ∗ l -∗ (B + 9) ↦ₘ∗ r -∗ G.
Proof.
  intros HB HB' Hlen Hr G. iIntros "HG Hl Hr". unfold G.
  assert_fails (idtac; ZesuSsz.Automation2.SpanningRead.zesu_read_span).
  iExact "HG".
Qed.

Lemma test_read_span_inside `{!islaG Sigma} `{!threadG} (B : Z) (l : list (bv 8))
    kind tag ann es (v : bv 64) :
  2684354560 <= B -> B + 32 <= 3221225472 -> length l = 9%nat ->
  let G := WPasm (ReadMem (RVal_Bits (@bv_to_bvn 64 v)) kind
    (RVal_Bits (@bv_to_bvn 64 (Z_to_bv 64 (B + 1)))) 8 tag ann :t: es) in
  G -∗ B ↦ₘ∗ l -∗ (B + 9) ↦ₘ? 7 -∗ G.
Proof.
  intros HB HB' Hlen G. iIntros "HG Hl Hu". unfold G.
  assert_fails (idtac; ZesuSsz.Automation2.SpanningRead.zesu_read_span).
  iExact "HG".
Qed.

Lemma test_read_span_byte `{!islaG Sigma} `{!threadG} (B : Z) (l : list (bv 8))
    kind tag ann es (v : bv 8) :
  2684354560 <= B -> B + 32 <= 3221225472 -> length l = 9%nat ->
  let G := WPasm (ReadMem (RVal_Bits (@bv_to_bvn 8 v)) kind
    (RVal_Bits (@bv_to_bvn 64 (Z_to_bv 64 (B + 8)))) 1 tag ann :t: es) in
  G -∗ B ↦ₘ∗ l -∗ (B + 9) ↦ₘ? 7 -∗ G.
Proof.
  intros HB HB' Hlen G. iIntros "HG Hl Hu". unfold G.
  assert_fails (idtac; ZesuSsz.Automation2.SpanningRead.zesu_read_span).
  iExact "HG".
Qed.

(* Fires with a length fact instead of an explicit spine. *)
Lemma test_read_span_length_fact `{!islaG Sigma} `{!threadG} (B : Z) (l : list (bv 8))
    kind tag ann es (v : bv 64) :
  2684354560 <= B -> B + 32 <= 3221225472 -> length l = 9%nat ->
  B ↦ₘ∗ l -∗ (B + 9) ↦ₘ? 7 -∗
  (∀ values : list (bv 8), ⌜Z.of_nat (length values) = 7⌝ -∗
     ⌜v = Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8)
            (drop (Z.to_nat 8) (l ++ values))))⌝ -∗
     B ↦ₘ∗ l -∗ (B + 9) ↦ₘ? 7 -∗ WPasm es) -∗
  WPasm (ReadMem (RVal_Bits (@bv_to_bvn 64 v)) kind
    (RVal_Bits (@bv_to_bvn 64 (Z_to_bv 64 (B + 8)))) 8 tag ann :t: es).
Proof.
  intros HB HB' Hlen. iIntros "Hl Hu HK".
  ZesuSsz.Automation2.SpanningRead.zesu_read_span.
  iExact "HK".
Qed.
