From Coq Require Import ZArith.ZArith Lia.
Open Scope Z_scope.

Lemma zesu_loop_readable_window (base length cursor width alo ahi blo bhi : Z) :
  ((alo <= base /\ base + length <= ahi) \/ (blo <= base /\ base + length <= bhi)) ->
  base <= cursor -> cursor + width <= base + length ->
  ((alo <= cursor /\ cursor + width <= ahi) \/ (blo <= cursor /\ cursor + width <= bhi)).
Proof.
  intros [[Hlo Hhi] | [Hlo Hhi]] Hcursor Hread; [left | right]; split; lia.
Qed.

Lemma zesu_loop_readable_upper_refutation (cursor width alo ahi blo bhi : Z) :
  ((alo <= cursor /\ cursor + width <= ahi) \/ (blo <= cursor /\ cursor + width <= bhi)) ->
  0 < width -> ahi <= blo -> blo <= cursor -> ~ (cursor + width <= bhi) -> False.
Proof.
  intros [[Hlo Hhi] | [Hlo Hhi]] Hwidth Horder Hcursor Houtside; lia.
Qed.

Lemma zesu_loop_readable_lower_upper_refutation (cursor width alo ahi blo bhi : Z) :
  ((alo <= cursor /\ cursor + width <= ahi) \/ (blo <= cursor /\ cursor + width <= bhi)) ->
  cursor < blo -> ~ (cursor + width <= ahi) -> False.
Proof.
  intros [[Hlo Hhi] | [Hlo Hhi]] Hcursor Houtside; lia.
Qed.

Lemma zesu_loop_readable_below_refutation (cursor width alo ahi blo bhi : Z) :
  ((alo <= cursor /\ cursor + width <= ahi) \/ (blo <= cursor /\ cursor + width <= bhi)) ->
  cursor < alo -> cursor < blo -> False.
Proof.
  intros [[Hlo Hhi] | [Hlo Hhi]] Hfirst Hsecond; lia.
Qed.
