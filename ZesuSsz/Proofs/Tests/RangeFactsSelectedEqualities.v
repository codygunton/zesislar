Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
Lemma selected_bv_equality_two_hops (a b c d e unrelated : bv 64)
 (Hrange : bv_unsigned a < bv_unsigned b)
 (Hfirst : b = c) (Hsecond : c = d) (Hthird : d = e) (Hother : unrelated = 0%bv) : True.
Proof.
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_collect
   constr:(bv_unsigned a) constr:(bv_unsigned a) constr:(a)).
 clear Hrange Hfirst Hsecond Hthird Hother.
 assert (HselectedFirst : b = c) by assumption.
 assert (HselectedSecond : c = d) by assumption.
 Fail assert (HthirdSelected : d = e) by assumption.
 Fail assert (HunrelatedSelected : unrelated = 0%bv) by assumption.
 exact I.
Qed.
Lemma selected_string_equality_stays_excluded (a : bv 64) (left right : string)
 (Hrange : bv_unsigned a < 10) (Htext : left = right) : True.
Proof.
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_collect
   constr:(bv_unsigned a) constr:(bv_unsigned a) constr:(a)).
 clear Htext Hrange.
 Fail assert (HtextSelected : left = right) by assumption.
 exact I.
Qed.
Lemma selected_bv_preserves_unused_evar (a : bv 64)
 (Hrange : bv_unsigned a < 10) : True.
Proof.
 let witness := open_constr:(_ : bv 64) in
 let bare := eval hnf in witness in
 is_evar bare;
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_collect
   constr:(bv_unsigned a) constr:(bv_unsigned a) constr:(a));
 is_evar bare; unify bare (Z_to_bv 64 0).
 exact I.
Qed.
