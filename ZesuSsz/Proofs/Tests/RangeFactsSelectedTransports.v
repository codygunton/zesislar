Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
Lemma selected_boolean_order (a b c d : Z)
 (Hselected : Z.ltb a b = true) (Hother : Z.leb c d = true) : True.
Proof.
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_collect constr:(a) constr:(a) constr:(a)).
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_isolate ()).
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_reflect_selected_all ()).
 assert (Horder : a < b) by assumption.
 Fail assert (Hunrelated : c <= d) by assumption.
 exact I.
Qed.
Lemma selected_negated_boolean_order (a b : Z)
 (Hselected : negb (bool_decide (a >= b)) = true) : True.
Proof.
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_collect constr:(a) constr:(a) constr:(a)).
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_isolate ()).
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_reflect_selected_all ()).
 assert (Horder : a < b) by assumption.
 exact I.
Qed.
Lemma selected_endpoint_no_wrap (endpoint lhs rhs : bv 64)
 (Hendpoint : endpoint = (lhs + rhs)%bv)
 (Hsum : 0 <= bv_unsigned lhs + bv_unsigned rhs < 2^64) : True.
Proof.
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_collect constr:(bv_unsigned lhs) constr:(bv_unsigned lhs) constr:(lhs)).
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_isolate ()).
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_unsigned_selected_all ()).
 ZesuSsz.Automation2.RangeFacts.zesu_range_selected_no_wrap.
 assert (Harithmetic : bv_unsigned endpoint = bv_unsigned lhs + bv_unsigned rhs) by assumption.
 exact I.
Qed.
Lemma selected_endpoint_keeps_wrap (endpoint lhs rhs : bv 64)
 (Hendpoint : endpoint = (lhs + rhs)%bv)
 (Hwrapped : 2^64 <= bv_unsigned lhs + bv_unsigned rhs) : True.
Proof.
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_collect constr:(bv_unsigned lhs) constr:(bv_unsigned lhs) constr:(lhs)).
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_isolate ()).
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_unsigned_selected_all ()).
 ZesuSsz.Automation2.RangeFacts.zesu_range_selected_no_wrap.
 assert (Hmodular : bv_unsigned endpoint = bv_wrap 64 (bv_unsigned lhs + bv_unsigned rhs)) by assumption.
 Fail assert (Harithmetic : bv_unsigned endpoint = bv_unsigned lhs + bv_unsigned rhs) by assumption.
 exact I.
Qed.
Lemma selected_boolean_variable_answer_refuses (a b : Z) (answer : bool)
 (Hselected : Z.ltb a b = answer) : True.
Proof.
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_collect constr:(a) constr:(a) constr:(a)).
 clear Hselected.
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_reflect_selected_all ()).
 Fail assert (Horder : a < b) by assumption.
 exact I.
Qed.
Lemma transport_preserves_unused_evar (a b : Z)
 (Hselected : Z.ltb a b = true) : True.
Proof.
 let witness := open_constr:(_ : bv 64) in
 let bare := eval hnf in witness in
 is_evar bare;
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_collect constr:(a) constr:(a) constr:(a));
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_reflect_selected_all ());
 is_evar bare; unify bare (Z_to_bv 64 0).
 exact I.
Qed.
Lemma selected_nested_endpoint_no_wrap (endpoint count : bv 64) (base len : Z)
 (Hbase : 0 <= base) (Hlen : 0 <= len) (Hspace : base + len < 2^64)
 (Hcount : bv_unsigned count < len)
 (Hendpoint : endpoint = (Z_to_bv 64 base + (count + 1))%bv) : True.
Proof.
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_collect constr:(bv_unsigned count) constr:(base) constr:(count)).
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_isolate ()).
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_unsigned_selected_all ()).
 ZesuSsz.Automation2.RangeFacts.zesu_selected_casts.
 ZesuSsz.Automation2.RangeFacts.zesu_range_selected_no_wrap.
 assert (Harithmetic : bv_unsigned endpoint = base + (bv_unsigned count + 1)) by assumption.
 exact I.
Qed.
Lemma selected_nested_endpoint_keeps_wrap (endpoint count : bv 64) (base : Z)
 (Hbase : 0 <= base < 2^64) (Hwrapped : 2^64 <= bv_unsigned count + 1)
 (Hendpoint : endpoint = (Z_to_bv 64 base + (count + 1))%bv) : True.
Proof.
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_collect constr:(bv_unsigned count) constr:(base) constr:(count)).
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_isolate ()).
 ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_unsigned_selected_all ()).
 ZesuSsz.Automation2.RangeFacts.zesu_selected_casts.
 ZesuSsz.Automation2.RangeFacts.zesu_range_selected_no_wrap.
 assert (Hmodular : bv_unsigned endpoint = bv_wrap 64 (base + bv_wrap 64 (bv_unsigned count + 1))) by assumption.
 Fail assert (Harithmetic : bv_unsigned endpoint = base + (bv_unsigned count + 1)) by assumption.
 exact I.
Qed.
