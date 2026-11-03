Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.LoopResourceBackedge.
Require Import ZesuSsz.Automation.SwitchDispatch.
Require Import ZesuSsz.Automation.ByteWindowFold.
From Coq Require Import Lists.List ZArith.ZArith.
Import ListNotations.
Require Import ZesuSsz.Automation.All.
Open Scope Z_scope.

Section Controls.
Context `{!islaG Sigma} `{!threadG}.
Variables (origin index : Z) (cursor endpoint accumulator next_accumulator : bv 64).
Variables (bytes : list (bv 8)) (start : nat).
Variables (P Q : bv 64 -> iProp Sigma) (frame other_frame : iProp Sigma).
Context (Hindex : 0 <= index).
Context (Horigin : bv_unsigned cursor = origin + index).
Context (Hhead : bv_unsigned cursor < bv_unsigned endpoint).
Context (Hbranch : negb (bool_decide (bv_add cursor (BV 64 1) = endpoint)) = true).
Context (Hfold : bv_unsigned accumulator =
  ByteWindowFold.zesu_byte_window_fold bytes start (Z.to_nat index)).
Context (Hnext_fold : bv_unsigned next_accumulator =
  ByteWindowFold.zesu_byte_window_fold bytes start (Z.to_nat (index + 1))).

Definition loop_resource_source : iProp Sigma :=
  (P next_accumulator ∗ Q (bv_add cursor (BV 64 1)) ∗ frame)%I.
Definition loop_resource_target (retained : iProp Sigma) : iProp Sigma :=
  (∃ (value next_cursor : bv 64) (next_index : Z),
    P value ∗ Q next_cursor ∗ retained ∗
    ⌜(bv_unsigned value = ByteWindowFold.zesu_byte_window_fold
      bytes start (Z.to_nat next_index))%Z⌝ ∗
    ⌜(bv_unsigned next_cursor = origin + next_index)%Z⌝ ∗
    ⌜(0 <= next_index)%Z⌝ ∗ ⌜(bv_unsigned next_cursor < bv_unsigned endpoint)%Z⌝)%I.

Lemma loop_resource_positive : loop_resource_source -∗ loop_resource_target frame.
Proof using All.
  assert (enabled : ZesuStepLoopResourceBackedge) by constructor.
  unfold loop_resource_source, loop_resource_target.
  iIntros "[HP [HQ Hframe]]".
  zesu_loop_resource_backedge
    constr:((next_accumulator, (bv_add cursor (BV 64 1), tt)))
    constr:(next_accumulator) ltac:(exact Hnext_fold).
(* POSITIVE_COMPLETE_EXPORT *)
Qed.

Lemma loop_resource_disabled_refuses : True.
Proof using All.
  assert (off : ZesuSwitchDispatchCache [(ZesuStepLoopResourceBackedge, false)])
    by constructor.
  Fail assert (test : loop_resource_source -∗ loop_resource_target frame) by
    (unfold loop_resource_source, loop_resource_target;
     iIntros "[HP [HQ Hframe]]";
     zesu_loop_resource_backedge
       constr:((next_accumulator, (bv_add cursor (BV 64 1), tt)))
       constr:(next_accumulator) ltac:(fail 100 "CALLBACK_RAN")).
  exact I.
Qed.

Lemma loop_resource_missing_refuses : True.
Proof using All.
  assert (enabled : ZesuStepLoopResourceBackedge) by constructor.
  Fail assert (test : loop_resource_source -∗ loop_resource_target frame) by
    (unfold loop_resource_source, loop_resource_target;
     iIntros "[HP [HQ Hframe]]";
     zesu_loop_resource_backedge constr:(tt) constr:(next_accumulator)
       ltac:(exact Hnext_fold)).
  exact I.
Qed.

Lemma loop_resource_extra_refuses : True.
Proof using All.
  assert (enabled : ZesuStepLoopResourceBackedge) by constructor.
  Fail assert (test : loop_resource_source -∗ loop_resource_target frame) by
    (unfold loop_resource_source, loop_resource_target;
     iIntros "[HP [HQ Hframe]]";
     zesu_loop_resource_backedge
       constr:((next_accumulator, (bv_add cursor (BV 64 1), (cursor, tt))))
       constr:(next_accumulator) ltac:(exact Hnext_fold)).
  exact I.
Qed.

Lemma loop_resource_wrong_type_refuses : True.
Proof using All.
  assert (enabled : ZesuStepLoopResourceBackedge) by constructor.
  Fail assert (test : loop_resource_source -∗ loop_resource_target frame) by
    (unfold loop_resource_source, loop_resource_target;
     iIntros "[HP [HQ Hframe]]";
     zesu_loop_resource_backedge constr:((true, (cursor, tt)))
       constr:(next_accumulator) ltac:(exact Hnext_fold)).
  exact I.
Qed.

Lemma loop_resource_swapped_refuses : True.
Proof using All.
  assert (enabled : ZesuStepLoopResourceBackedge) by constructor.
  Fail assert (test : loop_resource_source -∗ loop_resource_target frame) by
    (unfold loop_resource_source, loop_resource_target;
     iIntros "[HP [HQ Hframe]]";
     zesu_loop_resource_backedge
       constr:((bv_add cursor (BV 64 1), (next_accumulator, tt)))
       constr:(next_accumulator) ltac:(exact Hnext_fold)).
  exact I.
Qed.

Lemma loop_resource_changed_frame_refuses : True.
Proof using All.
  assert (enabled : ZesuStepLoopResourceBackedge) by constructor.
  Fail assert (test : loop_resource_source -∗ loop_resource_target other_frame) by
    (unfold loop_resource_source, loop_resource_target;
     iIntros "[HP [HQ Hframe]]";
     zesu_loop_resource_backedge
       constr:((next_accumulator, (bv_add cursor (BV 64 1), tt)))
       constr:(next_accumulator) ltac:(exact Hnext_fold)).
  exact I.
Qed.

Lemma loop_resource_wrong_shape_refuses : True.
Proof using All.
  assert (enabled : ZesuStepLoopResourceBackedge) by constructor.
  Fail zesu_loop_resource_backedge constr:(tt) constr:(next_accumulator)
    ltac:(fail 100 "CALLBACK_RAN").
  exact I.
Qed.
End Controls.

Section SymbolicWidth.
Context `{!islaG Sigma} `{!threadG}.
Context (width : N).
Variables (origin index : Z) (cursor endpoint : bv width).
Variables (accumulator next_accumulator : bv 64) (bytes : list (bv 8)) (start : nat).
Variables (P : bv 64 -> iProp Sigma) (Q : bv width -> iProp Sigma).
Context (Hindex : 0 <= index).
Context (Horigin : bv_unsigned cursor = origin + index).
Context (Hhead : bv_unsigned cursor < bv_unsigned endpoint).
Context (Hbranch : negb (bool_decide
  (bv_add cursor (Z_to_bv width 1) = endpoint)) = true).
Context (Hfold : bv_unsigned accumulator =
  ByteWindowFold.zesu_byte_window_fold bytes start (Z.to_nat index)).

Lemma loop_resource_symbolic_width_refuses : True.
Proof using All.
  assert (enabled : ZesuStepLoopResourceBackedge) by constructor.
  Fail assert (test : (
      (P next_accumulator ∗ Q (bv_add cursor (Z_to_bv width 1))) -∗
      ∃ (value : bv 64) (next_cursor : bv width) (next_index : Z),
        P value ∗ Q next_cursor ∗ ⌜(0 <= next_index)%Z⌝)%I) by
    (iIntros "[HP HQ]";
     zesu_loop_resource_backedge
       constr:((next_accumulator, (bv_add cursor (Z_to_bv width 1), tt)))
       constr:(next_accumulator) ltac:(fail 100 "CALLBACK_RAN")).
  exact I.
Qed.
End SymbolicWidth.

Print Assumptions loop_resource_positive.
Print Assumptions loop_resource_disabled_refuses.
Print Assumptions loop_resource_missing_refuses.
Print Assumptions loop_resource_extra_refuses.
Print Assumptions loop_resource_wrong_type_refuses.
Print Assumptions loop_resource_swapped_refuses.
Print Assumptions loop_resource_changed_frame_refuses.
Print Assumptions loop_resource_wrong_shape_refuses.
Print Assumptions loop_resource_symbolic_width_refuses.
