From Coq Require Import ZArith.ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation2.LoopCursorRanges.
Local Open Scope Z_scope.

Lemma zesu_loop_unsigned_backedge (width : N) (cursor limit : bv width) :
  bv_unsigned cursor < bv_unsigned limit ->
  bv_add cursor (Z_to_bv width 1) <> limit ->
  bv_unsigned (bv_add cursor (Z_to_bv width 1)) < bv_unsigned limit.
Proof.
  intros Hhead Hbranch.
  pose proof (zesu_loop_unsigned_step width cursor limit Hhead) as Hstep.
  assert (Hdifferent : bv_unsigned cursor + 1 <> bv_unsigned limit).
  { intros Hequal. apply Hbranch. apply bv_eq. rewrite Hstep. exact Hequal. }
  rewrite Hstep. lia.
Qed.

Lemma zesu_loop_index_backedge (width : N) (cursor limit : bv width)
    (origin index : Z) :
  0 <= index -> bv_unsigned cursor = origin + index ->
  bv_unsigned cursor < bv_unsigned limit ->
  bv_add cursor (Z_to_bv width 1) <> limit ->
  let next := bv_add cursor (Z_to_bv width 1) in
  let next_index := bv_unsigned next - origin in
  next_index = index + 1 /\
  bv_unsigned next = origin + next_index /\
  0 <= next_index /\ bv_unsigned next < bv_unsigned limit.
Proof.
  intros Hindex Horigin Hhead Hbranch. cbn zeta.
  pose proof (zesu_loop_unsigned_step width cursor limit Hhead) as Hstep.
  pose proof (zesu_loop_unsigned_backedge width cursor limit Hhead Hbranch) as Hnext.
  rewrite Hstep in Hnext |- *. repeat split; lia.
Qed.
