From Coq Require Import ZArith.ZArith Bool.Bool.
From stdpp Require Import bitvector.definitions decidable.
From iris.proofmode Require Import tactics environments.
Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.VmClosed.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Require Import ZesuSsz.Automation2.LoopCursorBackedge.
Require Import ZesuSsz.Automation2.ResourceGroups.
Local Open Scope Z_scope.

Class ZesuStepLoopResourceBackedge : Prop := zesu_step_loop_resource_backedge : True.

(* The caller supplies source-owned values in declaration order. *)
Ltac zesu_loop_pack_values values next_index :=
  lazymatch values with
  | tt => iExists next_index
  | (?value, ?tail) => iExists value; zesu_loop_pack_values tail next_index
  end.

Ltac zesu_loop_finish_pure :=
  lazymatch goal with
  | |- envs_entails _ ?body =>
      ResourceGroups.zesu_is_pure_resource body;
      solve [repeat first
        [solve [iPureIntro; assumption] |
         solve [iPureIntro; reflexivity] | iSplit]]
  end.

(* The callback proves the fold step from the caller's existing source facts. *)
Ltac zesu_loop_resource_backedge values next_accumulator derive_fold :=
  zesu_switch_enabled constr:(ZesuStepLoopResourceBackedge);
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ _ _) => idtac
  end;
  solve [multimatch goal with
  | Hfold : bv_unsigned ?accumulator = ByteWindowFold.zesu_byte_window_fold
      ?bytes ?start (Z.to_nat ?index),
    Hindex : 0 <= ?index,
    Horigin : bv_unsigned ?cursor = ?origin + ?index,
    Hhead : bv_unsigned ?cursor < bv_unsigned ?endpoint,
    Hbranch : negb (bool_decide (bv_add ?cursor ?unit = ?raw_endpoint)) = true |- _ =>
      let width := lazymatch type of cursor with bv ?width => width end in
      zesu_vm_closed width;
      zesu_vm_closed unit;
      let unit_unsigned := fresh "sourceUnitUnsigned" in
      assert (unit_unsigned : bv_unsigned unit = 1) by
        (let closed := constr:(bv_unsigned unit = 1) in
         zesu_vm_closed closed; vm_compute; reflexivity);
      let unit_view := fresh "sourceUnitView" in
      pose proof (Z_to_bv_bv_unsigned width unit) as unit_view;
      rewrite unit_unsigned in unit_view;
      let endpoint_view := fresh "sourceEndpointView" in
      assert (endpoint_view : endpoint = raw_endpoint) by
        first [reflexivity | assumption];
      let branch := fresh "sourceBranch" in
      pose proof Hbranch as branch;
      apply Bool.negb_true_iff in branch;
      apply bool_decide_eq_false_1 in branch;
      let next_branch := fresh "nextBranch" in
      assert (next_branch : bv_add cursor (Z_to_bv width 1) <> endpoint) by
        (rewrite unit_view; first [constr_eq endpoint raw_endpoint | rewrite endpoint_view]; exact branch);
      let next_fold := fresh "nextFold" in
      assert (next_fold : bv_unsigned next_accumulator =
        ByteWindowFold.zesu_byte_window_fold bytes start (Z.to_nat (index + 1)))
        by derive_fold;
      let advance := fresh "cursorAdvance" in
      pose proof (LoopCursorBackedge.zesu_loop_index_backedge width cursor endpoint
        origin index Hindex Horigin Hhead next_branch) as advance;
      cbn zeta in advance;
      rewrite unit_view in advance;
      let index_link := fresh "nextIndexLink" in
      let next_origin := fresh "nextOrigin" in
      let next_nonnegative := fresh "nextNonnegative" in
      let next_head := fresh "nextHead" in
      destruct advance as [index_link [next_origin [next_nonnegative next_head]]];
      first [constr_eq endpoint raw_endpoint | rewrite endpoint_view in next_head];
      rewrite <- index_link in next_fold;
      let next_index := constr:((bv_unsigned (bv_add cursor unit) - origin)%Z) in
      zesu_loop_pack_values values next_index;
      iFrame;
      zesu_loop_finish_pure
  end].
