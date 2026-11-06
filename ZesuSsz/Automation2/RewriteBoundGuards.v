From Coq Require Import ZArith.ZArith.
(* Scratch closed-bound fast path. Production consumers retain bv_solve fallback. *)
Require Import ZesuSsz.Automation2.VmClosed.
Require Import ZesuSsz.Automation2.SwitchDispatch.
Class ZesuStepRewriteBoundGuards : Prop := zesu_rewrite_bound_guards_enabled : True.
Ltac a3n_closed_bound :=
  lazymatch goal with
  | |- (?left <= ?right)%Z =>
      ZesuSsz.Automation2.VmClosed.zesu_vm_closed left;
      ZesuSsz.Automation2.VmClosed.zesu_vm_closed right;
      let lhs := eval vm_compute in left in
      let rhs := eval vm_compute in right in
      change (lhs <= rhs)%Z;
      exact (proj1 (Z.leb_le lhs rhs) eq_refl)
  | |- (?left < ?right)%Z =>
      ZesuSsz.Automation2.VmClosed.zesu_vm_closed left;
      ZesuSsz.Automation2.VmClosed.zesu_vm_closed right;
      let lhs := eval vm_compute in left in
      let rhs := eval vm_compute in right in
      change (lhs < rhs)%Z;
      exact (proj1 (Z.ltb_lt lhs rhs) eq_refl)
  | |- _ /\ _ => split; a3n_closed_bound
  end.
Ltac a3n_closed_bound_if_enabled :=
  ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled constr:(ZesuStepRewriteBoundGuards);
  solve [a3n_closed_bound].
(* The ordinary consumer adds this branch before its existing bv_solve call. *)
