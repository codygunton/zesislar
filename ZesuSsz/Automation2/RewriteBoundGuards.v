From Coq Require Import ZArith.ZArith Lia.
From stdpp Require Import list.
Require Import stdpp.bitvector.definitions.
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

(* A word read from a byte window, `little_endian_to_bv n (take k bytes)`, as the
   range side condition of a conditional rewrite: refused outright, so the
   consumer's `bv_solve` fallback does not run either (`fail 2` leaves the
   consumer's `first`). bv_solve has no fact about `little_endian_to_bv`; it
   searched the whole context and failed (~4.5 s per entry binder in 032c). Proving
   the bound instead lets the rewrite fire, and the unwrapped words then cost
   +60-96% instructions in decodeItem blocks (zify div/mod equations in later
   bound solves), so the rewrite stays unfired, as before, at no solver cost. *)
Ltac a3n_closed_bound_if_enabled :=
  ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled constr:(ZesuStepRewriteBoundGuards);
  lazymatch goal with
  | |- (0 <= little_endian_to_bv _ (take _ _) < bv_modulus _)%Z =>
      fail 2 "byte-window word bound: no solver runs"
  | |- _ => solve [a3n_closed_bound]
  end.
(* The ordinary consumer adds this branch before its existing bv_solve call. *)
