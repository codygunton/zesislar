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

(* A word read from a byte window, `little_endian_to_bv n (take k bytes)`, is below
   2^(k*n) whatever the bytes are. The library solver has no fact about
   `little_endian_to_bv`, so it searched the whole context and failed (~4.5 s in
   032c), the rewrite of `bv_unsigned (Z_to_bv 64 word)` did not fire, and the
   same side condition came back at every later binder of the entry. *)
Lemma zesu_little_endian_take_in_range (n m : N) (k : nat) (bytes : list (bv n)) :
  (Z.of_nat k * Z.of_N n <= Z.of_N m)%Z ->
  (0 <= little_endian_to_bv n (take k bytes) < bv_modulus m)%Z.
Proof.
  intros Hk. pose proof (little_endian_to_bv_bound n (take k bytes)) as [Hlow Hhigh].
  split; [exact Hlow|]. unfold bv_modulus.
  eapply Z.lt_le_trans; [exact Hhigh|]. apply Z.pow_le_mono_r; [lia|].
  assert (Hlength : (length (take k bytes) <= k)%nat) by (rewrite length_take; lia).
  apply Nat2Z.inj_le in Hlength. pose proof (N2Z.is_nonneg n). nia.
Qed.

Ltac zesu_little_endian_take_bound :=
  lazymatch goal with
  | |- (0 <= little_endian_to_bv ?n (take ?k ?bytes) < bv_modulus ?m)%Z =>
      apply (zesu_little_endian_take_in_range n m k bytes); a3n_closed_bound
  end.
Ltac a3n_closed_bound_if_enabled :=
  ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled constr:(ZesuStepRewriteBoundGuards);
  solve [first [a3n_closed_bound | zesu_little_endian_take_bound]].
(* The ordinary consumer adds this branch before its existing bv_solve call. *)
