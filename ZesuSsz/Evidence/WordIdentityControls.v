(* Positive and refusal controls for switched word identities. *)
Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.WordIdentity.
From Coq Require Import Lists.List ZArith.ZArith.
Import ListNotations.
Require Import ZesuSsz.Automation.All.
Local Open Scope Z_scope.

Definition control_displacement : Z := 5.

Lemma word_identity_disabled : (0%bv : bv 64) = Z_to_bv 64 0.
Proof.
  assert (Hdisabled : ZesuSsz.Automation.SwitchDispatch.ZesuSwitchDispatchCache
    [(ZesuStepWordIdentity, false)]) by constructor.
  Fail zesu_word_identity.
  apply bv_eq. reflexivity.
Qed.

Lemma word_identity_zero_fold (digits : list Z) :
  (0%bv : bv 64) =
    Z_to_bv 64 (fold_left Z.add (firstn (Z.to_nat 0) digits) 0).
Proof.
  assert (enabled : ZesuStepWordIdentity) by constructor.
  zesu_word_identity.
Qed.

Lemma word_identity_closed_cast (base : Z) :
  bv_add (Z_to_bv 64 base) (Z_to_bv 64 (-control_displacement)) =
    Z_to_bv 64 (base - control_displacement).
Proof.
  assert (enabled : ZesuStepWordIdentity) by constructor.
  zesu_word_identity.
Qed.



Lemma word_identity_symbolic_width (width : N) :
  (Z_to_bv width 0) = Z_to_bv width 0.
Proof.
  assert (enabled : ZesuStepWordIdentity) by constructor.
  Fail zesu_word_identity.
  reflexivity.
Qed.


Lemma word_identity_wrong_shape : True.
Proof.
  assert (enabled : ZesuStepWordIdentity) by constructor.
  Fail zesu_word_identity.
  exact I.
Qed.
