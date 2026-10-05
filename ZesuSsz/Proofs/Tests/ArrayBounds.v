Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Lemma array_bounds_opt_in : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepArrayBounds) in idtac.
  exact I.
Qed.

Lemma array_bounds_disabled (p : Z) (storage : list byte)
    (Hlength : length storage = 40%nat) :
  SHELVED_SIDECOND (Z.to_nat (p + 32 - p) + N.to_nat 2 <= length storage)%nat.
Proof.
  Fail zesu_array_bounds_if_enabled.
  unshelve_sidecond.
  replace (p + 32 - p) with 32 by lia.
  cbn. lia.
Qed.

Require Import ZesuSsz.Automation.Switches.ArrayBounds.

Lemma array_bounds_lower (p k : Z) (Hk : 0 <= k) :
  SHELVED_SIDECOND (0 <= p + k - p).
Proof.
  zesu_array_bounds_if_enabled.
Qed.

Lemma array_bounds_extent (p k : Z) (width count : nat)
    (storage : list byte) (Hlength : length storage = count)
    (Hbound : (Z.to_nat k + width <= count)%nat) :
  SHELVED_SIDECOND (Z.to_nat (p + k - p) + width <= length storage)%nat.
Proof.
  zesu_array_bounds_if_enabled.
Qed.

Lemma array_bounds_updated (p : Z) (storage : list byte)
    (v0 v1 : byte) (Hlength : length storage = 40%nat) :
  SHELVED_SIDECOND
    (Z.to_nat (p + 0 - p) + N.to_nat 8 <=
     length (take (Z.to_nat (p + 32 - p)) storage ++
       v0 :: v1 :: drop (Z.to_nat (p + 32 - p) + N.to_nat 2) storage))%nat.
Proof.
  zesu_array_bounds_if_enabled.
Qed.

Definition array_bounds_folded_length (storage : list byte) :=
  (length storage = 40%nat /\ True).

Lemma array_bounds_folded (p : Z) (storage : list byte)
    (Howned : array_bounds_folded_length storage) :
  SHELVED_SIDECOND (Z.to_nat (p + 32 - p) + N.to_nat 2 <= length storage)%nat.
Proof.
  zesu_array_bounds_if_enabled.
Qed.

Lemma array_bounds_finisher (p : Z) (storage : list byte)
    (Howned : array_bounds_folded_length storage) :
  SHELVED_SIDECOND (Z.to_nat (p + 32 - p) + N.to_nat 2 <= length storage)%nat.
Proof.
  zesu_finish.
Qed.

Lemma array_bounds_preserve_other_shelf : SHELVED_SIDECOND (True = True).
Proof.
  Fail zesu_array_bounds_if_enabled.
  reflexivity.
Qed.

Lemma array_bounds_reject_false (storage : list byte)
    (Hlength : length storage = 0%nat) : True.
Proof.
  assert (Hunchanged : True) by exact I.
  Fail assert (Hbad : SHELVED_SIDECOND (1 <= length storage)%nat)
    by zesu_array_bounds_if_enabled.
  exact Hunchanged.
Qed.

Print Assumptions array_bounds_updated.
