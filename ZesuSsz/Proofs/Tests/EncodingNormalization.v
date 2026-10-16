Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.SwitchDispatch.
Require Import ZesuSsz.Automation.Switches.EncodingNormalization.
Set Default Proof Mode "Classic".
Open Scope Z_scope.

Lemma encoding_wide_compare (left right : bv 64)
    (Hcompare : bv_signed (bv_zero_extend 128 left) <
                bv_signed (bv_zero_extend 128 right)) :
    bv_unsigned left < bv_unsigned right.
Proof. zesu_encoding_normalization_if_enabled. exact Hcompare. Qed.

Lemma encoding_other_width (left right : bv 8)
    (Hcompare : bv_signed (bv_zero_extend 16 left) <=
                bv_signed (bv_zero_extend 16 right)) :
    bv_unsigned left <= bv_unsigned right.
Proof. zesu_encoding_normalization_if_enabled. exact Hcompare. Qed.

Lemma encoding_bounded_cast (value : Z) (Hbound : 0 <= value <= 2048)
    (Hcast : bv_unsigned (Z_to_bv 64 value) > 64) : 65 <= value.
Proof. zesu_encoding_normalization_if_enabled. lia. Qed.

Lemma encoding_cast_goal (value : Z) (Hbound : 0 <= value <= 2048) :
    bv_unsigned (Z_to_bv 64 value) = value.
Proof. zesu_encoding_normalization_if_enabled. reflexivity. Qed.

Lemma encoding_literal_xor :
    bv_xor (Z_to_bv 64 7) (Z_to_bv 64 3) = Z_to_bv 64 4.
Proof. zesu_encoding_normalization_if_enabled. apply bv_eq. reflexivity. Qed.

Lemma encoding_literal_sub :
    bv_sub (Z_to_bv 64 3) (Z_to_bv 64 5) = Z_to_bv 64 (-2).
Proof. zesu_encoding_normalization_if_enabled. apply bv_eq. reflexivity. Qed.

Lemma encoding_literal_ite_true (value : Z) :
    ite (bool_decide (3 < 5)) value 0 = value.
Proof. zesu_encoding_normalization_if_enabled. reflexivity. Qed.

Lemma encoding_literal_ite_false (value : Z) :
    ite (bool_decide (5 <= 3)) 0 value = value.
Proof. zesu_encoding_normalization_if_enabled. reflexivity. Qed.

Lemma encoding_literal_equality : bool_decide (3 = 3) = true.
Proof. zesu_encoding_normalization_if_enabled. reflexivity. Qed.

Lemma encoding_mixed (left right : bv 64) (value : Z)
    (Hbound : 0 <= value <= 2048)
    (Hcompare : bv_signed (bv_zero_extend 128 left) <
                bv_signed (bv_zero_extend 128 right))
    (Hleft : bv_unsigned left = 64)
    (Hright : bv_unsigned right = bv_unsigned (Z_to_bv 64 value)) :
    65 <= value.
Proof. zesu_encoding_normalization_if_enabled. lia. Qed.

Lemma encoding_finish_dispatch (left right : bv 64)
    (Hcompare : bv_signed (bv_zero_extend 128 left) <
                bv_signed (bv_zero_extend 128 right)) :
    bv_unsigned left < bv_unsigned right.
Proof. zesu_finish. Qed.

Lemma encoding_missing_bound (value : Z) : value = value.
Proof.
  assert_fails (idtac; zesu_encoding_cast_term
    constr:(bv_unsigned (Z_to_bv 64 value)) constr:(tt)).
  reflexivity.
Qed.

Lemma encoding_symbolic_compute (value : bv 64) : value = value.
Proof.
  assert_fails (idtac; zesu_encoding_compute
    constr:(bv_xor value (Z_to_bv 64 1)) constr:(tt)).
  assert_fails (idtac; zesu_encoding_compute
    constr:(bv_sub value (Z_to_bv 64 1)) constr:(tt)).
  reflexivity.
Qed.

Lemma encoding_symbolic_comparison (value : Z) : value = value.
Proof.
  assert_fails (idtac; zesu_encoding_compute constr:(bool_decide (value < 5)) constr:(tt)).
  reflexivity.
Qed.

Lemma encoding_narrow_extension (value : bv 64) : value = value.
Proof.
  assert_fails (idtac; zesu_encoding_wide_term
    constr:(bv_signed (bv_zero_extend 32 value)) constr:(tt)).
  reflexivity.
Qed.

Lemma encoding_same_width (value : bv 64) : value = value.
Proof.
  assert_fails (idtac; zesu_encoding_wide_term
    constr:(bv_signed (bv_zero_extend 64 value)) constr:(tt)).
  reflexivity.
Qed.

Lemma encoding_cached_off (value : Z) (Hbound : 0 <= value <= 2048) :
    bv_unsigned (Z_to_bv 64 value) = value.
Proof.
  assert (Hcache : ZesuSwitchDispatchCache
    [(ZesuStepEncodingNormalization, false)]) by constructor.
  assert_fails (idtac; zesu_encoding_normalization_if_enabled).
  apply zesu_bv_unsigned_Z_to_bv_small. change (0 <= value < 18446744073709551616). lia.
Qed.

Lemma encoding_rejected_evar : True.
Proof.
  evar (pending : Z).
  assert_fails (idtac; zesu_encoding_compute constr:(Z_to_bv 64 pending) constr:(tt)).
  assert_fails (idtac; zesu_encoding_cast_term
    constr:(bv_unsigned (Z_to_bv 64 pending)) constr:(tt)).
  let value := eval unfold pending in pending in unify value 0%Z.
  exact I.
Qed.

Lemma encoding_symbolic_width (width : N) : True.
Proof.
  assert_fails (idtac; zesu_encoding_width_literal width).
  exact I.
Qed.

Lemma encoding_nonliteral_operand (value : Z) : value = value.
Proof.
  assert_fails (idtac; zesu_encoding_literal_term
    constr:(bv_xor (Z_to_bv 64 value) (Z_to_bv 64 1)) constr:(tt)).
  reflexivity.
Qed.

Print Assumptions encoding_wide_compare.
Print Assumptions encoding_bounded_cast.
Print Assumptions encoding_mixed.
