Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.EncodingNormalization.
Set Default Proof Mode "Classic".
Open Scope Z_scope.

Lemma encoding_switch_default_off (left right : bv 64)
    (Hcompare : bv_signed (bv_zero_extend 128 left) <
                bv_signed (bv_zero_extend 128 right)) :
    bv_unsigned left < bv_unsigned right.
Proof.
  assert_fails (idtac; zesu_encoding_normalization_if_enabled).
  rewrite !zesu_bv_signed_zero_extend_wide in Hcompare; [exact Hcompare | lia..].
Qed.
