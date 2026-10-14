Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemUnfoldRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Compliance.DecodeItemS40GuardFacts.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Open Scope Z_scope.

Module Off.
Local Remove Hints zesu_switch_pure_fact_hints : typeclass_instances.

Lemma shortStringNegatedGuardOff args (x13 : bv 64) :
  ~ bv_signed (bv_zero_extend 128 (bv_and x13 127)) >=
      bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  bv_unsigned (bv_and x13 127) <
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)).
Proof.
  intros H9. Fail zesu_pure_fact_hints_if_enabled.
  exact (decodeItemShortStringNegatedGuardUnsigned args x13 H9).
Qed.
End Off.

Module On.
Lemma shortStringNegatedGuardOn args (x13 : bv 64) :
  ~ bv_signed (bv_zero_extend 128 (bv_and x13 127)) >=
      bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  bv_unsigned (bv_and x13 127) <
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)).
Proof. intros H9. zesu_pure_fact_hints_if_enabled. Qed.

Lemma shortStringNegatedGuardOtherRegister args (x13 other : bv 64)
    (H9 : ~ bv_signed (bv_zero_extend 128 (bv_and x13 127)) >=
      bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args)))) :
  True.
Proof.
  Fail assert (Hother : bv_unsigned (bv_and other 127) <
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)))
    by zesu_pure_fact_hints_if_enabled.
  exact I.
Qed.
End On.

Print Assumptions Off.shortStringNegatedGuardOff.
Print Assumptions On.shortStringNegatedGuardOn.
Print Assumptions On.shortStringNegatedGuardOtherRegister.
