Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.Switches.BranchGuards.
Require Import ZesuSsz.Compliance.DecodeItemNormalizedGuardRegistrations.
Require Import ZesuSsz.Generated.DecodeItem.BootstrapRegistrations.
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
  zesu_saturate_derived_facts. lia.
Qed.
End Off.
Require Import ZesuSsz.Generated.DecodeItem.Registrations.

Module On.
Lemma shortStringNegatedGuardOn args (x13 : bv 64) :
  ~ bv_signed (bv_zero_extend 128 (bv_and x13 127)) >=
      bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  bv_unsigned (bv_and x13 127) <
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)).
Proof. intros H9. zesu_saturate_derived_facts. apply Znot_ge_lt; assumption. Qed.

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
