Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SpecTable.
Require Import ZesuSsz.Automation.CallReturnSpec.
Require Import ZesuSsz.Automation.Switches.CallReturnSpec.
Require Import ZesuSsz.Automation.V2Steps.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderBytes.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanClosedCall.
Require Import isla.riscv64.riscv64.

Lemma test_bytes_return_table_entry `{!islaG Sigma} `{!threadG} :
  ZesuSpecAt 88304 (zesu_ld_spec 88304 "x10" "x2" 936).
Proof. typeclasses eauto. Qed.
Print Assumptions test_bytes_return_table_entry.

Lemma test_boolean_return_table_entry `{!islaG Sigma} `{!threadG} :
  ZesuSpecAt 88480 (zesu_ld_spec 88480 "x8" "x2" 96).
Proof. typeclasses eauto. Qed.
Print Assumptions test_boolean_return_table_entry.

Lemma test_bytes_return_step `{!islaG Sigma} `{!threadG}
    (data size sp bytes_old_x6 old_s0 old_s1 stack2 : bv 64)
    (bytes : list (bv 8)) (tail : spec) :
  (encoderBytesExactReturn data size sp (Z_to_bv 64 (88300 + 4))
     bytes bytes_old_x6 old_s0 old_s1 stack2 tail -∗
   zesu_ld_spec 88304 "x10" "x2" 936) -∗
  (encoderBytesExactReturn data size sp (Z_to_bv 64 (88300 + 4))
     bytes bytes_old_x6 old_s0 old_s1 stack2 tail -∗
   zesu_ld_spec 88304 "x10" "x2" 936) ∗ True.
Proof.
  iIntros "Hcontinue".
  zesu_rule_set_v2_steps.
  iApply ("Hcontinue" with "[$]").
Qed.
Print Assumptions test_bytes_return_step.

Lemma test_boolean_return_step `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (tail : spec) :
  (encoderBooleanClosedReturn 0 sp (Z_to_bv 64 (88476 + 4)) tail -∗
   zesu_ld_spec 88480 "x8" "x2" 96) -∗
  (encoderBooleanClosedReturn 0 sp (Z_to_bv 64 (88476 + 4)) tail -∗
   zesu_ld_spec 88480 "x8" "x2" 96) ∗ True.
Proof.
  iIntros "Hcontinue".
  zesu_rule_set_v2_steps.
  iApply ("Hcontinue" with "[$]").
Qed.
Print Assumptions test_boolean_return_step.
