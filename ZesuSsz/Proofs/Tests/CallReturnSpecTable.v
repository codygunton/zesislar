Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SpecTable.
Require Import ZesuSsz.Automation.Sets.v2.
Require Import ZesuSsz.Automation.Switches.CallReturnSpecTable.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderBytes.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanClosedCall.
Require Import isla.riscv64.riscv64.

Lemma test_tf1_return_table_entry `{!islaG Sigma} `{!threadG} :
  ZesuSpecAt 88304 (zesu_ld_spec 88304 "x10" "x2" 936).
Proof. typeclasses eauto. Qed.
Print Assumptions test_tf1_return_table_entry.

Lemma test_tf2_return_table_entry `{!islaG Sigma} `{!threadG} :
  ZesuSpecAt 88480 (zesu_ld_spec 88480 "x8" "x2" 96).
Proof. typeclasses eauto. Qed.
Print Assumptions test_tf2_return_table_entry.

Lemma test_tf1_call_return_into_load_spec `{!islaG Sigma} `{!threadG}
    (data size sp bytes_old_x6 old_s0 old_s1 stack2 : bv 64)
    (bytes : list (bv 8)) (tail : spec) :
  (encoderBytesExactReturn data size sp (Z_to_bv 64 (88300 + 4))
     bytes bytes_old_x6 old_s0 old_s1 stack2 tail -∗
   zesu_ld_spec 88304 "x10" "x2" 936) -∗
  ((encoderBytesExactReturn data size sp (Z_to_bv 64 (88300 + 4))
      bytes bytes_old_x6 old_s0 old_s1 stack2 tail -∗
    zesu_ld_spec 88304 "x10" "x2" 936) ∗ True).
Proof.
  iIntros "Hcontinue".
  zesu_rule_set_v2_steps.
  iApply ("Hcontinue" with "[$]").
Qed.
Print Assumptions test_tf1_call_return_into_load_spec.

Lemma test_tf2_call_return_into_load_spec `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (tail : spec) :
  (encoderBooleanClosedReturn 0 sp (Z_to_bv 64 (88476 + 4)) tail -∗
   zesu_ld_spec 88480 "x8" "x2" 96) -∗
  ((encoderBooleanClosedReturn 0 sp (Z_to_bv 64 (88476 + 4)) tail -∗
    zesu_ld_spec 88480 "x8" "x2" 96) ∗ True).
Proof.
  iIntros "Hcontinue".
  zesu_rule_set_v2_steps.
  iApply ("Hcontinue" with "[$]").
Qed.
Print Assumptions test_tf2_call_return_into_load_spec.

Lemma test_call_return_rule_rejects_existential `{!islaG Sigma} `{!threadG}
    (R : iProp Sigma) :
  (R -∗ ∃ n : nat, ⌜n = 0%nat⌝) -∗
  ((R -∗ ∃ n : nat, ⌜n = 0%nat⌝) ∗ True).
Proof.
  iIntros "Hcontinue".
  tryif zesu_rule_set_v2_steps
  then fail "the load-only return rule matched an existential"
  else idtac.
  iSplit; last done.
  iIntros "Hreturned".
  iApply "Hcontinue". iExact "Hreturned".
Qed.
Print Assumptions test_call_return_rule_rejects_existential.
