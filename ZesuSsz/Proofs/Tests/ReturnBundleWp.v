Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanClosedCall.
Require Import ZesuSsz.Automation.Sets.v2.
Require Import ZesuSsz.Automation.Switches.ReturnBundle.

Section tests.
Context `{!islaG Sigma} `{!threadG}.
Lemma return_bundle_wp_double (value sp ret : bv 64) (tail : spec) (t : isla_trace) :
  ⊢ ((reg_col zesu_ram_sys_regs -∗ spec_trace tail -∗ "PC" ↦ᵣ RVal_Bits ret -∗ WPasm t) -∗
    ((encoderBooleanClosedReturn value sp ret tail -∗ "PC" ↦ᵣ RVal_Bits ret -∗ WPasm t) ∗ True))%I.
Proof.
  iIntros "Hcontinue".
  time "T6 WP dispatch" zesu_rule_set_v2_steps.
  iMatchHyp ltac:(fun H body => lazymatch body with reg_col zesu_ram_sys_regs => iRename H into "Hsys" end).
  iMatchHyp ltac:(fun H body => lazymatch body with spec_trace _ => iRename H into "Htrace" end).
  iIntros "HPC".
  iApply ("Hcontinue" with "Hsys Htrace HPC").
Qed.
Lemma return_bundle_wp_single (value sp ret : bv 64) (tail : spec) (t : isla_trace) :
  ⊢ ((reg_col zesu_ram_sys_regs -∗ spec_trace tail -∗ WPasm t) -∗
    ((encoderBooleanClosedReturn value sp ret tail -∗ WPasm t) ∗ True))%I.
Proof.
  iIntros "Hcontinue".
  time "T6 WP dispatch" zesu_rule_set_v2_steps.
  iMatchHyp ltac:(fun H body => lazymatch body with reg_col zesu_ram_sys_regs => iRename H into "Hsys" end).
  iMatchHyp ltac:(fun H body => lazymatch body with spec_trace _ => iRename H into "Htrace" end).
  iApply ("Hcontinue" with "Hsys Htrace").
Qed.
Lemma return_bundle_wp_double_pure (relation : Prop)
    (value sp ret : bv 64) (tail : spec) (t : isla_trace) :
  ⊢ ((⌜relation⌝ -∗ reg_col zesu_ram_sys_regs -∗
      "x2" ↦ᵣ RVal_Bits sp -∗ (bv_unsigned sp - 8) ↦ₘ ret -∗
      bv_unsigned (sp - BV 64 9)%bv ↦ₘ∗ WriteSuccessExactBooleanSpec.writeSuccessBooleanWordPayload value -∗
      spec_trace tail -∗ "PC" ↦ᵣ RVal_Bits ret -∗ WPasm t) -∗
    (((⌜relation⌝ ∗ encoderBooleanClosedReturn value sp ret tail) -∗ "PC" ↦ᵣ RVal_Bits ret -∗ WPasm t) ∗ True))%I.
Proof.
  iIntros "Hcontinue".
  time "T6 WP pure dispatch double" zesu_rule_set_v2_steps.
  match goal with Hrelation : relation |- _ => idtac end.
  iMatchHyp ltac:(fun H body => lazymatch body with reg_col zesu_ram_sys_regs => iRename H into "Hsys" end).
  iMatchHyp ltac:(fun H body => lazymatch body with spec_trace _ => iRename H into "Htrace" end).
  iIntros "HPC".
  iApply ("Hcontinue" with "[] Hsys [$] [$] [$] Htrace HPC"). iPureIntro. assumption.
Qed.
Lemma return_bundle_wp_single_pure (relation : Prop)
    (value sp ret : bv 64) (tail : spec) (t : isla_trace) :
  ⊢ ((⌜relation⌝ -∗ reg_col zesu_ram_sys_regs -∗
      "x2" ↦ᵣ RVal_Bits sp -∗ (bv_unsigned sp - 8) ↦ₘ ret -∗
      bv_unsigned (sp - BV 64 9)%bv ↦ₘ∗ WriteSuccessExactBooleanSpec.writeSuccessBooleanWordPayload value -∗
      spec_trace tail -∗ WPasm t) -∗
    (((⌜relation⌝ ∗ encoderBooleanClosedReturn value sp ret tail) -∗ WPasm t) ∗ True))%I.
Proof.
  iIntros "Hcontinue".
  time "T6 WP pure dispatch single" zesu_rule_set_v2_steps.
  match goal with Hrelation : relation |- _ => idtac end.
  iMatchHyp ltac:(fun H body => lazymatch body with reg_col zesu_ram_sys_regs => iRename H into "Hsys" end).
  iMatchHyp ltac:(fun H body => lazymatch body with spec_trace _ => iRename H into "Htrace" end).
  iApply ("Hcontinue" with "[] Hsys [$] [$] [$] Htrace"). iPureIntro. assumption.
Qed.
End tests.
Print Assumptions return_bundle_wp_double.
Print Assumptions return_bundle_wp_single.

Print Assumptions return_bundle_wp_double_pure.
Print Assumptions return_bundle_wp_single_pure.
