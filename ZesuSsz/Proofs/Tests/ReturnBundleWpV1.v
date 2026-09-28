Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanClosedCall.
Require Import ZesuSsz.Automation.V2Steps.

Section tests.
Context `{!islaG Sigma} `{!threadG}.
Lemma return_bundle_wp_double_inactive (value sp ret : bv 64) (tail : spec) (t : isla_trace) :
  ⊢ ((reg_col zesu_ram_sys_regs -∗ spec_trace tail -∗ "PC" ↦ᵣ RVal_Bits ret -∗ WPasm t) -∗
    ((encoderBooleanClosedReturn value sp ret tail -∗ "PC" ↦ᵣ RVal_Bits ret -∗ WPasm t) ∗ True))%I.
Proof.
  iIntros "Hcontinue".
  Fail zesu_rule_set_v2_steps.
  iSplit; last done. iIntros "Hreturn".
  iEval (unfold encoderBooleanClosedReturn) in "Hreturn".
  iDestruct "Hreturn" as "(Hsys & H1 & H2 & Hra & H5 & H10 & H11 & Hpayload & Hlow & Hmmio & Htrace & _)".
  iIntros "HPC".
  iApply ("Hcontinue" with "Hsys Htrace HPC").
Qed.
Lemma return_bundle_wp_single_inactive (value sp ret : bv 64) (tail : spec) (t : isla_trace) :
  ⊢ ((reg_col zesu_ram_sys_regs -∗ spec_trace tail -∗ WPasm t) -∗
    ((encoderBooleanClosedReturn value sp ret tail -∗ WPasm t) ∗ True))%I.
Proof.
  iIntros "Hcontinue".
  Fail zesu_rule_set_v2_steps.
  iSplit; last done. iIntros "Hreturn".
  iEval (unfold encoderBooleanClosedReturn) in "Hreturn".
  iDestruct "Hreturn" as "(Hsys & H1 & H2 & Hra & H5 & H10 & H11 & Hpayload & Hlow & Hmmio & Htrace & _)".
  iApply ("Hcontinue" with "Hsys Htrace").
Qed.
Lemma return_bundle_wp_double_pure_inactive (relation : Prop)
    (value sp ret : bv 64) (tail : spec) (t : isla_trace) :
  ⊢ ((⌜relation⌝ -∗ reg_col zesu_ram_sys_regs -∗
      "x2" ↦ᵣ RVal_Bits sp -∗ (bv_unsigned sp - 8) ↦ₘ ret -∗
      bv_unsigned (sp - BV 64 9)%bv ↦ₘ∗ WriteSuccessExactBooleanSpec.writeSuccessBooleanWordPayload value -∗
      spec_trace tail -∗ "PC" ↦ᵣ RVal_Bits ret -∗ WPasm t) -∗
    (((⌜relation⌝ ∗ encoderBooleanClosedReturn value sp ret tail) -∗ "PC" ↦ᵣ RVal_Bits ret -∗ WPasm t) ∗ True))%I.
Proof.
  iIntros "Hcontinue".
  Fail zesu_rule_set_v2_steps.
  iSplit; last done. iIntros "[Hrelation Hreturn]".
  iDestruct "Hrelation" as %Hrelation.
  iEval (unfold encoderBooleanClosedReturn) in "Hreturn".
  iDestruct "Hreturn" as "(Hsys & H1 & H2 & Hra & H5 & H10 & H11 & Hpayload & Hlow & Hmmio & Htrace & _)".
  match goal with Hrelation : relation |- _ => idtac end.
  iIntros "HPC".
  iApply ("Hcontinue" with "[] Hsys [$] [$] [$] Htrace HPC"). iPureIntro. assumption.
Qed.
Lemma return_bundle_wp_single_pure_inactive (relation : Prop)
    (value sp ret : bv 64) (tail : spec) (t : isla_trace) :
  ⊢ ((⌜relation⌝ -∗ reg_col zesu_ram_sys_regs -∗
      "x2" ↦ᵣ RVal_Bits sp -∗ (bv_unsigned sp - 8) ↦ₘ ret -∗
      bv_unsigned (sp - BV 64 9)%bv ↦ₘ∗ WriteSuccessExactBooleanSpec.writeSuccessBooleanWordPayload value -∗
      spec_trace tail -∗ WPasm t) -∗
    (((⌜relation⌝ ∗ encoderBooleanClosedReturn value sp ret tail) -∗ WPasm t) ∗ True))%I.
Proof.
  iIntros "Hcontinue".
  Fail zesu_rule_set_v2_steps.
  iSplit; last done. iIntros "[Hrelation Hreturn]".
  iDestruct "Hrelation" as %Hrelation.
  iEval (unfold encoderBooleanClosedReturn) in "Hreturn".
  iDestruct "Hreturn" as "(Hsys & H1 & H2 & Hra & H5 & H10 & H11 & Hpayload & Hlow & Hmmio & Htrace & _)".
  match goal with Hrelation : relation |- _ => idtac end.
  iApply ("Hcontinue" with "[] Hsys [$] [$] [$] Htrace"). iPureIntro. assumption.
Qed.
End tests.
Print Assumptions return_bundle_wp_double_inactive.
Print Assumptions return_bundle_wp_single_inactive.

Print Assumptions return_bundle_wp_double_pure_inactive.
Print Assumptions return_bundle_wp_single_pure_inactive.
