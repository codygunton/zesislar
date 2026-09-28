Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayLoadPreselect.
Require Import ZesuSsz.Automation.Switches.ArrayLoadPriority.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Section array_load_preselect_tests.
Context `{!islaG Sigma} `{!threadG}.
Lemma preselect_active (sp : bv 64) (values : list (bv 64))
 (Hlen : length values = 17%nat) :
 instr_lookup_resources Index.lookup -∗
 instr_body_lookup_resources Index.body_lookup -∗
 instr_pre 0x156e8 ("x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ values) -∗
 instr_pre 0x156e8 ("x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ values).
Proof.
 iIntros "#Hcode #Htable Hpre".
 assert_succeeds zesu_array_load_preselect.
 iExact "Hpre".
Qed.
Lemma preselect_framed (sp : bv 64) (values : list (bv 64))
 (Hlen : length values = 17%nat) :
 instr_lookup_resources Index.lookup -∗
 instr_body_lookup_resources Index.body_lookup -∗
 instr_pre 0x156e8 ("x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ values) -∗
 instr_pre 0x156e8 ("x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ values) ∗ True.
Proof.
 iIntros "#Hcode #Htable Hpre".
 time assert_succeeds zesu_array_load_preselect.
 iFrame "Hpre".
Qed.
Lemma preselect_word_handoff (sp word : bv 64) :
 instr_lookup_resources Index.lookup -∗
 instr_body_lookup_resources Index.body_lookup -∗
 instr_pre 0x156e8 ("x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 1136) ↦ₘ word) -∗
 instr_pre 0x156e8 ("x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 1136) ↦ₘ word).
Proof.
 iIntros "#Hcode #Htable Hpre".
 assert_succeeds zesu_array_load_preselect.
 iExact "Hpre".
Qed.
(* This control removes the handoff only inside the failed trial. *)
Lemma preselect_word_without_handoff_rejects_raw (sp word : bv 64) :
 instr_lookup_resources Index.lookup -∗
 instr_body_lookup_resources Index.body_lookup -∗
 instr_pre 0x156e8 ("x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 1136) ↦ₘ word) -∗
 instr_pre 0x156e8 ("x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 1136) ↦ₘ word).
Proof.
 iIntros "#Hcode #Htable Hpre".
 Fail (iClear "Hpre"; zesu_array_load_preselect).
 iExact "Hpre".
Qed.
Local Remove Hints zesu_switch_array_load_priority : typeclass_instances.
Lemma preselect_inactive (sp : bv 64) (values : list (bv 64))
 (Hlen : length values = 17%nat) :
 instr_lookup_resources Index.lookup -∗
 instr_body_lookup_resources Index.body_lookup -∗
 instr_pre 0x156e8 ("x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ values) -∗
 instr_pre 0x156e8 ("x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ values).
Proof.
 iIntros "#Hcode #Htable Hpre".
 Fail zesu_array_load_preselect.
 iExact "Hpre".
Qed.
End array_load_preselect_tests.
Print Assumptions preselect_active.
Print Assumptions preselect_framed.
Print Assumptions preselect_word_handoff.
Print Assumptions preselect_word_without_handoff_rejects_raw.
Print Assumptions preselect_inactive.
