Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.RegisterTupleWitness.
Section Tests.
Context `{!islaG Sigma} `{!threadG}.
Lemma owned_tuple (r : bv 64) (sp : bv 64) (mask : bv 64) (v : valu) :
 valu_has_shape v (BitsShape 64) ->
 "x1" ↦ᵣ RVal_Bits r -∗ "x2" ↦ᵣ RVal_Bits sp -∗
 "x13" ↦ᵣ v -∗
 ∃ x : bv 64 *ₗ bv 64 *ₗ bv 64 *ₗ (),
 ⌜v = RVal_Bits x.1ₗ⌝ ∗ "x13" ↦ᵣ v ∗
 "x1" ↦ᵣ RVal_Bits x.2ₗ ∗ "x2" ↦ᵣ RVal_Bits x.3ₗ.
Proof using All. zesu_block. Qed.
Lemma missing_register_rejects (mask : bv 64) :
 True -∗ ∃ x : bv 64 *ₗ (), ("x1" ↦ᵣ RVal_Bits x.1ₗ ∨ True)%I.
Proof using All.
 iIntros "H". Fail zesu_register_tuple_witness.
 iExists (BV 64 0, tt)ₗ. iRight. done.
Qed.
Lemma unrelated_register_rejects (mask : bv 64) :
 "x2" ↦ᵣ RVal_Bits mask -∗ ∃ x : bv 64 *ₗ (), ("x1" ↦ᵣ RVal_Bits x.1ₗ ∨ True)%I.
Proof using All.
 iIntros "H". Fail zesu_register_tuple_witness.
 iExists (BV 64 0, tt)ₗ. iRight. done.
Qed.
Lemma spatial_shape_tuple (mask : bv 64) (v : valu) :
 ⌜valu_has_shape v (BitsShape 64)⌝ -∗ "x13" ↦ᵣ v -∗
 ∃ x : bv 64 *ₗ (), ⌜v = RVal_Bits x.1ₗ⌝ ∗ "x13" ↦ᵣ v.
Proof using All.
 iIntros "Hshape H13". zesu_register_tuple_witness.
 iSplit; first (iPureIntro; assumption). iFrame.
Qed.
Lemma orphan_finish_rejects (mask expected : bv 64) : True.
Proof using All.
 assert (chosen : bv 64).
 { Fail zesu_finish. exact expected. }
 exact I.
Qed.
End Tests.
