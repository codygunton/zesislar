Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.EntryPreparation.
Require Import ZesuSsz.Automation.RegisterTupleWitness.
Require Import ZesuSsz.Automation.SharedSuffixWitness.
Require Import ZesuSsz.Automation.GuardedMemorySelection.
Require Import ZesuSsz.Automation.Switches.TracePrefixTail.
Require Import ZesuSsz.Automation.Switches.SealedOpen.
Section Tests.
Context `{!islaG Sigma} `{!threadG}.
Lemma entry_enabled (t : isla_trace) :
 ⌜True⌝ -∗ (⌜True⌝ -∗ WPasm t) -∗ WPasm t.
Proof.
 iIntros "Hfact Hnext". zesu_prepare_entry_facts.
 iApply "Hnext". done.
Qed.
Lemma register_enabled (r : bv 64) :
 "x1" ↦ᵣ RVal_Bits r -∗ ∃ x : bv 64 *ₗ (), "x1" ↦ᵣ RVal_Bits x.1ₗ.
Proof.
 iIntros "Hr". zesu_register_tuple_witness. iExact "Hr".
Qed.
Lemma suffix_enabled (row : list (bv 8)) (rest : list (list (bv 8))) :
 ⊢ ∃ y : li_prod (list (bv 8)) (li_prod (list (list (bv 8))) unit),
 (⌜row :: rest = y.2ₗ ++ y.1ₗ :: rest⌝ : iProp Sigma).
Proof.
 iStartProof. zesu_select_shared_suffix_tuple. done.
Qed.
Lemma uninit_enabled (base : Z) :
 base ↦ₘ? 1896 -∗ find_in_context (FindMemMapsTo (base+312))
 (fun mk => (⌜mk = MKUninit base 1896⌝)%I).
Proof.
 iIntros "Hregion". zesu_guarded_uninit_key. done.
Qed.
End Tests.
Print Assumptions entry_enabled.
Print Assumptions register_enabled.
Print Assumptions suffix_enabled.
Print Assumptions uninit_enabled.
