Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.v1.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.EntryPreparation.
Require Import ZesuSsz.Automation.RegisterTupleWitness.
Require Import ZesuSsz.Automation.SharedSuffixWitness.
Require Import ZesuSsz.Automation.GuardedMemorySelection.
Require Import ZesuSsz.Automation.Switches.TracePrefixTail.
Require Import ZesuSsz.Automation.Switches.SealedOpen.
Ltac assert_call_rule_unchanged rule :=
 let before := match goal with |- ?G => constr:(G) end in
 tryif rule then fail "Accepted disabled call rule" else idtac;
 let after := match goal with |- ?G => constr:(G) end in
 constr_eq before after.
Section Tests.
Context `{!islaG Sigma} `{!threadG}.
Lemma entry_disabled (t : isla_trace) :
 ⌜True⌝ -∗ (⌜True⌝ -∗ WPasm t) -∗ WPasm t.
Proof.
 iIntros "Hfact Hnext". assert_call_rule_unchanged ltac:(zesu_prepare_entry_facts).
 iApply ("Hnext" with "Hfact").
Qed.
Lemma register_disabled (r : bv 64) :
 "x1" ↦ᵣ RVal_Bits r -∗ ∃ x : bv 64 *ₗ (), "x1" ↦ᵣ RVal_Bits x.1ₗ.
Proof.
 iIntros "Hr". assert_call_rule_unchanged ltac:(zesu_register_tuple_witness).
 iExists (r, tt)ₗ. iExact "Hr".
Qed.
Lemma suffix_disabled (row : list (bv 8)) (rest : list (list (bv 8))) :
 ⊢ ∃ y : li_prod (list (bv 8)) (li_prod (list (list (bv 8))) unit),
 (⌜row :: rest = y.2ₗ ++ y.1ₗ :: rest⌝ : iProp Sigma).
Proof.
 iStartProof. assert_call_rule_unchanged ltac:(zesu_select_shared_suffix_tuple).
 iExists (row, [], tt)ₗ. done.
Qed.
Lemma uninit_disabled (base : Z) :
 base ↦ₘ? 1896 -∗ find_in_context (FindMemMapsTo (base+312))
 (fun mk => (⌜mk = MKUninit base 1896⌝)%I).
Proof.
 iIntros "Hregion". assert_call_rule_unchanged ltac:(zesu_guarded_uninit_key).
 zesu_block.
Qed.
End Tests.
Print Assumptions entry_disabled.
Print Assumptions register_disabled.
Print Assumptions suffix_disabled.
Print Assumptions uninit_disabled.
