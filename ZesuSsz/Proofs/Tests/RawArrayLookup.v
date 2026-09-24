Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SpecTable.
Require Import InstrSpecs.Lookup.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.

Lemma test_raw_lookup_preserves_array `{!islaG Sigma} `{!threadG}
    (arrayBase : Z) (bytes : list (bv 8)) :
  (instr_lookup_resources Index.lookup ∗ arrayBase ↦ₘ∗ bytes) ⊢
  arrayBase ↦ₘ∗ bytes ∗
  find_in_context (FindInstrKind 0x156e8 true)
    (fun kind => ⌜kind = IKInstr (Index.lookup 0x156e8)⌝).
Proof.
  iIntros "[#Hcode Harray]".
  iFrame "Harray".
  iApply (find_in_context_instr_lookup_resources
            0x156e8 true
            (fun kind => ⌜kind = IKInstr (Index.lookup 0x156e8)⌝)%I).
  iExists Index.lookup.
  iFrame "Hcode".
  iSplit.
  - iPureIntro. rewrite Index.lookup_a156e8. eauto.
  - iPureIntro. reflexivity.
Qed.
Print Assumptions test_raw_lookup_preserves_array.
