Require Import isla.riscv64.riscv64.
From stdpp Require Import list.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SpecPrefix.
Require Import ZesuSsz.Automation.LoadedTrace.
Require Import ZesuSsz.Automation.V2Steps.
Require Import ZesuSsz.Proofs.Tests.LoadedTrace.

Local Instance loaded_trace_test_spec_tail : ZesuStepSpecTail := I.

Lemma loaded_trace_no_switch_fallthrough `{!islaG Sigma} `{!threadG}
    (tail : spec) :
  ⊢ ((∃ x : spec *ₗ (), ⌜x.1ₗ = tail⌝ ∗ True)%I : iProp Sigma).
Proof.
  iStartProof.
  zesu_rule_set_v2_steps.
  iPureIntro; exact I.
Qed.

Local Instance loaded_trace_test_switch : ZesuStepLoadedTrace := I.

Lemma loaded_trace_wrapper `{!islaG Sigma} `{!threadG}
    (words : list (bv 64)) (index : nat) (fallback loaded : bv 64)
    (event : seq_event) (addr : Z) (tail : spec) :
  ⊢ ((⌜words !! index = Some loaded⌝ -∗
  ∃ x : spec *ₗ (),
    ⌜scons_snap event
      (λ snapshot, read_mem_list (snap_mem snapshot) addr 8 =
        Some (loaded_word_bytes8 loaded)) x.1ₗ ⊆
      scons_snap event
      (λ snapshot, read_mem_list (snap_mem snapshot) addr 8 =
        Some (loaded_word_bytes8 (default fallback (words !! index)))) tail⌝ ∗
    True)%I : iProp Sigma).
Proof.
  iStartProof.
  iIntros "%Hlookup".
  zesu_rule_set_v2_steps.
  iPureIntro; exact I.
Qed.

Print Assumptions loaded_trace_no_switch_fallthrough.
Print Assumptions loaded_trace_wrapper.
