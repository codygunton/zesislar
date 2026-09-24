Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.OutcomeHandoff.
Require Import ZesuSsz.Automation.Switches.OutcomeHandoff.
Require Import isla.riscv64.riscv64.

Lemma test_outcome_handoff_distractor `{!islaG Sigma} `{!threadG}
    (valid : list (bv 8) → Prop)
    (outcome : list (bv 8) → option (bv 64))
    (bytes other : list (bv 8)) (result : option (bv 64))
    (tail : spec)
    (Hvalid : valid bytes) (Houtcome : outcome bytes = result)
    (Hdistractor : outcome other = None) :
  spec_trace tail -∗
  ∃ x : spec *ₗ list (bv 8) *ₗ (),
    ⌜valid x.2ₗ⌝ ∗
    spec_trace (match outcome x.2ₗ with
                | Some _ => x.1ₗ | None => x.1ₗ end) ∗
    ⌜x.2ₗ = bytes⌝.
Proof.
  iIntros "Htrace".
  zesu_outcome_handoff_if_enabled.
  destruct result; simpl; (iSplitL "Htrace"; [iFrame | by iPureIntro]).
Qed.
Print Assumptions test_outcome_handoff_distractor.

Lemma test_outcome_handoff_requires_matching_outcome `{!islaG Sigma} `{!threadG}
    (valid : list (bv 8) → Prop)
    (outcome : list (bv 8) → option (bv 64))
    (bytes other : list (bv 8)) (tail : spec)
    (Hvalid : valid bytes) (Hdistractor : outcome other = None) :
  spec_trace tail -∗
  ∃ x : spec *ₗ list (bv 8) *ₗ (),
    ⌜valid x.2ₗ⌝ ∗ spec_trace (match outcome x.2ₗ with
                                  | Some _ => x.1ₗ | None => x.1ₗ end).
Proof.
  iIntros "Htrace".
  Fail zesu_outcome_handoff_if_enabled.
  iExists (tail, bytes, tt)ₗ.
  iSplit; [by iPureIntro |].
  red_li_prod.
  destruct (outcome bytes); iFrame.
Qed.
Print Assumptions test_outcome_handoff_requires_matching_outcome.
