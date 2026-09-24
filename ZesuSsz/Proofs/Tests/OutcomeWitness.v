Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.OutcomeWitness.
Require Import isla.riscv64.riscv64.

Local Instance test_outcome_witness_switch : ZesuStepOutcomeWitness := I.

Lemma test_select_outcome_witness `{!islaG Sigma} `{!threadG}
    (valid : list (bv 8) -> Prop)
    (outcome : list (bv 8) -> option (bv 64))
    (bytes : list (bv 8)) (tail : spec) (result : option (bv 64))
    (other : nat) :
  valid bytes -> outcome bytes = result -> other = other ->
  (True%I : iProp Sigma) ⊢
    (∃ x : spec *ₗ list (bv 8) *ₗ (),
      ⌜valid x.2ₗ⌝ ∗
      ⌜x.1ₗ = tail⌝ ∗
      ⌜(match outcome x.2ₗ with
        | Some value => Some value
        | None => None
        end) =
        (match result with
         | Some value => Some value
         | None => None
         end)⌝ ∗ True)%I.
Proof.
  intros Hvalid Houtcome Hdistractor.
  iStartProof.
  iIntros "_".
  zesu_select_outcome_witness.
  iSplit; first (iPureIntro; reflexivity).
  iSplit; first (zesu_rewrite_selected_outcome; iPureIntro; destruct result; reflexivity).
  done.
Qed.
Print Assumptions test_select_outcome_witness.

Lemma test_select_matching_outcome_witness `{!islaG Sigma} `{!threadG}
    (valid otherValid : list (bv 8) -> Prop)
    (outcome : list (bv 8) -> option (bv 64))
    (bad good : list (bv 8)) (tail : spec) (result : option (bv 64)) :
  valid bad -> valid good -> otherValid good ->
  outcome good = result ->
  (True%I : iProp Sigma) ⊢
    (∃ x : spec *ₗ list (bv 8) *ₗ (),
      ⌜valid x.2ₗ⌝ ∗
      ⌜x.2ₗ = good⌝ ∗
      ⌜x.1ₗ = tail⌝ ∗
      ⌜(match outcome x.2ₗ with
        | Some value => Some value
        | None => None
        end) = result⌝ ∗ True)%I.
Proof.
  intros Hbad Hgood Hother Houtcome.
  iStartProof. iIntros "_".
  zesu_select_outcome_witness.
  iSplit; first (iPureIntro; reflexivity).
  iSplit; first (iPureIntro; reflexivity).
  iSplit; first (zesu_rewrite_selected_outcome; iPureIntro; destruct result; reflexivity).
  done.
Qed.
Print Assumptions test_select_matching_outcome_witness.
