Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Automation.Switches.PureFactHints.

Lemma decodeItemOutcomeRepackWitness `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (outcome : DecodeItemOutcome) :
  @ZesuPureFactIntro Sigma
    (∃ data : li_prod DecodeItemOutcome unit,
      ⌜DecodeMeaningModuloKnownBugs args data.1ₗ⌝ ∗
      decodeItemExitResources args data.1ₗ)%I
    (⌜DecodeMeaningModuloKnownBugs args outcome⌝ ∗
      decodeItemExitResources args outcome)%I.
Proof.
  unfold ZesuPureFactIntro. iIntros "[Hmeaning Hexit]".
  iExists (outcome, tt)ₗ. iFrame.
Qed.

#[export] Hint Extern 1
  (@ZesuPureFactIntro ?Sigma
    (∃ data : li_prod DecodeItemOutcome unit,
      ⌜DecodeMeaningModuloKnownBugs ?args data.1ₗ⌝ ∗
      decodeItemExitResources ?args data.1ₗ)%I _) =>
  match goal with Hmeaning : DecodeMeaningModuloKnownBugs args ?outcome |- _ =>
    assert_fails (has_evar outcome);
    exact (decodeItemOutcomeRepackWitness args outcome)
  end : typeclass_instances.

Print Assumptions decodeItemOutcomeRepackWitness.
