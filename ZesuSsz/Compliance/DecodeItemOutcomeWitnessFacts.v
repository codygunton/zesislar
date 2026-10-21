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

Print Assumptions decodeItemOutcomeRepackWitness.
