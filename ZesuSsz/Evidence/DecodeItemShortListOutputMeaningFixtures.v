Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Compliance.DecodeItemShortListOutputMeaning.
Lemma decodeItemShortListOutputMeaningConsumer args locals inputPrefix rest :
  decodeItemShortListOutputFacts args locals inputPrefix rest ->
  DecodeMeaningModuloKnownBugs args (decodeItemShortListUpdatedImage locals).
Proof.
  intros HoutputFacts.
  ZesuSsz.Automation.PureFacts.zesu_saturate_derived_facts; assumption.
Qed.
