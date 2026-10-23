Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Generated.DecodeItem.BootstrapRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemFoldInitializationWitnesses.
Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
Require Import ZesuSsz.Compliance.DecodeItemFoldZeroFacts.
Require Import ZesuSsz.Compliance.DecodeItemHeaderWitnessFacts.
Require Import ZesuSsz.Compliance.DecodeItemBranchGuardFacts.
Require Import ZesuSsz.Compliance.DecodeItemS40GuardFacts.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Open Scope Z_scope.

Require Import ZesuSsz.Compliance.DecodeItemInitializationPureFacts.
Require Import ZesuSsz.Generated.DecodeItem.Registrations.
Lemma initializationFirstGuardActivation args n payloadStart bytes :
  decodeItemByteFoldFacts args n 0 payloadStart bytes -> 0 < n.
Proof. intros Hfacts. zesu_pure_fact_hints_if_enabled. Qed.

Lemma initializationCursorActivation args isList prefix rest n payloadStart bytes :
  decodeItemFoldProvenance args isList prefix rest n payloadStart bytes ->
  (Z_to_bv 64 (decodeItemInputPointer args) + (Z_to_bv 64 n + 1))%bv =
    Z_to_bv 64 (payloadStart + n).
Proof. intros Hfacts. zesu_pure_fact_hints_if_enabled. Qed.

Lemma initializationStartCursorActivation args isList prefix rest n payloadStart bytes :
  decodeItemFoldProvenance args isList prefix rest n payloadStart bytes ->
  (Z_to_bv 64 (decodeItemInputPointer args) + 1)%bv = Z_to_bv 64 (payloadStart + 0).
Proof. intros Hfacts. zesu_pure_fact_hints_if_enabled. Qed.

Print Assumptions initializationFirstGuardActivation.
Print Assumptions initializationCursorActivation.
Print Assumptions initializationStartCursorActivation.
