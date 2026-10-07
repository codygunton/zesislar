Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.InstructionLookup.
Require Import ZesuSsz.Automation.Switches.RamFault.
Require Import ZesuSsz.Automation.Switches.EvarSideconditionGuard.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemFoldInitializationWitnesses.
Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Automation.Switches.StackWrite.
Require Import ZesuSsz.Automation.Switches.RegionFault.
Require Import ZesuSsz.Automation.Switches.LowMask.
Require Import ZesuSsz.Automation.Switches.IntegerArrayAddress.
Require Import ZesuSsz.Automation.Switches.RecordWitness.
Require Import ZesuSsz.Automation.Switches.ArrayBounds.
Require Import ZesuSsz.Automation.Switches.WordArrayHandoff.
Require Import ZesuSsz.Automation.Switches.ReturnBundle.
Require Import ZesuSsz.Automation.Switches.ReturnWand.
Require Import ZesuSsz.Automation.Switches.StrictSigned.
Require Import ZesuSsz.Automation.Switches.ListWitness.
Require Import ZesuSsz.Automation.Switches.TupleWitness.
Require Import ZesuSsz.Automation.Switches.ArrayRegionBounds.
Require Import ZesuSsz.Automation.Switches.KnownPairWitness.
Require Import ZesuSsz.Automation.Switches.PureWitnessConstraints.
Require Import ZesuSsz.Automation.Switches.RegisterCollectionSelection.
Require Import ZesuSsz.Automation.Switches.RegionFaultNormalization.
Require Import ZesuSsz.Automation.Switches.CanonicalAnchor.
Require Import ZesuSsz.Compliance.DecodeItemBranchGuardFacts.
Require Import ZesuSsz.Compliance.DecodeItemDataWitnessFacts.
Require Import ZesuSsz.Compliance.DecodeItemOutcomeWitnessFacts.
Require Import ZesuSsz.Compliance.DecodeItemFoldRejectionFacts.
Require Import ZesuSsz.Compliance.DecodeItemFoldZeroFacts.
Require Import ZesuSsz.Compliance.DecodeItemHeaderWitnessFacts.
Require Import ZesuSsz.Compliance.DecodeItemOutputBaseWitnessFacts.
Require Import ZesuSsz.Compliance.DecodeItemShortListHandoffFacts.
Require Import ZesuSsz.Compliance.DecodeItemFoldBackEdgeWitnesses.
Require Import ZesuSsz.Compliance.DecodeItemS40GuardFacts.
Require Import ZesuSsz.Compliance.DecodeItemCanonicalAnchors.
Require Import ZesuSsz.Compliance.DecodeItemCompletedFoldFacts.
Require Import ZesuSsz.Compliance.DecodeItemInitializationPureFacts.
Open Scope Z_scope.

Lemma decodeItemJoin6ac4From6ab4_correct `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte) (oldAcc oldCursor loaded : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  ⊢ decodeItemJoin6ac4From6ab4 args n payloadStart lengthBytes frameBytes
      oldAcc oldCursor loaded inputPrefix rest.
Proof.
  zesu_block.
Qed.

Print Assumptions decodeItemJoin6ac4From6ab4_correct.

