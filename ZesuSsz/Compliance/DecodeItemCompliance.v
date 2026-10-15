Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.PromotedBodies.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Proofs.DecodeItem.Composition.CompleteFamily.
From Coq Require Import List ZArith.
Open Scope Z_scope.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6974Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d697cConditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d698cConditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69b0Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69e8Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a08Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a24Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a38Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a40Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a78Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6aa8Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ac4Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ad8Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ae0Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6b08Conditional.

Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6960Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.Composition.CompleteNativeFamily.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Proofs.DecodeItem.Auto.Block800d6974.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d697c.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d69e8.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6a08.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6b08.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d698c.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6a38.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6960.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6ae0.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6ac4.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6a24.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6aa8.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6ad8.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6a78.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d69b0.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6a40.

Require Import ZesuSsz.Compliance.DecodeItemCompositionalCompliance.
Require Import ZesuSsz.Compliance.DecodeItemCompositionalBridge.

Definition ReviewedDecodeItemComplianceType : Prop :=
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (decodeItemSelectedModel returnAddress).

Lemma decodeItemSelectedCompliance
 :
  ReviewedDecodeItemComplianceType.
Proof.
  unfold ReviewedDecodeItemComplianceType.
  intros returnAddress.
  apply decodeItemRegisterComplianceWeakens.
  apply decodeItemSelectedComplianceRegisters.
Qed.
Print Assumptions decodeItemSelectedCompliance.
