Require Import ZesuSsz.Automation.All.
Require Import Scaffolding.DecodeItemNativeBlocksCompliance.
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
Require Import Scaffolding.DecodeItemComplianceStatement.
Require Import Scaffolding.DecodeItemSignatureGates.

Lemma decodeItemNativeBlocksSignatureFixture
  (native800d69b0 : forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte),
  decodeItemSelectedCode -∗
  instr_body 0x800d69b0
    (decodeItemEntryAt800d69b0 args locals inputPrefix rest ∗ True))
  (native800d6a40 : forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) (headerLength : Z) (payloadLength : Z),
  decodeItemSelectedCode -∗
  instr_body 0x800d6a40
    (decodeItemEntryAt800d6a40 args locals inputPrefix rest headerLength payloadLength ∗ True))
  (native800d6a78 : forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte),
  decodeItemSelectedCode -∗
  instr_body 0x800d6a78
    (decodeItemEntryAt800d6a78 args locals inputPrefix rest ∗ True))
 :
  ReviewedDecodeItemComplianceType.
Proof.
  exact (decodeItemNativeBlocksSelectedCompliance native800d69b0 native800d6a40 native800d6a78).
Qed.
Print Assumptions decodeItemNativeBlocksSignatureFixture.

Lemma decodeItemNativeBlocksMissing69b0Rejected
  (native800d69b0 : forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte),
  decodeItemSelectedCode -∗
  instr_body 0x800d69b0
    (decodeItemEntryAt800d69b0 args locals inputPrefix rest ∗ True))
  (native800d6a40 : forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) (headerLength : Z) (payloadLength : Z),
  decodeItemSelectedCode -∗
  instr_body 0x800d6a40
    (decodeItemEntryAt800d6a40 args locals inputPrefix rest headerLength payloadLength ∗ True))
  (native800d6a78 : forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte),
  decodeItemSelectedCode -∗
  instr_body 0x800d6a78
    (decodeItemEntryAt800d6a78 args locals inputPrefix rest ∗ True))
 :
  ReviewedDecodeItemComplianceType.
Proof.
  Fail exact (decodeItemNativeBlocksSelectedCompliance native800d6a40 native800d6a78).
  exact (decodeItemNativeBlocksSelectedCompliance native800d69b0 native800d6a40 native800d6a78).
Qed.
Print Assumptions decodeItemNativeBlocksMissing69b0Rejected.
