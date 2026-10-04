From Coq Require Import List ZArith.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ParentHeaderLevel1.
Require Import ZesuSsz.Contracts.ParentHeaderPendingTypes.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.
Require Import ZesuSsz.Evidence.PendingParentHeaderSignatureGates.

Definition fixtureNextPlainExtra (_ : False) := nextUint64PlainC1ATarget.
Definition fixtureParentPlainExtra (_ : False) := parentHeaderPlainC1ATarget.
Definition fixtureNextCandidateExtra (_ : False) := nextUint64CandidateTarget.
Definition fixtureParentCandidateExtra (_ : False) := parentHeaderCandidateTarget.

Fail Check (fixtureNextPlainExtra : NextUint64Call -> Prop).
Fail Check (fixtureParentPlainExtra :
  ParentHeaderCall -> (Z -> list byte -> Prop) -> Prop).
Fail Check (fixtureNextCandidateExtra :
  list byte -> Z -> NextUint64Call -> Prop).
Fail Check (fixtureParentCandidateExtra :
  ParentHeaderCall -> (Z -> list byte -> Prop) -> Prop).
