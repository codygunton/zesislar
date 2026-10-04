From Coq Require Import List.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.
Require Import ZesuSsz.Evidence.PendingParentHeaderSignatureGates.

Definition fixtureNestedWrapExtra (_ : False) := nestedWrapOccurs.
Fail Check (fixtureNestedWrapExtra : list byte -> Prop).
