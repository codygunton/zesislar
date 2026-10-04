From Coq Require Import List ZArith.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ParentHeaderLevel1.

(* These closed pure targets are pending machine contracts. They do not
   supply code resources, a memcpy service, or a compliance theorem. *)
Definition nextUint64PlainC1ATarget : NextUint64Call -> Prop :=
  nextUint64Domain.

Definition parentHeaderPlainC1ATarget (args : ParentHeaderCall)
    (callInputAt : Z -> list byte -> Prop) : Prop :=
  parentHeaderDomain args /\ nestedC1AObligation callInputAt.
