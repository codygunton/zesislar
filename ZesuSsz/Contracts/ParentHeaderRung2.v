From Coq Require Import List ZArith.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Compliance.ProjectionParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderLevel1.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ParentHeaderRequiredFields.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.

Open Scope Z_scope.

Definition parentHeaderSailNode (bytes : list byte) :
    StatelessInputSliceFields 0 (Z.of_nat (List.length bytes)) :=
  @Build_StatelessInputSliceFields 0 (Z.of_nat (List.length bytes))
    0 (Z.of_nat (List.length bytes)).

Definition parentHeaderNestedBugApplies (bug : KnownBug)
    (bytes : list byte) : Prop :=
  match bug with
  | RlpLongLengthWrap => nestedWrapOccurs bytes
  end.

Definition parentHeaderSuccessAgreement (bytes result : list byte) : Prop :=
  exists header,
    parentHeaderResult80 result header /\
    (ParentHeaderSuccess bytes (parentHeaderSailNode bytes) header \/
     exists bug, List.In bug knownBugs /\
       parentHeaderNestedBugApplies bug bytes).

Definition parentHeaderRejectionAgreement (bytes result : list byte) : Prop :=
  parentHeaderError80 result /\
  (ParentHeaderRejects bytes (parentHeaderSailNode bytes) \/
   parentHeaderMissingRequiredField bytes).

(* R2-1 is a named rejection-side class. The user has not yet decided
   whether the final claim keeps this class or narrows its input domain. *)
Definition ParentHeaderMeaningModuloKnownBugs
    (args : ParentHeaderCall) (result : list byte) : Prop :=
  parentHeaderDomain args /\
  (parentHeaderSuccessAgreement args.(headerInputBytes) result \/
   parentHeaderRejectionAgreement args.(headerInputBytes) result).
