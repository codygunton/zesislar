From Coq Require Import List ZArith.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ParentHeaderLevel1.
Require Import ZesuSsz.Contracts.ParentHeaderPendingTypes.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.

Definition ReviewedNextUint64PlainTarget : NextUint64Call -> Prop :=
  nextUint64Domain.
Definition ReviewedParentHeaderPlainTarget :
    ParentHeaderCall -> (Z -> list byte -> Prop) -> Prop :=
  fun args callInputAt =>
    parentHeaderDomain args /\ nestedC1AObligation callInputAt.

Definition ReviewedNextUint64CandidateTarget :
    list byte -> Z -> NextUint64Call -> Prop :=
  fun parentInput pc call =>
    allContiguousHeadersFit parentInput /\
    List.In pc parentHeaderNextUint64CallSites /\
    candidateCallInputAt parentInput pc call.(nextInputBytes) /\
    nextUint64Domain call.
Definition ReviewedParentHeaderCandidateTarget :
    ParentHeaderCall -> (Z -> list byte -> Prop) -> Prop :=
  fun args callInputAt =>
    parentHeaderEntryLayout
      args.(headerInputPointer)
      (Z.of_nat (List.length args.(headerInputBytes)))
      args.(headerResultPointer) args.(headerStackPointer)
      args.(headerReturnAddress) /\
    allContiguousHeadersFit args.(headerInputBytes) /\
    reachedCallCorrespondence args.(headerInputBytes) callInputAt.

Check (eq_refl : nextUint64PlainC1ATarget = ReviewedNextUint64PlainTarget).
Check (eq_refl : parentHeaderPlainC1ATarget = ReviewedParentHeaderPlainTarget).
Check (eq_refl : nextUint64CandidateTarget = ReviewedNextUint64CandidateTarget).
Check (eq_refl : parentHeaderCandidateTarget = ReviewedParentHeaderCandidateTarget).

(* The four public machine theorem checks remain pending concrete code
   resources, the memcpy service, and the source-to-result relation. *)
