From Coq Require Import List ZArith.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Compliance.ProjectionParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderLevel1.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Contracts.ParentHeaderBugTriggers.

Open Scope Z_scope.

Definition parentHeaderSailNode (bytes : list byte) :
    StatelessInputSliceFields 0 (Z.of_nat (List.length bytes)) :=
  @Build_StatelessInputSliceFields 0 (Z.of_nat (List.length bytes))
    0 (Z.of_nat (List.length bytes)).

(* Sail agrees with the candidate: where the candidate succeeds, Sail
   succeeds on the same bytes and its base fee, blob gas used and excess
   blob gas equal the candidate's (Sail does not return gas limit, gas used
   or timestamp); where the candidate rejects, Sail rejects. *)
Definition parentHeaderSailAgrees (bytes : list byte) : Prop :=
  match candidateParentHeader bytes with
  | candidateHeaderSuccess header =>
      ParentHeaderSuccess bytes (parentHeaderSailNode bytes) header
  | candidateHeaderError =>
      ParentHeaderRejects bytes (parentHeaderSailNode bytes)
  end.

(* The meaning of one decodeParentHeader call: the call is in the domain,
   the result bytes are exactly the candidate's (success record or error
   union), and Sail agrees with the candidate or the input triggers a
   registered KnownBug class. *)
Definition ParentHeaderMeaningModuloKnownBugs
    (args : ParentHeaderCall) (result : list byte) : Prop :=
  parentHeaderDomain args /\
  parentHeaderCandidateResult args.(headerInputBytes) result /\
  (parentHeaderSailAgrees args.(headerInputBytes) \/
   exists bug, List.In bug knownBugs /\
     parentHeaderBugTrigger bug args.(headerInputBytes) = true).
