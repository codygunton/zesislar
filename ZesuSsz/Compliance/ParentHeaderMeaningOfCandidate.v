(* Plan step 2.4: the meaning of a decodeParentHeader call follows from the
   candidate's result. The third conjunct of ParentHeaderMeaningModuloKnownBugs
   is a case split on the boolean triggers of the registered known bugs: when
   one fires it is the witness, otherwise M2 (candidateParentHeader_sail) gives
   Sail's agreement. Every exit (error and success) closes through this lemma. *)
From Coq Require Import Bool List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ParentHeaderLevel1.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Contracts.ParentHeaderBugTriggers.
Require Import ZesuSsz.Contracts.ParentHeaderRung2.
Require Import ZesuSsz.Compliance.ParentHeaderTriggerCoverage.

Lemma parentHeaderMeaningOfCandidate (call : ParentHeaderCall) (result : list byte) :
  parentHeaderDomain call ->
  headerFits call.(headerInputBytes) ->
  Z.of_nat (List.length call.(headerInputBytes)) < 2 ^ 31 ->
  parentHeaderCandidateResult call.(headerInputBytes) result ->
  ParentHeaderMeaningModuloKnownBugs call result.
Proof.
  intros Hdomain Hfits Hlength Hresult.
  split; [exact Hdomain|]. split; [exact Hresult|].
  destruct (existsb (fun bug => parentHeaderBugTrigger bug call.(headerInputBytes)) knownBugs)
    eqn:Htriggers.
  - right. apply existsb_exists in Htriggers. exact Htriggers.
  - left. apply candidateParentHeader_sail; [exact Hfits|exact Hlength|].
    intros bug Hin. apply not_true_is_false. intros Hfires.
    assert (Hsome : existsb (fun bug => parentHeaderBugTrigger bug call.(headerInputBytes)) knownBugs = true)
      by (apply existsb_exists; exists bug; split; [exact Hin|exact Hfires]).
    rewrite Hsome in Htriggers. discriminate.
Qed.

(* The machine domain gives the three side conditions: the layout, the outer
   header fit, and an input of at most 2^30 bytes (it lies in the input window). *)
Lemma parentHeaderMeaningOfCandidateWellFormed (args : ParentHeaderArgs) (result : list byte) :
  parentHeaderArgsWellFormed args ->
  parentHeaderCandidateResult (parentHeaderInputBytes args) result ->
  ParentHeaderMeaningModuloKnownBugs (parentHeaderCall args) result.
Proof.
  intros Hwf Hresult.
  apply parentHeaderMeaningOfCandidate; [apply parentHeaderArgsWellFormed_domain, Hwf| | |exact Hresult].
  - cbn. unfold parentHeaderArgsWellFormed in Hwf.
    repeat match goal with H : _ /\ _ |- _ => destruct H as [_ H] end. exact Hwf.
  - cbn. unfold parentHeaderArgsWellFormed in Hwf.
    destruct Hwf as (Hlen & _ & _ & _ & _ & Hlow & Hhigh & _).
    pose proof (bv_unsigned_in_range 64 (parentHeaderInputPointer args)).
    rewrite Hlen. lia.
Qed.
