From Coq Require Import Bool List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Values.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListBugTriggers.
Require Import ZesuSsz.Contracts.TxAccessListMeaning.
Require Import ZesuSsz.Compliance.TxAccessListSailAgreementStatements.
Require Import ZesuSsz.Compliance.TxAccessListSailAgreement.

Import ListNotations.
Open Scope Z_scope.

(* Plan B6, final step. txAccessListSailAgreesModuloProposed proves the
   "Sail agrees" side up to the three conditions of
   accessListProposedTriggers. Those conditions are now the registered
   KnownBug classes AccessListAddressLength, AccessListKeyLength and
   AccessListEntryTrailingBytes (txAccessListBugTrigger), so the Sail
   disjunct of TxAccessListMeaningModuloKnownBugs holds on the domain. *)

Lemma accessListProposedTriggersRegistered (input : list byte) :
  existsb (fun triggered => triggered) (accessListProposedTriggers input) = true ->
  exists bug, List.In bug knownBugs /\ txAccessListBugTrigger bug input = true.
Proof.
  unfold accessListProposedTriggers; simpl.
  destruct (accessListAddressLengthb input) eqn:address.
  { intros _; exists AccessListAddressLength; split; [simpl; tauto | exact address]. }
  destruct (accessListKeyLengthb input) eqn:key.
  { intros _; exists AccessListKeyLength; split; [simpl; tauto | exact key]. }
  destruct (accessListEntryTrailingb input) eqn:trailing.
  { intros _; exists AccessListEntryTrailingBytes; split; [simpl; tauto | exact trailing]. }
  discriminate.
Qed.

(* The Sail disjunct of TxAccessListMeaningModuloKnownBugs, on the domain. *)
Theorem txAccessListSailAgreement :
  forall input : list byte,
    txAccessListDomain input ->
    txAccessListSailAgrees input \/
    exists bug, List.In bug knownBugs /\ txAccessListBugTrigger bug input = true.
Proof.
  intros input domain.
  destruct (txAccessListSailAgreesModuloProposed input domain) as [agrees | triggered].
  - left; exact agrees.
  - right; exact (accessListProposedTriggersRegistered input triggered).
Qed.

(* The meaning of one call follows from its domain and its outcome class. *)
Corollary txAccessListMeaningOfOutcome :
  forall (input : list byte) (outcome : TxAccessListOutcomeClass) (consumed : Z),
    txAccessListDomain input ->
    txAccessListOutcomeAllowed input outcome consumed ->
    TxAccessListMeaningModuloKnownBugs input outcome consumed.
Proof.
  intros input outcome consumed domain allowed.
  exact (conj domain (conj allowed (txAccessListSailAgreement input domain))).
Qed.
