(* The meaning conjunct of txAccessList's two exits (the return slots of the
   duplicated return block 0x04b8), from the facts their return packages
   carry and the Sail agreement (txAccessListMeaningOfOutcome).
   Success: the outer walk reached the end of the first item's payload.
   Error: the join +0x4a8 carries the allowed error class of `consumed`. *)
From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemPayloadBounds.
Require Import ZesuSsz.Contracts.ParentHeaderCandidateWalk.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListMeaning.
Require Import ZesuSsz.Contracts.TxAccessListLoopFacts.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Compliance.TxAccessListSailAgreementTheorem.

Import ListNotations.
Open Scope Z_scope.

Lemma tx_skipn_firstn_same {A} (n : nat) (l : list A) : skipn n (firstn n l) = [].
Proof. apply skipn_all2. rewrite firstn_length. lia. Qed.

(* The outer walk at the end of the payload is the candidate's acceptance. *)
Lemma txAccessList_outer_walked_accepted (input : list byte) (h p : Z)
    (done : list AccessListEntryValue) :
  candidateDecodeItem input = candidateSuccess true h p ->
  txAccessListOuterWalked input (h + p) done ->
  0 <= h + p < word64Modulus ->
  candidateAccessList input = accessListAccepted done (h + p).
Proof.
  intros Hdec (h' & p' & Hdec' & _ & Hwalk) Hrange.
  rewrite Hdec in Hdec'. injection Hdec' as <- <-.
  replace (h + p - h) with p in Hwalk by lia.
  cbv zeta in Hwalk. unfold itemPayload in Hwalk.
  rewrite tx_skipn_firstn_same in Hwalk. cbn [List.length accessListEntriesWalk snd option_map] in Hwalk.
  unfold candidateAccessList, accessListWalk. rewrite Hdec. cbv zeta. unfold itemPayload.
  destruct (accessListEntriesWalk _ _) as [trace entries] eqn:W.
  cbn [snd] in Hwalk |- *. rewrite Hwalk. rewrite app_nil_r.
  unfold itemConsumed. rewrite Z.mod_small; [reflexivity|lia].
Qed.

Lemma txAccessList_domain (args : TxAccessListArgs) :
  txAccessListArgsWellFormed args -> txAccessListDomain (txInputBytes args).
Proof.
  unfold txAccessListArgsWellFormed. intros H. do 15 (destruct H as [_ H]). exact H.
Qed.

Lemma txAccessList_success_meaning (args : TxAccessListArgs) (h p : Z)
    (done : list AccessListEntryValue) :
  txAccessListArgsWellFormed args ->
  candidateDecodeItem (txInputBytes args) = candidateSuccess true h p ->
  txAccessListOuterWalked (txInputBytes args) (h + p) done ->
  TxAccessListMeaningModuloKnownBugs (txInputBytes args) (txAccessListOk done) (h + p).
Proof.
  intros Hwf Hdec Hwalk.
  pose proof (txAccessList_domain args Hwf) as Hdom.
  pose proof (candidateDecodeItemSuccessBounds _ _ _ _ Hdec) as (Hh & _).
  pose proof (candidatePayloadNonneg _ _ _ _ Hdec) as Hp.
  pose proof Hdom as (_ & Hlimit). rewrite Hdec in Hlimit.
  apply txAccessListMeaningOfOutcome; [exact Hdom|].
  cbn. apply txAccessList_outer_walked_accepted; [exact Hdec|exact Hwalk|lia].
Qed.

Lemma txAccessList_error_meaning (args : TxAccessListArgs) (consumed : Z) :
  txAccessListArgsWellFormed args ->
  txAccessListOutcomeAllowed (txInputBytes args) txAccessListInvalidInput consumed \/
  txAccessListOutcomeAllowed (txInputBytes args) txAccessListAllocationFailure consumed ->
  exists outcome,
    (outcome = txAccessListInvalidInput \/ outcome = txAccessListAllocationFailure) /\
    TxAccessListMeaningModuloKnownBugs (txInputBytes args) outcome consumed.
Proof.
  intros Hwf Hallowed. pose proof (txAccessList_domain args Hwf) as Hdom.
  destruct Hallowed as [H|H].
  - exists txAccessListInvalidInput. split; [tauto|].
    exact (txAccessListMeaningOfOutcome _ _ _ Hdom H).
  - exists txAccessListAllocationFailure. split; [tauto|].
    exact (txAccessListMeaningOfOutcome _ _ _ Hdom H).
Qed.
