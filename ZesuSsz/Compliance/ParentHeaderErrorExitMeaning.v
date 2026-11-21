(* Step 2.4 M1: the meaning of decodeParentHeader's memcpy error exit.
   Owner: compliance proof (hand-written). Every edge into the tail join 0x00b0
   proves `candidateParentHeader (parentHeaderInputBytes args) =
   candidateHeaderError` (EdgeObligations.v, ParentHeaderEdgeObligations.v); the
   tail call's return package keeps it in its history (profile `tail_calls`
   `return_facts`). The exit copies the constant error union
   parentHeaderMemcpySourceBefore, which the domain states is
   parentHeaderError80; parentHeaderMeaningOfCandidateWellFormed gives the rest. *)
From Coq Require Import List ZArith.
From stdpp Require Import base bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Automation2.Hist.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Contracts.ParentHeaderCandidateWalk.
Require Import ZesuSsz.Compliance.ParentHeaderMeaningOfCandidate.
Require Import ZesuSsz.Compliance.ParentHeaderTailExitBridge.

(* The join's error fact, read from an opened package history. *)
Ltac ph_history_error :=
  match goal with H : zesu_hist _ |- _ => apply zesu_hist_elim in H; hnf in H end;
  repeat match goal with
  | H : ex _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  end;
  match goal with H : zesu_join_history (candidateParentHeader _ = candidateHeaderError) |- _ => exact H end.

Lemma parentHeaderTailExitMeaning_holds : parentHeaderTailExitMeaning.
Proof.
  intros args returnAddress call_after _ Hwf Hh.
  apply parentHeaderMeaningOfCandidateWellFormed; [exact Hwf|].
  apply parentHeaderCandidateResultError; [ph_history_error|].
  destruct Hwf as (_ & _ & _ & _ & Herror & _). exact Herror.
Qed.
