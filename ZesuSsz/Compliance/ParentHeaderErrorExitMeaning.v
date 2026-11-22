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
Require Import ZesuSsz.Compliance.ParentHeaderExitBridgeTactics.
Require Import ZesuSsz.Compliance.ParentHeaderCandidateFacts.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.

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

(* The direct error return (slot 0 of 0x0274): every edge into 0x0270 proves
   the error fact and that the tag x10 it stores at bytes 72 and 73 is 3
   (`ErrorTag`); the package keeps both in its history. *)
Lemma parentHeaderSlot0ExitMeaning_holds :
  ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0_ExitMeaning
    parentHeaderResultMeaning.
Proof.
  intros args returnAddress call10_after call_after x10 out u0 u74 Hh [_ Hwf] _ _ _ _ _ _ H0 H74.
  apply parentHeaderMeaningOfCandidateWellFormed; [exact Hwf|].
  apply zesu_hist_elim in Hh; hnf in Hh.
  repeat match goal with
  | H : ex _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  end.
  apply parentHeaderCandidateResultError.
  - match goal with H : zesu_join_history (candidateParentHeader _ = candidateHeaderError) |- _ => exact H end.
  - apply phError80Store; [exact H0 | exact H74|].
    match goal with H : zesu_join_history (bv_unsigned x10 = 3) |- _ => exact H end.
Qed.
