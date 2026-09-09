From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerBasic.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerState.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessBlockerCurrentFirst memory :
  read_mem_list memory writeSuccessBlockerScratch 48%N =
    Some writeSuccessBlockerCurrent ->
  read_mem_list memory writeSuccessBlockerScratch 1%N =
    Some [Z_to_bv 8 1].
Proof.
  intro Hread.
  destruct (read_mem_list_split memory writeSuccessBlockerScratch
      1 47 writeSuccessBlockerCurrent Hread) as
    (first & rest & Hparts & HfirstLength & HrestLength & Hfirst & Hrest).
  unfold writeSuccessBlockerCurrent in Hparts.
  destruct first as [|byte first]; cbn in HfirstLength; first discriminate.
  destruct first; cbn in HfirstLength; last discriminate.
  cbn in Hparts. inversion Hparts. subst byte. exact Hfirst.
Qed.

Print Assumptions writeSuccessBlockerCurrentFirst.
