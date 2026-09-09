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

Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerFrame.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerCurrent.

Lemma writeSuccessBlockerRequiredPostContradiction memory :
  writeSuccessConcreteRepresentation writeSuccessBlockerDecoded memory
    writeSuccessBlockerOwner ->
  writeSuccessWithdrawalsMemoryFrame writeSuccessBlockerSp memory
    writeSuccessBlockerRepresentedMemory ->
  read_mem_list memory writeSuccessBlockerScratch 48%N =
    Some writeSuccessBlockerCurrent ->
  False.
Proof.
  intros Hrepresentation Hframe Hcurrent.
  pose proof (writeSuccessRepresentationExtraData _ _ _ Hrepresentation) as
    Hslice.
  destruct Hslice as
    (pointer & HpointerRange & Hpointer & Hlength & Hbyte).
  have Hheader := writeSuccessBlockerFrameHeader memory Hframe.
  have HpointerEq : pointer = writeSuccessBlockerScratch.
  { eapply writeSuccessMemoryInteger64Injective with
      (first := pointer) (second := writeSuccessBlockerScratch).
    - unfold writeSuccessUnsignedValid. exact HpointerRange.
    - unfold writeSuccessUnsignedValid, writeSuccessBlockerScratch.
      cbn. lia.
    - exact Hpointer.
    - exact Hheader. }
  subst pointer.
  unfold writeSuccessMemoryBytes in Hbyte. cbn in Hbyte.
  pose proof (writeSuccessBlockerCurrentFirst memory Hcurrent) as Hfirst.
  rewrite Hfirst in Hbyte. discriminate.
Qed.

Print Assumptions writeSuccessBlockerRequiredPostContradiction.
