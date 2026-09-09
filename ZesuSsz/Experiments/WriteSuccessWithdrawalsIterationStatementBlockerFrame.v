From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerBasic.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerState.

Open Scope Z_scope.

Local Opaque writeSuccessBlockerRepresentedMemory.

Lemma writeSuccessBlockerFrameHeader memory :
  writeSuccessWithdrawalsMemoryFrame writeSuccessBlockerSp memory
    writeSuccessBlockerRepresentedMemory ->
  writeSuccessMemoryInteger memory
    (writeSuccessBlockerOwner + 32) 8 writeSuccessBlockerScratch.
Proof.
  intros [_ Hframe].
  have Hagree :
      read_mem_list memory (writeSuccessBlockerOwner + 32) 8%N =
      read_mem_list writeSuccessBlockerRepresentedMemory
        (writeSuccessBlockerOwner + 32) 8%N.
  { unfold read_mem_list. apply mapM_ext_in.
    intros location Hlocation.
    have Hrange : writeSuccessBlockerOwner + 32 <= location <
        writeSuccessBlockerOwner + 32 + 8.
    { apply elem_of_list_In in Hlocation. apply elem_of_seqZ in Hlocation.
      cbn in Hlocation. lia. }
    destruct (Z_to_bv_checked 64 location) as [key|] eqn:Hkey;
      cbn; last reflexivity.
    apply Z_to_bv_checked_Some in Hkey. subst location.
    rewrite Hframe; first reflexivity.
    - rewrite writeSuccessBlockerSpUnsigned.
      unfold writeSuccessBlockerOwner in Hrange. cbn in Hrange. lia.
    - rewrite writeSuccessBlockerSpUnsigned.
      unfold writeSuccessBlockerOwner in Hrange. cbn in Hrange. lia. }
  unfold writeSuccessMemoryInteger, writeSuccessMemoryBytes in *.
  rewrite Hagree. exact writeSuccessBlockerExtraDataHeader.
Qed.

Print Assumptions writeSuccessBlockerFrameHeader.
