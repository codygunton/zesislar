From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOff.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationPreservationCore.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationPreservationOk.
Require Import ZesuSsz.Experiments.WriteSuccessStackRange.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Open Scope Z_scope.

Lemma writeSuccessReadMemListWithdrawalsFrames
    topSp sp before after frame address len :
  bv_unsigned sp = topSp - 2000 ->
  writeSuccessWithdrawalsMemoryFrame sp before frame ->
  writeSuccessWithdrawalsMemoryFrame sp after frame ->
  writeSuccessAvoidsRange (writeSuccessCalleeStackLow topSp) topSp address len ->
  read_mem_list after address (N.of_nat len) =
    read_mem_list before address (N.of_nat len).
Proof.
  intros Hsp [_ Hbefore] [_ Hafter] Havoids.
  unfold read_mem_list. apply mapM_ext_in.
  intros location Hlocation.
  apply elem_of_list_In in Hlocation. apply elem_of_seqZ in Hlocation.
  destruct (Z_to_bv_checked 64 location) as [key|] eqn:Hkey;
    cbn; last reflexivity.
  apply Z_to_bv_checked_Some in Hkey. subst location.
  have Houtside :
      bv_unsigned key < writeSuccessCalleeStackLow topSp \/
      topSp <= bv_unsigned key.
  { unfold writeSuccessAvoidsRange in Havoids.
    destruct Havoids as [Hempty|[Hleft|Hright]].
    - subst len. cbn in Hlocation. lia.
    - left. lia.
    - right. lia. }
  have HscratchLow :
      ~ (bv_unsigned sp - 16 <= bv_unsigned key < bv_unsigned sp).
  { intros [Hlower Hupper]. rewrite Hsp in Hlower, Hupper.
    unfold writeSuccessCalleeStackLow, writeSuccessHelperStackDepth in Houtside.
    destruct Houtside; lia. }
  have HscratchHigh :
      ~ (bv_unsigned sp + 1744 <= bv_unsigned key <
         bv_unsigned sp + 1792).
  { intros [Hlower Hupper]. rewrite Hsp in Hlower, Hupper.
    unfold writeSuccessCalleeStackLow, writeSuccessHelperStackDepth in Houtside.
    destruct Houtside; lia. }
  transitivity (frame !! key).
  - apply Hafter; assumption.
  - symmetry. apply Hbefore; assumption.
Qed.

Theorem writeSuccessConcreteRepresentationOffWithdrawalsFrames
    topSp sp decoded before after frame address :
  bv_unsigned sp = topSp - 2000 ->
  writeSuccessConcreteRepresentationOff topSp decoded before address ->
  writeSuccessWithdrawalsMemoryFrame sp before frame ->
  writeSuccessWithdrawalsMemoryFrame sp after frame ->
  writeSuccessConcreteRepresentationOff topSp decoded after address.
Proof.
  intros Hsp Hrepresentation Hbefore Hafter.
  unfold writeSuccessConcreteRepresentationOff in Hrepresentation |- *.
  eapply writeSuccessConcreteRepresentationOkReadsEqual;
    last exact Hrepresentation.
  intros pointer len Havoids.
  eapply writeSuccessReadMemListWithdrawalsFrames; eassumption.
Qed.

Print Assumptions writeSuccessReadMemListWithdrawalsFrames.
Print Assumptions writeSuccessConcreteRepresentationOffWithdrawalsFrames.
