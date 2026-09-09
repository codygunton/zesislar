From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHelperMemoryFrame.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessReadMemListWithinWithdrawalsFrames sp before after frame
    base totalLength address length :
  writeSuccessWithdrawalsMemoryFrame sp before frame ->
  writeSuccessWithdrawalsMemoryFrame sp after frame ->
  islaMemoryRangesDisjoint base totalLength (bv_unsigned sp - 16) 16 ->
  islaMemoryRangesDisjoint base totalLength (bv_unsigned sp + 1744) 48 ->
  base <= address ->
  address + Z.of_nat length <= base + Z.of_nat totalLength ->
  read_mem_list after address (N.of_nat length) =
    read_mem_list before address (N.of_nat length).
Proof.
  intros Hbefore Hafter HlowDisjoint HhighDisjoint Haddress Hlimit.
  unfold read_mem_list. apply mapM_ext_in. intros location Hlocation.
  apply elem_of_list_In in Hlocation. apply elem_of_seqZ in Hlocation.
  destruct (Z_to_bv_checked 64 location) as [key|] eqn:Hkey;
    cbn; last reflexivity.
  apply Z_to_bv_checked_Some in Hkey. subst location.
  apply writeSuccessWithdrawalsMemoryFramesLookup with (sp := sp) (frame := frame);
    try assumption.
  - intro Hinside. destruct HlowDisjoint; lia.
  - intro Hinside. destruct HhighDisjoint; lia.
Qed.

Theorem writeSuccessWithdrawalItemsAtWithdrawalsFrames sp before after frame
    base items :
  writeSuccessWithdrawalsMemoryFrame sp before frame ->
  writeSuccessWithdrawalsMemoryFrame sp after frame ->
  islaMemoryRangesDisjoint base (48 * length items)
    (bv_unsigned sp - 16) 16 ->
  islaMemoryRangesDisjoint base (48 * length items)
    (bv_unsigned sp + 1744) 48 ->
  Forall writeSuccessWithdrawalObservationValid items ->
  writeSuccessWithdrawalItemsAt before base items ->
  writeSuccessWithdrawalItemsAt after base items.
Proof.
  intros HbeforeFrame HafterFrame HlowDisjoint HhighDisjoint Hvalid Hitems.
  unfold writeSuccessWithdrawalItemsAt in *. intros index item Hnth.
  specialize (Hitems index item Hnth).
  have Hindex : (index < length items)%nat.
  { apply nth_error_Some. rewrite Hnth. discriminate. }
  have HitemValid : writeSuccessWithdrawalObservationValid item.
  { apply (proj1 (Forall_forall _ _) Hvalid).
    apply elem_of_list_In. eapply nth_error_In. exact Hnth. }
  have HaddressLength : length (observationWithdrawalAddress item) = 20%nat by
    (unfold writeSuccessWithdrawalObservationValid,
      writeSuccessBytesValid in HitemValid; tauto).
  unfold writeSuccessWithdrawalMemory, writeSuccessMemoryInteger,
    writeSuccessMemoryBytes in Hitems |- *.
  destruct Hitems as (HindexRead & HvalidatorRead & HamountRead & HaddressRead).
  repeat split.
  - rewrite (writeSuccessReadMemListWithinWithdrawalsFrames sp before after frame
      base (48 * length items) (base + 48 * Z.of_nat index) 8);
      try assumption; lia.
  - rewrite (writeSuccessReadMemListWithinWithdrawalsFrames sp before after frame
      base (48 * length items) (base + 48 * Z.of_nat index + 8) 8);
      try assumption; lia.
  - rewrite (writeSuccessReadMemListWithinWithdrawalsFrames sp before after frame
      base (48 * length items) (base + 48 * Z.of_nat index + 16) 8);
      try assumption; lia.
  - rewrite (writeSuccessReadMemListWithinWithdrawalsFrames sp before after frame
      base (48 * length items) (base + 48 * Z.of_nat index + 24)
      (length (observationWithdrawalAddress item)) HbeforeFrame HafterFrame
      HlowDisjoint HhighDisjoint ltac:(lia)
      ltac:(rewrite HaddressLength; lia)).
    exact HaddressRead.
Qed.

Print Assumptions writeSuccessReadMemListWithinWithdrawalsFrames.
Print Assumptions writeSuccessWithdrawalItemsAtWithdrawalsFrames.
