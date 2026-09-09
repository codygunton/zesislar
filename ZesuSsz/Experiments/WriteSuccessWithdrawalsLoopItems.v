From Coq Require Import Lia Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Lemma writeSuccessWithdrawalsCurrentRemainingItems {A} (items : list A)
    processed n (current : A) :
  nth_error items processed = Some current ->
  firstn (S n) (skipn processed items) =
    current :: firstn n (skipn (S processed) items).
Proof.
  revert items. induction processed as [|processed IH]; intros items Hcurrent.
  - destruct items as [|head items]; cbn in Hcurrent; first discriminate.
    injection Hcurrent as ->. reflexivity.
  - destruct items as [|head items]; cbn in Hcurrent; first discriminate.
    cbn. apply IH. exact Hcurrent.
Qed.

Lemma writeSuccessWithdrawalsRemainingItemsLength args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  length (skipn processed (observationWithdrawals
    (successDecoded WriteSuccessObservation args))) = remaining.
Proof.
  intros Hinv.
  have Htotal : total = length (observationWithdrawals
      (successDecoded WriteSuccessObservation args)) by
    (unfold Inv_15694 in Hinv; tauto).
  have Hremaining : total = (processed + remaining)%nat by
    (unfold Inv_15694 in Hinv; tauto).
  rewrite skipn_length. lia.
Qed.

Lemma writeSuccessWithdrawalsRemainingItemsExact args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  firstn remaining (skipn processed (observationWithdrawals
    (successDecoded WriteSuccessObservation args))) =
  skipn processed (observationWithdrawals
    (successDecoded WriteSuccessObservation args)).
Proof.
  intros Hinv. apply firstn_all2.
  rewrite (writeSuccessWithdrawalsRemainingItemsLength args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state Hinv).
  reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsCurrentRemainingItems.
Print Assumptions writeSuccessWithdrawalsRemainingItemsLength.
Print Assumptions writeSuccessWithdrawalsRemainingItemsExact.
