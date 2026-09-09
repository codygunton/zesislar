From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsIterationRemainingRange args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  (0 < Z.of_nat remaining < 2 ^ 64)%Z.
Proof.
  intros Hinv.
  have HtotalLength : total = length (observationWithdrawals
      (successDecoded WriteSuccessObservation args)) by
    (unfold Inv_15694 in Hinv; tauto).
  have Hremaining : total = (processed + remaining)%nat by
    (unfold Inv_15694 in Hinv; tauto).
  have Hnth : nth_error (observationWithdrawals
      (successDecoded WriteSuccessObservation args)) processed =
      Some withdrawal by (unfold Inv_15694 in Hinv; tauto).
  have Hprocessed : (processed < total)%nat.
  { rewrite HtotalLength. apply (proj1 (nth_error_Some _ _)). congruence. }
  destruct remaining as [|remaining]; first lia.
  have Hall : allBytes = prefix ++ current ++ suffix by
    (unfold Inv_15694 in Hinv; tauto).
  have Hprefix : length prefix = (48 * processed)%nat by
    (unfold Inv_15694 in Hinv; tauto).
  have Hcurrent : length current = 48%nat by
    (unfold Inv_15694 in Hinv; tauto).
  have Hsuffix : length suffix = (48 * remaining)%nat by
    (unfold Inv_15694 in Hinv; cbn in Hinv; tauto).
  have HbaseLower : (0x20000000 <= base)%Z by
    (unfold Inv_15694 in Hinv; tauto).
  have HbaseUpper : (base + Z.of_nat (length allBytes) < 0x40000000)%Z by
    (unfold Inv_15694 in Hinv; tauto).
  have HallLength : length allBytes = (48 * total)%nat.
  { rewrite Hall !app_length Hprefix Hcurrent Hsuffix Hremaining. lia. }
  rewrite HallLength Nat2Z.inj_mul in HbaseUpper. cbn in HbaseUpper.
  have HremainingZ := f_equal Z.of_nat Hremaining.
  rewrite Nat2Z.inj_add in HremainingZ. lia.
Qed.

Print Assumptions writeSuccessWithdrawalsIterationRemainingRange.
