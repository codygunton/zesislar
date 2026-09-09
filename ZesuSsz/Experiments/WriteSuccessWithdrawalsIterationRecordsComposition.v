From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsLogAppend.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Import ListNotations.

Lemma writeSuccessWithdrawalIterationRecordsCompose sp withdrawal
    indexRecords validatorRecords addressRecords amountRecords :
  writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalIndex withdrawal)) indexRecords ->
  writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalValidatorIndex withdrawal)) validatorRecords ->
  writeSuccessOutputRecords (sp + BV 64 1768)%bv (BV 64 20)
    (writeSuccessWithdrawalAddressBytes withdrawal) addressRecords ->
  writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalAmount withdrawal)) amountRecords ->
  writeSuccessWithdrawalIterationRecords sp withdrawal
    (indexRecords ++ validatorRecords ++ addressRecords ++ amountRecords).
Proof.
  intros [HindexEvents HindexPayload] [HvalidatorEvents HvalidatorPayload]
    [HaddressEvents HaddressPayload] [HamountEvents HamountPayload].
  unfold writeSuccessWithdrawalIterationRecords.
  split.
  - rewrite !map_app HindexEvents HvalidatorEvents HaddressEvents
      HamountEvents.
    unfold writeSuccessWithdrawalDescriptors,
      writeOutputDescriptorsEvents. reflexivity.
  - have HaddressAmount := writeSuccessWithdrawalsRecordedPayloads_app
      addressRecords amountRecords
      [writeSuccessWithdrawalAddressBytes withdrawal]
      [writeSuccessWithdrawalIntegerBytes
        (observationWithdrawalAmount withdrawal)]
      HaddressPayload HamountPayload.
    have HvalidatorTail := writeSuccessWithdrawalsRecordedPayloads_app
      validatorRecords (addressRecords ++ amountRecords)
      [writeSuccessWithdrawalIntegerBytes
        (observationWithdrawalValidatorIndex withdrawal)]
      ([writeSuccessWithdrawalAddressBytes withdrawal] ++
       [writeSuccessWithdrawalIntegerBytes
         (observationWithdrawalAmount withdrawal)])
      HvalidatorPayload HaddressAmount.
    have Hall := writeSuccessWithdrawalsRecordedPayloads_app
      indexRecords
      (validatorRecords ++ addressRecords ++ amountRecords)
      [writeSuccessWithdrawalIntegerBytes
        (observationWithdrawalIndex withdrawal)]
      ([writeSuccessWithdrawalIntegerBytes
          (observationWithdrawalValidatorIndex withdrawal)] ++
       [writeSuccessWithdrawalAddressBytes withdrawal] ++
       [writeSuccessWithdrawalIntegerBytes
         (observationWithdrawalAmount withdrawal)])
      HindexPayload HvalidatorTail.
    unfold writeSuccessWithdrawalFragments. exact Hall.
Qed.

Print Assumptions writeSuccessWithdrawalIterationRecordsCompose.
