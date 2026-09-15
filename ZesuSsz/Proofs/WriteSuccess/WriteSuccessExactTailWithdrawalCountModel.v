Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncodeFragments.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTrace.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawCallSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.

Definition exactTailAfterWithdrawalCountEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  let sp := writeSuccessFrameSp witness in
  let observation := writeSuccessExactObservation
    (writeSuccessDecodedBytes witness) (writeSuccessValues witness)
    (writeSuccessPayload witness) (writeSuccessTransactions witness)
    (writeSuccessRawTransactions witness) (writeSuccessWithdrawalsBytes witness)
    (writeSuccessWithdrawalsCount witness) (writeSuccessPostData witness) in
  writeOutputPayloadsSpec
    (writeSuccessWithdrawalsItemDescriptors sp
       (writeSuccessWithdrawalsCount witness) ++
     writeSuccessPost156e8Descriptors sp (writeSuccessPostData witness))
    (map writeSuccessPrivateBytes
       (concat (map writeSuccessWithdrawalFragments
          (observationWithdrawals observation))) ++
     map writeSuccessPrivateBytes (writeSuccessPostFragments observation))
    (writeSuccessTraceTail witness).

Lemma exact_observation_withdrawals_length decodedBytes values payload
    transactions rawTransactions withdrawalsBytes withdrawalsCount post :
  length (observationWithdrawals
    (writeSuccessExactObservation decodedBytes values payload transactions
      rawTransactions withdrawalsBytes withdrawalsCount post)) =
  withdrawalsCount.
Proof.
  cbn [writeSuccessExactObservation writeSuccessNativeObservation].
  rewrite !map_length seq_length. reflexivity.
Qed.
Print Assumptions exact_observation_withdrawals_length.

Lemma exact_tail_after_raw_count {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  exactTailAfterRawEvents witness =
  writeOutputEvents (writeSuccessFrameSp witness - BV 64 16)%bv (BV 64 8)
    (writeSuccessPrivateBytes
      (writeSuccessEncodeU64 (Z.of_nat (writeSuccessWithdrawalsCount witness))))
    (exactTailAfterWithdrawalCountEvents witness).
Proof.
  unfold exactTailAfterRawEvents, exactTailAfterWithdrawalCountEvents.
  cbn zeta.
  unfold writeSuccessAfterTransactionsDescriptors,
    writeSuccessWithdrawalsDescriptors, writeSuccessWithdrawalListFragments,
    writeSuccessListFragments.
  rewrite map_app.
  rewrite exact_observation_withdrawals_length.
  cbn [writeOutputPayloadsSpec].
  reflexivity.
Qed.
Print Assumptions exact_tail_after_raw_count.

Lemma exact_tail_withdrawal_count_word {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessWitnessWellFormed args witness ->
  bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 12) =
    Z.of_nat (writeSuccessWithdrawalsCount witness).
Proof.
  intros Hwf. unfold writeSuccessWitnessWellFormed in Hwf.
  destruct Hwf as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
     _ & Hword & Hlength & Hlower & Hupper & _ & _ & _).
  rewrite Hword. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small. split; first lia.
  rewrite Hlength in Hupper. rewrite Nat2Z.inj_mul in Hupper.
  cbn in Hupper. change (Z.of_nat (writeSuccessWithdrawalsCount witness) < 2 ^ 64)%Z.
  zesu_normalize_machine_map. lia.
Qed.
Print Assumptions exact_tail_withdrawal_count_word.
