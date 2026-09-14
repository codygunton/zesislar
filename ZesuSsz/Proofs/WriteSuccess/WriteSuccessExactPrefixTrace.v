Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessExactTrace WriteSuccessEncodeFragments WriteSuccessOutputDescriptors
  Interfaces WriteSuccessNativeContract WriteSuccessOutputSemantic.
Lemma write_success_exact_prefix_payload_bound sp decodedBytes values payload
    transactions rawTransactions withdrawalsBytes withdrawalsCount post :
  (length (writeSuccessMainDescriptors sp values transactions) <=
   length (writeSuccessExactPayloads decodedBytes values payload transactions
     rawTransactions withdrawalsBytes withdrawalsCount post))%nat.
Proof.
  pose proof (writeSuccessMainDescriptors_fragments_length sp decodedBytes values
    payload transactions rawTransactions withdrawalsBytes withdrawalsCount post) as Hmain.
  rewrite Hmain.
  unfold writeSuccessExactPayloads.
  rewrite map_length writeSuccessEncodeFragments_groups !app_length.
  lia.
Qed.
Print Assumptions write_success_exact_prefix_payload_bound.

Lemma write_success_exact_prefix_trace_split {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessNativeTailEvents witness =
  writeOutputPayloadsSpec
    (writeSuccessMainDescriptors (writeSuccessFrameSp witness) (writeSuccessValues witness) (writeSuccessTransactions witness))
    (take (length (writeSuccessMainDescriptors (writeSuccessFrameSp witness) (writeSuccessValues witness) (writeSuccessTransactions witness)))
      (writeSuccessExactPayloads (writeSuccessDecodedBytes witness) (writeSuccessValues witness) (writeSuccessPayload witness) (writeSuccessTransactions witness) (writeSuccessRawTransactions witness) (writeSuccessWithdrawalsBytes witness) (writeSuccessWithdrawalsCount witness) (writeSuccessPostData witness)))
    (writeSuccessExactTailEvents witness).
Proof.
  unfold writeSuccessNativeTailEvents, writeSuccessExactEvents,
    writeSuccessExactTailEvents, writeSuccessAllDescriptors.
  set (descriptors := writeSuccessMainDescriptors (writeSuccessFrameSp witness) (writeSuccessValues witness) (writeSuccessTransactions witness)).
  set (payloads := writeSuccessExactPayloads (writeSuccessDecodedBytes witness) (writeSuccessValues witness) (writeSuccessPayload witness) (writeSuccessTransactions witness) (writeSuccessRawTransactions witness) (writeSuccessWithdrawalsBytes witness) (writeSuccessWithdrawalsCount witness) (writeSuccessPostData witness)).
  have Hbound : (length descriptors <= length payloads)%nat.
  { apply write_success_exact_prefix_payload_bound. }
  rewrite -{1}(take_drop (length descriptors) payloads).
  rewrite writeOutputPayloadsSpec_app.
  - reflexivity.
  - rewrite length_take Nat.min_l; [reflexivity | exact Hbound].
Qed.
Print Assumptions write_success_exact_prefix_trace_split.
