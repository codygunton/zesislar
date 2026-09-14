Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTrace.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessOutputDescriptors WriteSuccessEncodeFragments WriteSuccessOutputSemantic.
Lemma exact_tail_payload_suffix sp decodedBytes values payload transactions
    rawTransactions withdrawalsBytes withdrawalsCount post :
  let observation := writeSuccessExactObservation decodedBytes values payload transactions
    rawTransactions withdrawalsBytes withdrawalsCount post in
  drop (length (writeSuccessMainDescriptors sp values transactions))
    (writeSuccessExactPayloads decodedBytes values payload transactions
      rawTransactions withdrawalsBytes withdrawalsCount post) =
  map writeSuccessPrivateBytes
    (writeSuccessRawTransactionFragments observation ++
     writeSuccessWithdrawalListFragments observation ++ writeSuccessPostFragments observation).
Proof.
  cbn zeta.
  pose proof (writeSuccessMainDescriptors_fragments_length sp decodedBytes values
    payload transactions rawTransactions withdrawalsBytes withdrawalsCount post) as Hlength.
  rewrite Hlength /writeSuccessExactPayloads writeSuccessEncodeFragments_groups !map_app.
  rewrite -(map_length writeSuccessPrivateBytes
    (writeSuccessMainFragments (writeSuccessExactObservation decodedBytes values
      payload transactions rawTransactions withdrawalsBytes withdrawalsCount post))).
  rewrite drop_app_length. reflexivity.
Qed.
Print Assumptions exact_tail_payload_suffix.
