Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessExactTrace
 WriteSuccessExactHeaderSpec WriteSuccessOutputDescriptors WriteSuccessExactStorageKeysModel
 WriteSuccessOutputSemantic WriteSuccessRepresentation.
Lemma header_payload_trim offset width bytes :
  (offset + width <= 592)%nat ->
  writeSuccessHeaderPayload offset width bytes = take width (drop offset bytes).
Proof.
  intros Hbound. rewrite /writeSuccessHeaderPayload !take_drop_commute take_take.
  rewrite Nat.min_l; [reflexivity | lia].
Qed.
Lemma exact_header_model sp decodedBytes values payload transactions rawTransactions
    withdrawalsBytes withdrawalsCount post tail :
  writeOutputPayloadsSpec (writeSuccessHeaderDescriptors sp)
    (map writeSuccessPrivateBytes (take 7 (writeSuccessMainFragments
      (writeSuccessExactObservation decodedBytes values payload transactions
        rawTransactions withdrawalsBytes withdrawalsCount post)))) tail =
  writeSuccessExactHeaderEvents sp (take 720 decodedBytes) tail.
Proof.
  rewrite /writeSuccessMainFragments /writeSuccessExactObservation /writeSuccessNativeObservation.
  cbn -[writeSuccessPrivateBytes writeSuccessBytesAt writeOutputEvents].
  rewrite /writeSuccessBytesAt !writeSuccessPrivatePublicBytes.
  rewrite /writeSuccessHeaderDescriptors /writeOutputPayloadsSpec
    /writeSuccessExactHeaderEvents /writeSuccessExactHeaderEventsAfterTag
    /writeSuccessExactHeaderEventsAfter1184 /writeSuccessExactHeaderEventsAfter1216
    /writeSuccessExactHeaderEventsAfter1236 /writeSuccessExactHeaderEventsAfter1268
    /writeSuccessExactHeaderEventsAfter1300.
  rewrite !header_payload_trim; try lia. reflexivity.
Qed.
Print Assumptions exact_header_model.
