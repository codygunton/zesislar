Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Contracts.IslarisMemory.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessExactTrace
 WriteSuccessExactValueSpec WriteSuccessOutputDescriptors WriteSuccessExactStorageKeysModel
 WriteSuccessOutputSemantic WriteSuccessRepresentation WriteSuccessValueBlock
 WriteSuccessEncodeFragments WriteSuccessObservation WriteSuccess.
Lemma exact_value_word_take69 values index :
  (index < 69)%nat -> writeSuccessExactValueWord values index = writeSuccessValueWord values index.
Proof. intros Hindex. rewrite /writeSuccessExactValueWord /writeSuccessValueWord lookup_take; auto. Qed.
Lemma exact_value_model sp decodedBytes values payload transactions rawTransactions
    withdrawalsBytes withdrawalsCount post tail
    (Hpayload : bv_unsigned (writeSuccessValueWord values 5) = Z.of_nat (length payload))
    (Hcount : bv_unsigned (writeSuccessValueWord values 8) = Z.of_nat (length transactions))
    (Hvalues : bytes_of_u64s values = take 592 (take 720 decodedBytes)) :
  writeOutputPayloadsSpec (writeSuccessValueDescriptors sp values)
    (map writeSuccessPrivateBytes (take 9 (drop 7 (writeSuccessMainFragments
      (writeSuccessExactObservation decodedBytes values payload transactions
        rawTransactions withdrawalsBytes withdrawalsCount post))))) tail =
  writeSuccessExactValueEvents sp values payload tail.
Proof.
  rewrite /writeSuccessMainFragments /writeSuccessExactObservation /writeSuccessNativeObservation
    /writeSuccessBytesFragments /writeSuccessListFragments.
  cbn -[writeSuccessPrivateBytes writeSuccessBytesAt writeOutputEvents writeSuccessEncodeU64
    writeSuccessPublicBytes writeSuccessValueWord].
  rewrite /writeSuccessBytesAt !writeSuccessPrivatePublicBytes /writeSuccessPublicBytes map_length.
  rewrite /writeSuccessValueDescriptors /writeOutputPayloadsSpec
    /writeSuccessExactValueEvents /writeSuccessExactValueEventsAfter0
    /writeSuccessExactValueEventsAfter1 /writeSuccessExactValueEventsAfter2
    /writeSuccessExactValueEventsAfterInts /writeSuccessExactValueEventsAfterExtra
    /writeSuccessExactValueIntEvent /writeSuccessValueBlockHash.
  rewrite !exact_value_word_take69; try lia.
  rewrite Hpayload Hcount Hvalues !take_drop_commute !take_take.
  cbn -[writeOutputEvents writeSuccessPrivateBytes writeSuccessEncodeU64].
  rewrite map_length. reflexivity.
Qed.
Print Assumptions exact_value_model.
