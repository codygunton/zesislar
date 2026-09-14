Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessExactTailPayloads
 WriteSuccessExactTrace WriteSuccessExactByteListsModel WriteSuccessOutputSemantic
 WriteSuccessByteLists WriteSuccessOutputDescriptors WriteSuccessEncodeFragments
 WriteSuccessRepresentation WriteSuccessPostTransactionDescriptors WriteSuccessExactByteListsSpec.
Lemma exact_tail_raw_byte_lists_model sp decodedBytes values payload transactions
    rawTransactions withdrawalsBytes withdrawalsCount post tail :
  Forall (fun item => bv_unsigned (byteListSize item) = Z.of_nat (length (byteListBytes item))) rawTransactions ->
  let observation := writeSuccessExactObservation decodedBytes values payload transactions
    rawTransactions withdrawalsBytes withdrawalsCount post in
  writeOutputPayloadsSpec
    (writeSuccessByteListsDescriptors sp rawTransactions ++
      writeSuccessAfterTransactionsDescriptors sp withdrawalsCount post)
    (drop (length (writeSuccessMainDescriptors sp values transactions))
      (writeSuccessExactPayloads decodedBytes values payload transactions
        rawTransactions withdrawalsBytes withdrawalsCount post)) tail =
  writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
    (writeSuccessPrivateBytes (WriteSuccessObservation.writeSuccessEncodeU64 (Z.of_nat (length rawTransactions))))
    (byteListItemPayloadEvents (sp - BV 64 32)%bv rawTransactions
      (writeOutputPayloadsSpec (writeSuccessAfterTransactionsDescriptors sp withdrawalsCount post)
        (map writeSuccessPrivateBytes (writeSuccessWithdrawalListFragments observation ++
          writeSuccessPostFragments observation)) tail)).
Proof.
  intros Hsizes. cbn zeta.
  rewrite exact_tail_payload_suffix map_app.
  rewrite writeOutputPayloadsSpec_app.
  - change (writeSuccessRawTransactionFragments
      (writeSuccessExactObservation decodedBytes values payload transactions
        rawTransactions withdrawalsBytes withdrawalsCount post)) with
      (writeSuccessListFragments writeSuccessBytesFragments
        (writeSuccessByteListsObservation rawTransactions)).
    rewrite exact_byte_lists_model; [reflexivity | exact Hsizes].
  - rewrite map_length.
    change (length (writeSuccessByteListsDescriptors sp rawTransactions) =
      length (writeSuccessListFragments writeSuccessBytesFragments
        (writeSuccessByteListsObservation rawTransactions))).
    symmetry. apply writeSuccessNativeByteListsFragments_length.
Qed.
Print Assumptions exact_tail_raw_byte_lists_model.
