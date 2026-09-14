Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessExactTrace
 WriteSuccessExactHeaderModel WriteSuccessExactValueModel WriteSuccessExactHeaderSpec
 WriteSuccessExactValueSpec WriteSuccessExactTransactionsSpec WriteSuccessOutputDescriptors
 WriteSuccessOutputSemantic WriteSuccessRepresentation WriteSuccessValueBlock
 WriteSuccessEncodeFragments WriteSuccessObservation WriteSuccessNativeContract
 WriteSuccessExactPrefixWitnessFacts WriteSuccessExactPrefixTrace WriteSuccessExactPrefixPayloads
 WriteSuccessExactTransactionsLiveSpec Interfaces.
Lemma exact_prefix_model sp decodedBytes values payload transactions rawTransactions
    withdrawalsBytes withdrawalsCount post tail
    (Hpayload : bv_unsigned (writeSuccessValueWord values 5) = Z.of_nat (length payload))
    (Hcount : bv_unsigned (writeSuccessValueWord values 8) = Z.of_nat (length transactions))
    (Hvalues : bytes_of_u64s values = take 592 (take 720 decodedBytes)) :
  writeOutputPayloadsSpec (writeSuccessMainDescriptors sp values transactions)
    (map writeSuccessPrivateBytes (writeSuccessMainFragments
      (writeSuccessExactObservation decodedBytes values payload transactions
        rawTransactions withdrawalsBytes withdrawalsCount post))) tail =
  writeSuccessExactHeaderEvents sp (take 720 decodedBytes)
    (writeSuccessExactValueEvents sp values payload
      (writeSuccessExactTransactionsEvents sp transactions tail)).
Proof.
  set (fragments := writeSuccessMainFragments (writeSuccessExactObservation decodedBytes
    values payload transactions rawTransactions withdrawalsBytes withdrawalsCount post)).
  have Hheader : length (writeSuccessHeaderDescriptors sp) = length (map writeSuccessPrivateBytes (take 7 fragments)).
  { rewrite map_length. unfold fragments, writeSuccessHeaderDescriptors, writeSuccessMainFragments. cbn. reflexivity. }
  have Hvalue : length (writeSuccessValueDescriptors sp values) = length (map writeSuccessPrivateBytes (take 9 (drop 7 fragments))).
  { rewrite map_length. unfold fragments, writeSuccessValueDescriptors, writeSuccessMainFragments,
      writeSuccessBytesFragments, writeSuccessListFragments. cbn. reflexivity. }
  rewrite /writeSuccessMainDescriptors -{1}(take_drop 16 fragments)
    -(take_take_drop fragments 7 9) !map_app -app_assoc.
  rewrite !writeOutputPayloadsSpec_app; [|exact Hvalue|exact Hheader].
  unfold fragments. rewrite exact_header_model.
  rewrite exact_value_model; [|exact Hpayload|exact Hcount|exact Hvalues].
  rewrite /writeSuccessExactTransactionsEvents /writeSuccessExactTransactionsPayloads
    /writeSuccessMainFragments /writeSuccessBytesFragments /writeSuccessListFragments
    /writeSuccessExactObservation /writeSuccessNativeObservation.
  cbn -[writeSuccessPrivateBytes writeSuccessTransactionFragments]. reflexivity.
Qed.
Print Assumptions exact_prefix_model.

Lemma write_success_exact_entry_trace {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (Hwf : writeSuccessWitnessWellFormed args witness)
    (Hfacts : transactionLoopSourceFacts (writeSuccessFrameSp witness)
      (writeSuccessTransactionBase witness) (writeSuccessTransactions witness) []
      (writeSuccessTransactions witness) (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)) :
  writeSuccessNativeTailEvents witness =
  writeSuccessExactHeaderEvents (writeSuccessFrameSp witness) (writeSuccessSourceBytes witness)
    (writeSuccessExactValueEvents (writeSuccessFrameSp witness) (writeSuccessValues witness)
      (writeSuccessPayload witness)
      (writeSuccessExactTransactionsEvents (writeSuccessFrameSp witness)
        (writeSuccessTransactions witness) (writeSuccessExactTailEvents witness))).
Proof.
  have [Hpayload [Hcount Hvalues]] := exact_prefix_witness_facts args witness Hwf Hfacts.
  rewrite write_success_exact_prefix_trace_split exact_main_payload_prefix.
  rewrite exact_prefix_model; [|exact Hpayload|exact Hcount|exact Hvalues].
  have Hsource : writeSuccessSourceBytes witness = take 720 (writeSuccessDecodedBytes witness).
  { unfold writeSuccessWitnessWellFormed in Hwf. tauto. }
  rewrite -Hsource. reflexivity.
Qed.
Print Assumptions write_success_exact_entry_trace.
