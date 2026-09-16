Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsRecipientTailModel
  WriteSuccessOutputDescriptors WriteSuccessEncodeFragments
  WriteSuccessRepresentation WriteSuccessObservation WriteSuccessOutputSemantic.

Definition writeSuccessExactTransactionAfterDataEvents
    (sp : bv 64) (transaction : writeSuccessTransaction) (tail : spec) : spec :=
  let count := (7 + length (writeSuccessOptionalU64Descriptors sp
    (writeSuccessTransactionChainId transaction)) +
    length (writeSuccessOptionalU128Descriptors sp
      (writeSuccessTransactionGasPriorityFee transaction)) +
    length (writeSuccessOptionalAddressDescriptors sp
      (writeSuccessTransactionTo transaction)))%nat in
  writeOutputPayloadsSpec (drop count (writeSuccessTransactionDescriptors sp transaction))
    (drop count (map writeSuccessPrivateBytes (writeSuccessTransactionFragments
      (writeSuccessTransactionObservationOfNative transaction)))) tail.

Lemma transactions_exact_data_tail sp transaction tail :
  writeSuccessExactTransactionAfterRecipientEvents sp transaction tail =
  writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
    (writeSuccessPrivateBytes (writeSuccessEncodeU256
      (writeSuccessWordsValue (writeSuccessTransactionValue transaction))))
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64
        (Z.of_nat (length (writeSuccessPublicBytes (writeSuccessTransactionData transaction))))))
      (writeOutputEvents (writeSuccessTransactionDataPointer transaction)
        (Z_to_bv 64 (Z.of_nat (length (writeSuccessTransactionData transaction))))
        (writeSuccessPrivateBytes (writeSuccessPublicBytes (writeSuccessTransactionData transaction)))
        (writeSuccessExactTransactionAfterDataEvents sp transaction tail))).
Proof.
  destruct (writeSuccessTransactionChainId transaction) as [chain|] eqn:Hchain;
    destruct (writeSuccessTransactionGasPriorityFee transaction) as [fee|] eqn:Hfee;
    destruct (writeSuccessTransactionTo transaction) as [address|] eqn:Haddress;
    unfold writeSuccessExactTransactionAfterRecipientEvents,
      writeSuccessExactTransactionAfterDataEvents,
      writeSuccessTransactionDescriptors, writeSuccessTransactionFragments,
      writeSuccessTransactionObservationOfNative, writeSuccessOptionalWordValue,
      writeSuccessOptionalPairValue;
    rewrite Hchain Hfee Haddress;
    cbn [writeSuccessOptionalU64Descriptors writeSuccessOptionalU128Descriptors
      writeSuccessOptionalAddressDescriptors writeSuccessOptionalFragments
      writeSuccessOptionalBytesFragments writeSuccessBytesFragments
      option_map map app tl drop length writeOutputPayloadsSpec]; reflexivity.
Qed.
Print Assumptions transactions_exact_data_tail.
