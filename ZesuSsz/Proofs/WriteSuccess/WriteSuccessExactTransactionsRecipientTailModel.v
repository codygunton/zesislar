Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsGasTailModel
  WriteSuccessOutputDescriptors WriteSuccessEncodeFragments
  WriteSuccessRepresentation WriteSuccessObservation WriteSuccessOutputSemantic.

Definition writeSuccessExactTransactionAfterRecipientEvents
    (sp : bv 64) (transaction : writeSuccessTransaction) (tail : spec) : spec :=
  let count := (4 + length (writeSuccessOptionalU64Descriptors sp
    (writeSuccessTransactionChainId transaction)) +
    length (writeSuccessOptionalU128Descriptors sp
      (writeSuccessTransactionGasPriorityFee transaction)) +
    length (writeSuccessOptionalAddressDescriptors sp
      (writeSuccessTransactionTo transaction)))%nat in
  writeOutputPayloadsSpec (drop count (writeSuccessTransactionDescriptors sp transaction))
    (drop count (map writeSuccessPrivateBytes (writeSuccessTransactionFragments
      (writeSuccessTransactionObservationOfNative transaction)))) tail.

Lemma transactions_exact_recipient_tail sp transaction tail :
  writeSuccessExactTransactionAfterGasEvents sp transaction tail =
  match writeSuccessTransactionTo transaction with
  | None => writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
      (writeSuccessPrivateBytes (writeSuccessEncodeU8 0))
      (writeSuccessExactTransactionAfterRecipientEvents sp transaction tail)
  | Some address => writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
      (writeSuccessPrivateBytes (writeSuccessEncodeU8 1))
      (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 20)
        (writeSuccessPrivateBytes (writeSuccessPublicBytes address))
        (writeSuccessExactTransactionAfterRecipientEvents sp transaction tail))
  end.
Proof.
  destruct (writeSuccessTransactionChainId transaction) as [chain|] eqn:Hchain;
    destruct (writeSuccessTransactionGasPriorityFee transaction) as [fee|] eqn:Hfee;
    destruct (writeSuccessTransactionTo transaction) as [address|] eqn:Haddress;
    unfold writeSuccessExactTransactionAfterGasEvents,
      writeSuccessExactTransactionAfterRecipientEvents,
      writeSuccessTransactionDescriptors, writeSuccessTransactionFragments,
      writeSuccessTransactionObservationOfNative, writeSuccessOptionalWordValue,
      writeSuccessOptionalPairValue;
    rewrite Hchain Hfee Haddress;
    cbn [writeSuccessOptionalU64Descriptors writeSuccessOptionalU128Descriptors
      writeSuccessOptionalAddressDescriptors writeSuccessOptionalFragments
      writeSuccessOptionalBytesFragments option_map map app tl drop length writeOutputPayloadsSpec];
    reflexivity.
Qed.
Print Assumptions transactions_exact_recipient_tail.
