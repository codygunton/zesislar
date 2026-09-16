Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsPriceTailModel
  WriteSuccessOutputDescriptors WriteSuccessEncodeFragments
  WriteSuccessRepresentation WriteSuccessObservation WriteSuccessOutputSemantic.

Definition writeSuccessExactTransactionAfterGasEvents
    (sp : bv 64) (transaction : writeSuccessTransaction) (tail : spec) : spec :=
  let count := (4 + length (writeSuccessOptionalU64Descriptors sp
    (writeSuccessTransactionChainId transaction)) +
    length (writeSuccessOptionalU128Descriptors sp
      (writeSuccessTransactionGasPriorityFee transaction)))%nat in
  writeOutputPayloadsSpec (drop count (writeSuccessTransactionDescriptors sp transaction))
    (drop count (map writeSuccessPrivateBytes (writeSuccessTransactionFragments
      (writeSuccessTransactionObservationOfNative transaction)))) tail.

Lemma transactions_exact_gas_tail sp transaction tail :
  writeSuccessExactTransactionAfterPriceEvents sp transaction tail =
  let gas := writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64
      (bv_unsigned (writeSuccessTransactionGasLimit transaction))))
    (writeSuccessExactTransactionAfterGasEvents sp transaction tail) in
  match writeSuccessTransactionGasPriorityFee transaction with
  | None => writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
      (writeSuccessPrivateBytes (writeSuccessEncodeU8 0)) gas
  | Some fee => writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
      (writeSuccessPrivateBytes (writeSuccessEncodeU8 1))
      (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
        (writeSuccessPrivateBytes (writeSuccessEncodeU128 (writeSuccessPairValue fee))) gas)
  end.
Proof.
  destruct (writeSuccessTransactionChainId transaction) as [chain|] eqn:Hchain;
    destruct (writeSuccessTransactionGasPriorityFee transaction) as [fee|] eqn:Hfee;
    unfold writeSuccessExactTransactionAfterPriceEvents,
      writeSuccessExactTransactionAfterGasEvents,
      writeSuccessTransactionDescriptors, writeSuccessTransactionFragments,
      writeSuccessTransactionObservationOfNative, writeSuccessOptionalWordValue,
      writeSuccessOptionalPairValue;
    rewrite Hchain Hfee;
    cbn [writeSuccessOptionalU64Descriptors writeSuccessOptionalU128Descriptors
      writeSuccessOptionalFragments option_map map app tl drop length writeOutputPayloadsSpec];
    reflexivity.
Qed.
Print Assumptions transactions_exact_gas_tail.
