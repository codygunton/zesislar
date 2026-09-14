Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsChainTailModel
  WriteSuccessOutputDescriptors WriteSuccessEncodeFragments
  WriteSuccessRepresentation WriteSuccessObservation WriteSuccessOutputSemantic.

Definition writeSuccessExactTransactionAfterPriceEvents
    (sp : bv 64) (transaction : writeSuccessTransaction) (tail : spec) : spec :=
  let count := (3 + length (writeSuccessOptionalU64Descriptors sp
    (writeSuccessTransactionChainId transaction)))%nat in
  writeOutputPayloadsSpec (drop count (writeSuccessTransactionDescriptors sp transaction))
    (drop count (map writeSuccessPrivateBytes (writeSuccessTransactionFragments
      (writeSuccessTransactionObservationOfNative transaction)))) tail.

Lemma transactions_exact_price_tail sp transaction tail :
  writeSuccessExactTransactionAfterChainEvents sp transaction tail =
  writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64
      (bv_unsigned (writeSuccessTransactionNonce transaction))))
    (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessPrivateBytes (writeSuccessEncodeU128
        (writeSuccessPairValue (writeSuccessTransactionGasPrice transaction))))
      (writeSuccessExactTransactionAfterPriceEvents sp transaction tail)).
Proof.
  destruct (writeSuccessTransactionChainId transaction) as [chain|] eqn:Hchain;
    unfold writeSuccessExactTransactionAfterChainEvents,
      writeSuccessExactTransactionAfterPriceEvents,
      writeSuccessTransactionDescriptors, writeSuccessTransactionFragments,
      writeSuccessTransactionObservationOfNative, writeSuccessOptionalWordValue;
    rewrite Hchain;
    cbn [writeSuccessOptionalU64Descriptors writeSuccessOptionalFragments
      option_map map app tl drop length writeOutputPayloadsSpec]; reflexivity.
Qed.
Print Assumptions transactions_exact_price_tail.
