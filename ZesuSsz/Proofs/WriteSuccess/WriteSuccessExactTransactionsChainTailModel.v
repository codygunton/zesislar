Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsTypeTailModel
  WriteSuccessOutputDescriptors WriteSuccessEncodeFragments
  WriteSuccessRepresentation WriteSuccessObservation WriteSuccessOutputSemantic.

Definition writeSuccessExactTransactionAfterChainEvents
    (sp : bv 64) (transaction : writeSuccessTransaction) (tail : spec) : spec :=
  let count := (1 + length (writeSuccessOptionalU64Descriptors sp
    (writeSuccessTransactionChainId transaction)))%nat in
  writeOutputPayloadsSpec (drop count (writeSuccessTransactionDescriptors sp transaction))
    (drop count (map writeSuccessPrivateBytes (writeSuccessTransactionFragments
      (writeSuccessTransactionObservationOfNative transaction)))) tail.

Lemma transactions_exact_chain_tail sp transaction tail :
  writeSuccessExactTransactionAfterTypeEvents sp transaction tail =
  match writeSuccessTransactionChainId transaction with
  | None => writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
      (writeSuccessPrivateBytes (writeSuccessEncodeU8 0))
      (writeSuccessExactTransactionAfterChainEvents sp transaction tail)
  | Some chain => writeOutputEvents (sp - BV 64 25)%bv (BV 64 1)
      (writeSuccessPrivateBytes (writeSuccessEncodeU8 1))
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned chain)))
        (writeSuccessExactTransactionAfterChainEvents sp transaction tail))
  end.
Proof.
  destruct (writeSuccessTransactionChainId transaction) as [chain|] eqn:Hchain;
    unfold writeSuccessExactTransactionAfterTypeEvents,
      writeSuccessExactTransactionAfterChainEvents;
    unfold writeSuccessTransactionDescriptors, writeSuccessTransactionFragments,
      writeSuccessTransactionObservationOfNative, writeSuccessOptionalWordValue;
    rewrite Hchain;
    cbn [writeSuccessOptionalU64Descriptors writeSuccessOptionalFragments
      option_map map app tl drop length writeOutputPayloadsSpec]; reflexivity.
Qed.
Print Assumptions transactions_exact_chain_tail.
