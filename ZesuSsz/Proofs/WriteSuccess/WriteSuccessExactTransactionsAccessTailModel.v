Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From Coq Require Import Lists.List.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsDataTailModel
  WriteSuccessExactAccessListsPayloadModel WriteSuccessExactAccessListsSpec
  WriteSuccessExactAccessListsPayloadLength
  WriteSuccessOutputDescriptors WriteSuccessEncodeFragments
  WriteSuccessRepresentation WriteSuccessObservation WriteSuccessOutputSemantic.

Definition writeSuccessExactTransactionAfterAccessEvents
    (sp : bv 64) (transaction : writeSuccessTransaction) (tail : spec) : spec :=
  let count := (8 + length (writeSuccessOptionalU64Descriptors sp
    (writeSuccessTransactionChainId transaction)) +
    length (writeSuccessOptionalU128Descriptors sp
      (writeSuccessTransactionGasPriorityFee transaction)) +
    length (writeSuccessOptionalAddressDescriptors sp
      (writeSuccessTransactionTo transaction)) +
    length (writeSuccessAccessListsDescriptors sp
      (writeSuccessTransactionAccessEntries transaction)))%nat in
  writeOutputPayloadsSpec (drop count (writeSuccessTransactionDescriptors sp transaction))
    (drop count (map writeSuccessPrivateBytes (writeSuccessTransactionFragments
      (writeSuccessTransactionObservationOfNative transaction)))) tail.

Lemma transactions_exact_access_tail sp transaction tail :
  writeSuccessExactTransactionAfterDataEvents sp transaction tail =
  writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64
      (Z.of_nat (length (writeSuccessTransactionAccessEntries transaction)))))
    (writeSuccessExactAccessListsEvents sp (writeSuccessTransactionAccessEntries transaction)
      (writeSuccessExactTransactionAfterAccessEvents sp transaction tail)).
Proof.
  destruct (writeSuccessTransactionChainId transaction) as [chain|] eqn:Hchain;
    destruct (writeSuccessTransactionGasPriorityFee transaction) as [fee|] eqn:Hfee;
    destruct (writeSuccessTransactionTo transaction) as [address|] eqn:Haddress;
    unfold writeSuccessExactTransactionAfterDataEvents,
      writeSuccessExactTransactionAfterAccessEvents,
      writeSuccessTransactionDescriptors, writeSuccessTransactionFragments,
      writeSuccessTransactionObservationOfNative, writeSuccessOptionalWordValue,
      writeSuccessOptionalPairValue;
    rewrite Hchain Hfee Haddress;
    cbn [writeSuccessOptionalU64Descriptors writeSuccessOptionalU128Descriptors
      writeSuccessOptionalAddressDescriptors writeSuccessOptionalFragments
      writeSuccessOptionalBytesFragments writeSuccessBytesFragments
      writeSuccessListFragments option_map map app tl drop length writeOutputPayloadsSpec].
  all: cbn.
  all: rewrite !map_app.
  all: rewrite !map_length.
  all: rewrite writeOutputPayloadsSpec_app;
    last apply access_lists_exact_payload_length.
  all: rewrite !map_map access_lists_exact_payload_model.
  all: rewrite drop_app_length.
  all: rewrite (access_lists_exact_payload_length sp
    (writeSuccessTransactionAccessEntries transaction)).
  all: rewrite (map_map writeSuccessAccessObservation writeSuccessAccessFragments
    (writeSuccessTransactionAccessEntries transaction)) drop_app_length.
  all: reflexivity.
Qed.
Print Assumptions transactions_exact_access_tail.
