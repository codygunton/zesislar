Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From Coq Require Import Lists.List.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsBlobCountTailModel
  WriteSuccessExactAccessListsPayloadLength WriteSuccessExactBlobHashesPayloadModel
  WriteSuccessExactStorageKeysModel
  WriteSuccessExactBlobHashesModel WriteSuccessOutputDescriptors WriteSuccessEncodeFragments
  WriteSuccessRepresentation WriteSuccessObservation WriteSuccessOutputSemantic.

Definition writeSuccessExactTransactionAfterBlobEvents
    (sp : bv 64) (transaction : writeSuccessTransaction) (tail : spec) : spec :=
  let count := (8 + length (writeSuccessOptionalU64Descriptors sp
    (writeSuccessTransactionChainId transaction)) +
    length (writeSuccessOptionalU128Descriptors sp
      (writeSuccessTransactionGasPriorityFee transaction)) +
    length (writeSuccessOptionalAddressDescriptors sp
      (writeSuccessTransactionTo transaction)) +
    length (writeSuccessAccessListsDescriptors sp
      (writeSuccessTransactionAccessEntries transaction)))%nat in
  let hashes := length (writeSuccessTransactionBlobHashes transaction) in
  writeOutputPayloadsSpec
    (drop hashes (tl (drop count (writeSuccessTransactionDescriptors sp transaction))))
    (drop hashes (tl (drop count (map writeSuccessPrivateBytes (writeSuccessTransactionFragments
      (writeSuccessTransactionObservationOfNative transaction)))))) tail.

Lemma transactions_exact_blob_tail sp transaction tail :
  Forall (fun hash => length hash = 32%nat) (writeSuccessTransactionBlobHashes transaction) ->
  writeSuccessExactTransactionAfterBlobCountEvents sp transaction tail =
  writeSuccessExactBlobHashesEvents sp 0 (length (writeSuccessTransactionBlobHashes transaction))
    (concat (writeSuccessTransactionBlobHashes transaction))
    (writeSuccessExactTransactionAfterBlobEvents sp transaction tail).
Proof.
  intros Hhashes.
  have Hsingle (items : list (list Z)) : concat (map (fun item => [item]) items) = items.
  { induction items; cbn; [reflexivity | rewrite IHitems; reflexivity]. }
  have Hrepeat data size count : length (writeSuccessRepeatedDescriptors data size count) = count.
  { induction count; cbn; [reflexivity | rewrite IHcount; reflexivity]. }
  have Hdrop (count : nat) (items rest : list (bv 64 * bv 64))
      (Hlength : length items = count) : drop count (items ++ rest) = rest.
  { rewrite -Hlength drop_app_length. reflexivity. }
  have Hpublic : Forall (fun hash => length hash = 32%nat)
      (map writeSuccessPublicBytes (writeSuccessTransactionBlobHashes transaction)).
  { apply Forall_map. eapply Forall_impl; [|exact Hhashes].
    intros hash Hlength. unfold writeSuccessPublicBytes. rewrite map_length. exact Hlength. }
  have Hblob := blob_hashes_exact_payload_model sp
    (map writeSuccessPublicBytes (writeSuccessTransactionBlobHashes transaction))
    (writeSuccessExactTransactionAfterBlobEvents sp transaction tail) Hpublic.
  rewrite !map_length !map_map in Hblob.
  have Hprivate (items : list (list (bv 8))) :
      map (fun item => writeSuccessPrivateBytes (writeSuccessPublicBytes item)) items = items.
  { induction items; cbn [List.map]; [reflexivity | rewrite writeSuccessPrivatePublicBytes IHitems; reflexivity]. }
  rewrite Hprivate in Hblob.
  rewrite -Hblob.
  destruct (writeSuccessTransactionChainId transaction) as [chain|] eqn:Hchain;
    destruct (writeSuccessTransactionGasPriorityFee transaction) as [fee|] eqn:Hfee;
    destruct (writeSuccessTransactionTo transaction) as [address|] eqn:Haddress;
    unfold writeSuccessExactTransactionAfterBlobCountEvents,
      writeSuccessExactTransactionAfterBlobEvents,
      writeSuccessTransactionDescriptors, writeSuccessTransactionFragments,
      writeSuccessTransactionObservationOfNative, writeSuccessOptionalWordValue,
      writeSuccessOptionalPairValue;
    rewrite Hchain Hfee Haddress;
    cbn [writeSuccessOptionalU64Descriptors writeSuccessOptionalU128Descriptors
      writeSuccessOptionalAddressDescriptors writeSuccessOptionalFragments
      writeSuccessOptionalBytesFragments writeSuccessBytesFragments
      writeSuccessListFragments option_map map app tl drop length writeOutputPayloadsSpec].
  all: cbn.
  all: rewrite !map_app !map_length !drop_app_length.
  all: rewrite (access_lists_exact_payload_length sp
    (writeSuccessTransactionAccessEntries transaction)).
  all: rewrite (map_map writeSuccessAccessObservation writeSuccessAccessFragments
    (writeSuccessTransactionAccessEntries transaction)) !drop_app_length.
  all: cbn [tl].
  all: rewrite Hsingle ?map_app ?map_length.
  all: cbn [List.map tl].
  all: rewrite ?map_app ?map_map ?Hprivate.
  all: rewrite writeOutputPayloadsSpec_app; last (unfold writeSuccessBlobHashesDescriptors; rewrite Hrepeat ?map_length; reflexivity).
  all: rewrite (Hdrop _ (writeSuccessBlobHashesDescriptors sp _) _ ltac:(apply Hrepeat)).
  all: rewrite !drop_app_length.
  all: reflexivity.
Qed.
Print Assumptions transactions_exact_blob_tail.
