Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From Coq Require Import Lists.List.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsBlobTailModel
  WriteSuccessExactAccessListsPayloadLength WriteSuccessExactAuthorizationsModel
  WriteSuccessOutputDescriptors WriteSuccessEncodeFragments WriteSuccessRepresentation
  WriteSuccessObservation WriteSuccessOutputSemantic.

Definition writeSuccessExactTransactionAfterAuthorizationEvents
    (sp : bv 64) (transaction : writeSuccessTransaction) (tail : spec) : spec :=
  writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned (writeSuccessTransactionV transaction))))
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessPrivateBytes (writeSuccessEncodeU256 (writeSuccessWordsValue (writeSuccessTransactionR transaction))))
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
        (writeSuccessPrivateBytes (writeSuccessEncodeU256 (writeSuccessWordsValue (writeSuccessTransactionS transaction)))) tail)).

Definition writeSuccessExactTransactionAfterAuthorizationCountEvents
    (sp : bv 64) (transaction : writeSuccessTransaction) (tail : spec) : spec :=
  writeSuccessExactAuthorizationEvents sp (writeSuccessTransactionAuthorizations transaction)
    (writeSuccessExactTransactionAfterAuthorizationEvents sp transaction tail).

Lemma transactions_exact_authorization_count_tail sp transaction tail :
  writeSuccessExactTransactionAfterBlobEvents sp transaction tail =
  writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
    (writeSuccessPrivateBytes (writeSuccessEncodeU128
      (writeSuccessPairValue (writeSuccessTransactionMaxFeePerBlobGas transaction))))
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64
        (Z.of_nat (length (writeSuccessTransactionAuthorizations transaction)))))
      (writeSuccessExactTransactionAfterAuthorizationCountEvents sp transaction tail)).
Proof.
  have Hsingle (items : list (list Z)) : concat (map (fun item => [item]) items) = items.
  { induction items; cbn; [reflexivity | rewrite IHitems; reflexivity]. }
  have Hrepeat data size count : length (writeSuccessRepeatedDescriptors data size count) = count.
  { induction count; cbn; [reflexivity | rewrite IHcount; reflexivity]. }
  have Hauth count : length (writeSuccessAuthorizationsDescriptors sp count) = (6 * count)%nat.
  { induction count; cbn; [reflexivity | rewrite IHcount; lia]. }
  have Hfragments rows :
      length (concat (map writeSuccessAuthorizationFragments
        (map writeSuccessAuthorizationObservationOfBytes rows))) = (6 * length rows)%nat.
  { induction rows; cbn [List.map concat length]; first reflexivity.
    rewrite app_length IHrows. cbn [writeSuccessAuthorizationFragments length]. lia. }
  have Hdrop (count : nat) (items rest : list (bv 64 * bv 64))
      (Hlength : length items = count) : drop count (items ++ rest) = rest.
  { rewrite -Hlength drop_app_length. reflexivity. }
  have HdropPayload (items : list (list (bv 8))) rest :
      drop (length items) (map writeSuccessPrivateBytes (map writeSuccessPublicBytes items) ++ rest) = rest.
  { replace (length items) with (length (map writeSuccessPrivateBytes (map writeSuccessPublicBytes items)))
      by (rewrite !map_length; reflexivity).
    rewrite drop_app_length. reflexivity. }
  destruct (writeSuccessTransactionChainId transaction) as [chain|] eqn:Hchain;
    destruct (writeSuccessTransactionGasPriorityFee transaction) as [fee|] eqn:Hfee;
    destruct (writeSuccessTransactionTo transaction) as [address|] eqn:Haddress;
    unfold writeSuccessExactTransactionAfterBlobEvents,
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
  all: rewrite ?map_app ?map_length.
  all: rewrite (Hdrop _ (writeSuccessBlobHashesDescriptors sp _) _ ltac:(apply Hrepeat)).
  all: rewrite HdropPayload.
  all: cbn [List.map].
  all: rewrite ?map_app.
  all: unfold writeSuccessExactTransactionAfterAuthorizationCountEvents.
  all: rewrite authorization_exact_events_descriptors.
  all: cbn [writeOutputPayloadsSpec].
  all: rewrite writeOutputPayloadsSpec_app.
  all: unfold writeSuccessExactTransactionAfterAuthorizationEvents.
  all: try (rewrite !map_length Hauth Hfragments; reflexivity).
  all: rewrite (map_map writeSuccessAuthorizationObservationOfBytes
    writeSuccessAuthorizationFragments (writeSuccessTransactionAuthorizations transaction)).
  all: cbn [List.map writeOutputPayloadsSpec].
  all: try reflexivity.
Qed.
Print Assumptions transactions_exact_authorization_count_tail.
