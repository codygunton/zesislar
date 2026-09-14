Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Contracts.Endpoints.
From Coq Require Import Lists.List.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesModel WriteSuccessOutputDescriptors
  WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma blob_hashes_exact_payload_model sp blobHashes tail :
  Forall (fun hash : ByteString => length hash = 32%nat) blobHashes ->
  writeOutputPayloadsSpec (writeSuccessBlobHashesDescriptors sp (length blobHashes))
    (map writeSuccessPrivateBytes blobHashes) tail =
  writeSuccessExactBlobHashesEvents sp 0 (length blobHashes)
    (concat (map writeSuccessPrivateBytes blobHashes)) tail.
Proof.
  intros Hvalid.
  have Hindexed : forall hashes,
      Forall (fun hash : ByteString => length hash = 32%nat) hashes ->
      forall processed bytes,
      drop (32 * processed) bytes = concat (map writeSuccessPrivateBytes hashes) ->
      writeOutputPayloadsSpec (writeSuccessBlobHashesDescriptors sp (length hashes))
        (map writeSuccessPrivateBytes hashes) tail =
      writeSuccessExactBlobHashesEvents sp processed (length hashes) bytes tail.
  { intros items Hitems. induction Hitems as [|hash hashes Hhash Hhashes IH];
      intros processed bytes Hdrop; first reflexivity.
    have HprivateLength : length (writeSuccessPrivateBytes hash) = 32%nat.
    { unfold writeSuccessPrivateBytes. rewrite map_length. exact Hhash. }
    cbn [map concat] in Hdrop.
    cbn [length writeSuccessBlobHashesDescriptors writeSuccessRepeatedDescriptors
      map writeOutputPayloadsSpec writeSuccessExactBlobHashesEvents].
    rewrite Hdrop take_app_le; last lia.
    rewrite take_ge; last lia.
    rewrite (IH (S processed) bytes); first reflexivity.
    replace (32 * S processed)%nat with (32 * processed + 32)%nat by lia.
    rewrite <- drop_drop, Hdrop, <- HprivateLength, drop_app_length.
    reflexivity. }
  apply Hindexed; [exact Hvalid | reflexivity].
Qed.
Print Assumptions blob_hashes_exact_payload_model.
