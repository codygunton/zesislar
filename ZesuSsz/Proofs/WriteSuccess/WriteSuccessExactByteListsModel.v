Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessByteLists
  WriteSuccessExactByteListsSpec WriteSuccessRepresentation WriteSuccessEncodeFragments
  WriteSuccessOutputSemantic WriteSuccessOutputDescriptors WriteSuccessExactStorageKeysModel.
Lemma exact_byte_list_items_model sp items tail :
  Forall (fun item => bv_unsigned (byteListSize item) = Z.of_nat (length (byteListBytes item))) items ->
  writeOutputPayloadsSpec (byteListItemDescriptors sp items)
    (map writeSuccessPrivateBytes (concat (map writeSuccessBytesFragments
      (writeSuccessByteListsObservation items)))) tail =
  byteListItemPayloadEvents sp items tail.
Proof.
  induction items as [|item rest IH]; intros Hsizes; [reflexivity |].
  inversion Hsizes as [|item0 rest0 Hsize Hrest]; subst item0 rest0.
  cbn [writeSuccessByteListsObservation writeSuccessBytesFragments
    byteListItemDescriptors byteListItemPayloadEvents concat map writeOutputPayloadsSpec].
  rewrite map_app.
  cbn [writeSuccessBytesFragments map app writeOutputPayloadsSpec].
  rewrite writeSuccessPrivatePublicBytes.
  have Hlength : length (writeSuccessPublicBytes (byteListBytes item)) = length (byteListBytes item).
  { rewrite /writeSuccessPublicBytes map_length. reflexivity. }
  rewrite Hlength -Hsize (IH Hrest). reflexivity.
Qed.
Print Assumptions exact_byte_list_items_model.
Lemma exact_byte_lists_model sp items tail :
  Forall (fun item => bv_unsigned (byteListSize item) = Z.of_nat (length (byteListBytes item))) items ->
  writeOutputPayloadsSpec (writeSuccessByteListsDescriptors sp items)
    (map writeSuccessPrivateBytes (writeSuccessListFragments writeSuccessBytesFragments
      (writeSuccessByteListsObservation items))) tail =
  writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
    (writeSuccessPrivateBytes (WriteSuccessObservation.writeSuccessEncodeU64 (Z.of_nat (length items))))
    (byteListItemPayloadEvents (sp - BV 64 32)%bv items tail).
Proof.
  intros Hsizes.
  rewrite /writeSuccessByteListsDescriptors /writeSuccessListFragments
    /writeSuccessByteListsObservation map_length.
  cbn [map writeOutputPayloadsSpec].
  rewrite (exact_byte_list_items_model (sp - BV 64 32)%bv items tail Hsizes). reflexivity.
Qed.
Print Assumptions exact_byte_lists_model.
