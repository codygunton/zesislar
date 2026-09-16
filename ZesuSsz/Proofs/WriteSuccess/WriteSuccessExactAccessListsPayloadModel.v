Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Contracts.Endpoints.
From Coq Require Import Lists.List.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessAccessListsSpec WriteSuccessExactAccessListsSpec
  WriteSuccessOutputDescriptors WriteSuccessEncodeFragments
  WriteSuccessRepresentation WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma access_lists_exact_payload_model sp entries tail :
  writeOutputPayloadsSpec (writeSuccessAccessListsDescriptors sp entries)
    (map writeSuccessPrivateBytes (concat (map (fun entry =>
      writeSuccessAccessFragments (writeSuccessAccessObservation entry)) entries))) tail =
  writeSuccessExactAccessListsEvents sp entries tail.
Proof.
  have Hsingle (items : list ByteString) : concat (map (fun item => [item]) items) = items.
  { induction items; cbn; [reflexivity | rewrite IHitems; reflexivity]. }
  have Hrepeat (payloads : list (list (bv 8))) (rest : spec) :
      writeOutputPayloadsSpec (writeSuccessStorageKeysDescriptors sp (length payloads)) payloads rest =
        writeSuccessExactStorageKeyEvents sp payloads rest /\
      length (writeSuccessStorageKeysDescriptors sp (length payloads)) = length payloads.
  { induction payloads as [|payload payloads IH];
      cbn [length writeSuccessStorageKeysDescriptors writeSuccessRepeatedDescriptors
        writeOutputPayloadsSpec writeSuccessExactStorageKeyEvents] in *;
      [split; reflexivity | destruct IH as [Hevents Hlength]; split; [rewrite Hevents | rewrite Hlength]; reflexivity]. }
  revert tail. induction entries as [|entry entries IH]; intros tail; first reflexivity.
  have HkeysLength : length (observationStorageKeys (writeSuccessAccessObservation entry)) =
      writeSuccessAccessEntryStorageCount entry.
  { unfold writeSuccessAccessObservation, writeSuccessFixedChunks. cbn.
    rewrite map_length length_seq. reflexivity. }
  cbn [map concat writeSuccessAccessListsDescriptors writeSuccessExactAccessListsEvents].
  unfold writeSuccessAccessFragments, writeSuccessListFragments at 1.
  rewrite Hsingle HkeysLength !map_app.
  cbn [map app writeOutputPayloadsSpec].
  rewrite writeOutputPayloadsSpec_app.
  - rewrite IH.
    pose proof (Hrepeat (map writeSuccessPrivateBytes
      (observationStorageKeys (writeSuccessAccessObservation entry)))
      (writeSuccessExactAccessListsEvents sp entries tail)) as [Hevents Hlength].
    rewrite map_length HkeysLength in Hevents. rewrite Hevents.
    reflexivity.
  - pose proof (proj2 (Hrepeat (map writeSuccessPrivateBytes
      (observationStorageKeys (writeSuccessAccessObservation entry))) tail)) as Hlength.
    rewrite map_length HkeysLength in Hlength. rewrite map_length HkeysLength. exact Hlength.
Qed.
Print Assumptions access_lists_exact_payload_model.
