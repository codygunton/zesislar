Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessAccessListsSpec WriteSuccessOutputDescriptors WriteSuccessEncodeFragments
  WriteSuccessRepresentation WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma access_lists_exact_payload_length sp entries :
  length (writeSuccessAccessListsDescriptors sp entries) =
  length (map writeSuccessPrivateBytes
    (concat (map writeSuccessAccessFragments (map writeSuccessAccessObservation entries)))).
Proof.
  have Hrepeat data size count :
    length (writeSuccessRepeatedDescriptors data size count) = count.
  { induction count; cbn; [reflexivity | rewrite IHcount; reflexivity]. }
  induction entries as [|entry entries IH]; first reflexivity.
  cbn [writeSuccessAccessListsDescriptors map concat].
  rewrite !map_app !app_length !map_length.
  unfold writeSuccessAccessFragments, writeSuccessListFragments.
  cbn. rewrite ?app_length ?map_length.
  unfold writeSuccessStorageKeysDescriptors. rewrite Hrepeat.
  unfold writeSuccessAccessObservation, writeSuccessFixedChunks.
  cbn. rewrite ?map_length ?length_seq.
  have Hsingle items : length (concat (map (fun item : list Z => [item]) items)) = length items.
  { induction items; cbn; [reflexivity | rewrite IHitems; reflexivity]. }
  rewrite ?Hsingle ?map_length ?length_seq.
  rewrite map_length in IH. rewrite IH. reflexivity.
Qed.
Print Assumptions access_lists_exact_payload_length.
