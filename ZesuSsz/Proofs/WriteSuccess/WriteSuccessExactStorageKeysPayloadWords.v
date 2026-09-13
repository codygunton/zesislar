Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactStorageKeysFixedBytes WriteSuccessExactStorageKeysEmit.

Lemma storage_keys_payload_word bytes index offset :
  (index + 32 <= length bytes)%nat -> (offset + 8 <= 32)%nat ->
  storageKeyWord (take 32 (drop index bytes)) offset = storageKeyEight bytes index offset.
Proof.
  intros Hbound Hoffset. unfold storageKeyWord.
  rewrite (take_drop_commute (take 32 (drop index bytes)) 8 offset) take_take.
  rewrite Nat.min_l; [|lia].
  rewrite -(take_drop_commute (drop index bytes) 8 offset) drop_drop.
  symmetry. apply storage_keys_eight_bytes. lia.
Qed.
Print Assumptions storage_keys_payload_word.
