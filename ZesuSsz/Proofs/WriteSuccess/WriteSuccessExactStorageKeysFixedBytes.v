Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysPairHandoff.

Lemma storage_keys_fixed_bytes bytes index offset count :
  (index + offset + count <= length bytes)%nat ->
  take count (drop (index + offset)%nat bytes) =
    (storageKeyByte bytes index <$> seq offset count).
Proof.
  intros Hbound. apply list_eq. intros position.
  destruct (lt_dec position count) as [Hlt | Hge].
  - rewrite lookup_take; [|lia].
    rewrite lookup_drop list_lookup_fmap lookup_seq_lt; [|lia].
    simpl. unfold storageKeyByte.
    replace (index + (offset + position))%nat with (index + offset + position)%nat by lia.
    destruct (bytes !! (index + offset + position)%nat) eqn:Hlookup; simpl; [done|].
    apply lookup_ge_None in Hlookup. lia.
  - rewrite lookup_take_ge; [|lia].
    rewrite list_lookup_fmap lookup_seq_ge; [done|lia].
Qed.
Print Assumptions storage_keys_fixed_bytes.

Definition storageKeyEight (bytes : list (bv 8)) (index offset : nat) : bv 64 :=
  Z_to_bv 64 (little_endian_to_bv 8 (storageKeyByte bytes index <$> seq offset 8)).

Lemma storage_keys_eight_bytes bytes index offset :
  (index + offset + 8 <= length bytes)%nat ->
  storageKeyEight bytes index offset =
    Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (index + offset)%nat bytes))).
Proof.
  intros Hbound. unfold storageKeyEight.
  rewrite -(storage_keys_fixed_bytes bytes index offset 8 Hbound). reflexivity.
Qed.
Print Assumptions storage_keys_eight_bytes.
