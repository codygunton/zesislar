From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.

Import ListNotations.

Definition bytes_of_u64s (values : list (bv 64)) : list (bv 8) :=
  values ≫= fun value => bv_to_little_endian 8 8 (bv_unsigned value).

Definition u64s_of_bytes (count : nat) (values : list (bv 8)) :
    list (bv 64) :=
  (fun bytes => Z_to_bv 64 (little_endian_to_bv 8 bytes))
    <$> reshape (replicate count 8%nat) values.

Lemma reshape_8_lengths count (values : list (bv 8)) :
  length values = (count * 8)%nat ->
  Forall (fun bytes => length bytes = 8%nat)
    (reshape (replicate count 8%nat) values).
Proof.
  revert values. induction count as [|count IH]; intros values Hlength.
  - cbn. constructor.
  - cbn. constructor.
    + rewrite length_take. lia.
    + apply IH. rewrite length_drop. lia.
Qed.

Lemma u64_bytes_roundtrip (values : list (bv 8)) :
  length values = 8%nat ->
  bv_to_little_endian 8 8
    (bv_unsigned (Z_to_bv 64 (little_endian_to_bv 8 values))) = values.
Proof.
  intros Hlength.
  have Hbound :
    (0 <= little_endian_to_bv 8 values < bv_modulus 64)%Z.
  { pose proof (little_endian_to_bv_bound 8 values).
    unfold bv_modulus. rewrite Hlength in H. cbn in H |-; lia. }
  rewrite Z_to_bv_small; [apply bv_to_little_endian_to_bv; lia | done].
Qed.

Lemma bytes_of_u64s_map_chunks (chunks : list (list (bv 8))) :
  Forall (fun bytes => length bytes = 8%nat) chunks ->
  bytes_of_u64s
    ((fun bytes => Z_to_bv 64 (little_endian_to_bv 8 bytes)) <$> chunks) =
  mjoin chunks.
Proof.
  intros Hchunks. induction Hchunks as [|chunk chunks Hlength Hchunks IH].
  - reflexivity.
  - unfold bytes_of_u64s in IH |- *. cbn.
    rewrite (u64_bytes_roundtrip chunk Hlength) IH. reflexivity.
Qed.

Lemma bytes_of_u64s_of_bytes count (values : list (bv 8)) :
  length values = (count * 8)%nat ->
  bytes_of_u64s (u64s_of_bytes count values) = values.
Proof.
  intros Hlength. rewrite /u64s_of_bytes.
  rewrite bytes_of_u64s_map_chunks; [|by apply reshape_8_lengths].
  apply join_reshape. rewrite sum_list_replicate. symmetry. exact Hlength.
Qed.
