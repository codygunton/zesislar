Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.

Lemma writeSuccessMemoryBytesOkForget ok memory address bytes :
  writeSuccessMemoryBytesOk ok memory address bytes ->
  writeSuccessMemoryBytes memory address bytes.
Proof. unfold writeSuccessMemoryBytesOk. tauto. Qed.

Lemma writeSuccessMemoryIntegerOkForget ok memory address width value :
  writeSuccessMemoryIntegerOk ok memory address width value ->
  writeSuccessMemoryInteger memory address width value.
Proof. apply writeSuccessMemoryBytesOkForget. Qed.

Lemma writeSuccessMemorySliceOkForget ok memory owner offset bytes :
  writeSuccessMemorySliceOk ok memory owner offset bytes ->
  writeSuccessMemorySlice memory owner offset bytes.
Proof.
  intros (pointer & Hrange & Hpointer & Hlength & Hbytes).
  exists pointer. split; first exact Hrange.
  split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hpointer).
  split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hlength).
  exact (writeSuccessMemoryBytesOkForget _ _ _ _ Hbytes).
Qed.

Lemma writeSuccessMemoryOptionalU64OkForget ok memory owner offset value :
  writeSuccessMemoryOptionalU64Ok ok memory owner offset value ->
  writeSuccessMemoryOptionalU64 memory owner offset value.
Proof.
  destruct value as [value|]; cbn; intro H.
  - destruct H as [Hvalue Htag]. split;
      apply writeSuccessMemoryIntegerOkForget with (ok := ok); assumption.
  - apply writeSuccessMemoryIntegerOkForget with (ok := ok). exact H.
Qed.

Lemma writeSuccessMemoryOptionalBytesOkForget ok memory owner offset value :
  writeSuccessMemoryOptionalBytesOk ok memory owner offset value ->
  writeSuccessMemoryOptionalBytes memory owner offset value.
Proof.
  destruct value as [bytes|]; cbn; intro H.
  - destruct H as (pointer & Hrange & Hpointer & Hlength & Hbytes & Hnonzero).
    exists pointer. split; first exact Hrange.
    split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hpointer).
    split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hlength).
    split; first exact (writeSuccessMemoryBytesOkForget _ _ _ _ Hbytes).
    exact Hnonzero.
  - apply writeSuccessMemoryIntegerOkForget with (ok := ok). exact H.
Qed.

Lemma writeSuccessMemoryFixedListOkForget ok memory owner offset stride items :
  writeSuccessMemoryFixedListOk ok memory owner offset stride items ->
  writeSuccessMemoryFixedList memory owner offset stride items.
Proof.
  intros (pointer & Hrange & Hpointer & Hlength & Hitems).
  exists pointer. split; first exact Hrange.
  split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hpointer).
  split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hlength).
  intros index item Hnth. apply writeSuccessMemoryBytesOkForget with (ok := ok).
  exact (Hitems index item Hnth).
Qed.

Lemma writeSuccessMemoryByteListsOkForget ok memory owner offset items :
  writeSuccessMemoryByteListsOk ok memory owner offset items ->
  writeSuccessMemoryByteLists memory owner offset items.
Proof.
  intros (pointer & Hrange & Hpointer & Hlength & Hitems).
  exists pointer. split; first exact Hrange.
  split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hpointer).
  split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hlength).
  intros index item Hnth. apply writeSuccessMemorySliceOkForget with (ok := ok).
  exact (Hitems index item Hnth).
Qed.

Print Assumptions writeSuccessMemoryByteListsOkForget.
