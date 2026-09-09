From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.

Definition writeSuccessRepresentationReadsEqual
    (ok : Z -> nat -> Prop) (before after : mem_map) : Prop :=
  forall address len,
    ok address len ->
    read_mem_list after address (N.of_nat len) =
      read_mem_list before address (N.of_nat len).

Lemma writeSuccessMemoryBytesOkReadsEqual ok before after address bytes :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessMemoryBytesOk ok before address bytes ->
  writeSuccessMemoryBytesOk ok after address bytes.
Proof.
  intros Hreads [Hread Hok]. split; last exact Hok.
  unfold writeSuccessMemoryBytes in Hread.
  change (read_mem_list after address (N.of_nat (length bytes)) =
    Some (map (Z_to_bv 8) bytes)).
  rewrite (Hreads address (length bytes) Hok). exact Hread.
Qed.

Lemma writeSuccessMemoryIntegerOkReadsEqual ok before after address width value :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessMemoryIntegerOk ok before address width value ->
  writeSuccessMemoryIntegerOk ok after address width value.
Proof.
  unfold writeSuccessMemoryIntegerOk.
  apply writeSuccessMemoryBytesOkReadsEqual.
Qed.

Lemma writeSuccessMemorySliceOkReadsEqual ok before after owner offset bytes :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessMemorySliceOk ok before owner offset bytes ->
  writeSuccessMemorySliceOk ok after owner offset bytes.
Proof.
  intros Hreads (pointer & Hrange & Hpointer & Hlength & Hbytes).
  exists pointer. split; first exact Hrange.
  split.
  - eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
  - split.
    + eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
    + eapply writeSuccessMemoryBytesOkReadsEqual; eassumption.
Qed.

Lemma writeSuccessMemoryOptionalU64OkReadsEqual
    ok before after owner offset value :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessMemoryOptionalU64Ok ok before owner offset value ->
  writeSuccessMemoryOptionalU64Ok ok after owner offset value.
Proof.
  intros Hreads Hvalue. destruct value; cbn in Hvalue |- *;
    eauto using writeSuccessMemoryIntegerOkReadsEqual.
  destruct Hvalue. split;
    eauto using writeSuccessMemoryIntegerOkReadsEqual.
Qed.

Lemma writeSuccessMemoryOptionalBytesOkReadsEqual
    ok before after owner offset value :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessMemoryOptionalBytesOk ok before owner offset value ->
  writeSuccessMemoryOptionalBytesOk ok after owner offset value.
Proof.
  intros Hreads Hvalue. destruct value as [bytes|]; cbn in Hvalue |- *.
  - destruct Hvalue as
      (pointer & Hrange & Hpointer & Hlength & Hbytes & Hnonnull).
    exists pointer. split; first exact Hrange.
    split.
    + eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
    + split.
      * eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
      * split.
        -- eapply writeSuccessMemoryBytesOkReadsEqual; eassumption.
        -- exact Hnonnull.
  - eauto using writeSuccessMemoryIntegerOkReadsEqual.
Qed.

Lemma writeSuccessMemoryFixedListOkReadsEqual
    ok before after owner offset stride items :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessMemoryFixedListOk ok before owner offset stride items ->
  writeSuccessMemoryFixedListOk ok after owner offset stride items.
Proof.
  intros Hreads (pointer & Hrange & Hpointer & Hlength & Hitems).
  exists pointer. split; first exact Hrange.
  split.
  - eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
  - split.
    + eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
    + intros index item Hnth. eapply writeSuccessMemoryBytesOkReadsEqual;
        eauto.
Qed.

Lemma writeSuccessMemoryByteListsOkReadsEqual
    ok before after owner offset items :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessMemoryByteListsOk ok before owner offset items ->
  writeSuccessMemoryByteListsOk ok after owner offset items.
Proof.
  intros Hreads (pointer & Hrange & Hpointer & Hlength & Hitems).
  exists pointer. split; first exact Hrange.
  split.
  - eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
  - split.
    + eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
    + intros index item Hnth. eapply writeSuccessMemorySliceOkReadsEqual;
        eauto.
Qed.

Print Assumptions writeSuccessMemoryBytesOkReadsEqual.
Print Assumptions writeSuccessMemoryIntegerOkReadsEqual.
Print Assumptions writeSuccessMemorySliceOkReadsEqual.
Print Assumptions writeSuccessMemoryOptionalU64OkReadsEqual.
Print Assumptions writeSuccessMemoryOptionalBytesOkReadsEqual.
Print Assumptions writeSuccessMemoryFixedListOkReadsEqual.
Print Assumptions writeSuccessMemoryByteListsOkReadsEqual.
