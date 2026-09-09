Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.

Lemma writeSuccessMemoryBytesOkTrue memory address bytes :
  writeSuccessMemoryBytesOk (fun _ _ => True) memory address bytes <->
  writeSuccessMemoryBytes memory address bytes.
Proof. unfold writeSuccessMemoryBytesOk. tauto. Qed.

Lemma writeSuccessMemoryIntegerOkTrue memory address width value :
  writeSuccessMemoryIntegerOk (fun _ _ => True) memory address width value <->
  writeSuccessMemoryInteger memory address width value.
Proof.
  unfold writeSuccessMemoryIntegerOk, writeSuccessMemoryInteger.
  apply writeSuccessMemoryBytesOkTrue.
Qed.

Lemma writeSuccessMemorySliceOkTrue memory owner offset bytes :
  writeSuccessMemorySliceOk (fun _ _ => True) memory owner offset bytes <->
  writeSuccessMemorySlice memory owner offset bytes.
Proof.
  unfold writeSuccessMemorySliceOk, writeSuccessMemorySlice.
  setoid_rewrite writeSuccessMemoryIntegerOkTrue.
  setoid_rewrite writeSuccessMemoryBytesOkTrue.
  reflexivity.
Qed.

Lemma writeSuccessMemoryOptionalU64OkTrue memory owner offset value :
  writeSuccessMemoryOptionalU64Ok (fun _ _ => True) memory owner offset value <->
  writeSuccessMemoryOptionalU64 memory owner offset value.
Proof.
  destruct value; unfold writeSuccessMemoryOptionalU64Ok,
    writeSuccessMemoryOptionalU64;
    setoid_rewrite writeSuccessMemoryIntegerOkTrue; reflexivity.
Qed.

Lemma writeSuccessMemoryOptionalBytesOkTrue memory owner offset value :
  writeSuccessMemoryOptionalBytesOk (fun _ _ => True) memory owner offset value <->
  writeSuccessMemoryOptionalBytes memory owner offset value.
Proof.
  destruct value; unfold writeSuccessMemoryOptionalBytesOk,
    writeSuccessMemoryOptionalBytes;
    setoid_rewrite writeSuccessMemoryIntegerOkTrue;
    try setoid_rewrite writeSuccessMemoryBytesOkTrue; reflexivity.
Qed.

Lemma writeSuccessMemoryFixedListOkTrue memory owner offset stride items :
  writeSuccessMemoryFixedListOk (fun _ _ => True)
      memory owner offset stride items <->
  writeSuccessMemoryFixedList memory owner offset stride items.
Proof.
  unfold writeSuccessMemoryFixedListOk, writeSuccessMemoryFixedList.
  setoid_rewrite writeSuccessMemoryIntegerOkTrue.
  setoid_rewrite writeSuccessMemoryBytesOkTrue.
  reflexivity.
Qed.

Lemma writeSuccessMemoryByteListsOkTrue memory owner offset items :
  writeSuccessMemoryByteListsOk (fun _ _ => True)
      memory owner offset items <->
  writeSuccessMemoryByteLists memory owner offset items.
Proof.
  unfold writeSuccessMemoryByteListsOk, writeSuccessMemoryByteLists.
  setoid_rewrite writeSuccessMemoryIntegerOkTrue.
  setoid_rewrite writeSuccessMemorySliceOkTrue.
  reflexivity.
Qed.

Print Assumptions writeSuccessMemoryByteListsOkTrue.
