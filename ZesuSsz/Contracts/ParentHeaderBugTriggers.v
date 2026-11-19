From Coq Require Import Bool List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ParentHeaderRequiredFields.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.

Import ListNotations.
Open Scope Z_scope.

(* Owner: contract fact. For each KnownBug class, a decidable condition on
   the input bytes of decodeParentHeader under which the binary's result
   (candidateParentHeader) may differ from Sail's. The meaning
   ParentHeaderMeaningModuloKnownBugs always requires the exact candidate
   result; a trigger only excuses a disagreement with Sail. These are the
   drafts of plan step 2.1-4; step 2.4 refines them with the user. *)

(* Positions in parentHeaderFieldSchedule (0-based field numbers of the
   header list). *)
Notation parentHashField := (0%nat) (only parsing).
Notation stateRootField := (3%nat) (only parsing).
Notation gasLimitField := (9%nat) (only parsing).
Notation timestampField := (11%nat) (only parsing).
Notation baseFeeField := (15%nat) (only parsing).
(* Sail's gas per blob (sizeof(gas_per_blob_value)). *)
Notation gasPerBlob := (2 ^ 17) (only parsing).

(* RlpLongLengthWrap: some nested call of the reached-slice walk
   (fieldSlices) decodes an item whose header and payload lengths add to
   2^64 or more. Boolean form of nestedWrapOccurs. *)
Definition nestedWrapOccursb (bytes : list byte) : bool :=
  match fieldSlices bytes with
  | Some slices =>
      existsb (fun call =>
        let '(pc, remaining) := call in
        negb (pc =? 0x800d5cf4) &&
        existsb (Z.eqb pc)
          (parentHeaderDecodeItemCallSites ++ parentHeaderNextUint64CallSites) &&
        match candidateDecodeItem remaining with
        | candidateSuccess _ headerLength payloadLength =>
            (0 <=? headerLength) && (0 <=? payloadLength) &&
            (word64Modulus <=? headerLength + payloadLength)
        | candidateError => false
        end) slices
  | None => false
  end.

Lemma nestedWrapOccursb_spec (bytes : list byte) :
  nestedWrapOccursb bytes = true <-> nestedWrapOccurs bytes.
Proof.
  unfold nestedWrapOccursb, nestedWrapOccurs, candidateCallInputAt.
  destruct (fieldSlices bytes) as [slices|] eqn:Hslices; split.
  - intros Hex. apply existsb_exists in Hex as [[pc remaining] [Hin Hcall]].
    cbv beta iota in Hcall.
    destruct (candidateDecodeItem remaining) as [|isList headerLength payloadLength]
      eqn:Hdecode; [rewrite andb_false_r in Hcall; discriminate|].
    apply andb_prop in Hcall as [Hcall Hwrap].
    apply andb_prop in Hcall as [Hpc Hsite].
    apply andb_prop in Hwrap as [Hwrap Hsum].
    apply andb_prop in Hwrap as [Hheader Hpayload].
    apply existsb_exists in Hsite as [site [Hsite Hsame]].
    apply Z.eqb_eq in Hsame. subst site.
    apply negb_true_iff, Z.eqb_neq in Hpc.
    apply Z.leb_le in Hheader, Hpayload, Hsum.
    exists pc, remaining, isList, headerLength, payloadLength.
    split; [exact Hpc|]. split; [exact Hsite|].
    split; [exists slices; split; [reflexivity|exact Hin]|].
    split; [exact Hdecode|].
    unfold binaryWrapCase. repeat split; assumption.
  - intros (pc & remaining & isList & headerLength & payloadLength & Hpc &
      Hsite & (other & Hother & Hin) & Hdecode & (Hheader & Hpayload & Hsum & _)).
    injection Hother as <-.
    apply existsb_exists. exists (pc, remaining). split; [exact Hin|].
    cbv beta iota. rewrite Hdecode.
    apply Z.eqb_neq in Hpc. rewrite Hpc.
    assert (Hsiteb : existsb (Z.eqb pc)
      (parentHeaderDecodeItemCallSites ++ parentHeaderNextUint64CallSites) = true).
    { apply existsb_exists. exists pc. split; [exact Hsite|apply Z.eqb_refl]. }
    rewrite Hsiteb.
    apply Z.leb_le in Hheader, Hpayload, Hsum. rewrite Hheader, Hpayload, Hsum.
    reflexivity.
  - discriminate.
  - intros (pc & remaining & isList & headerLength & payloadLength & _ &
      _ & (other & Hother & _) & _). discriminate.
Qed.

(* ParentHeaderMissingRequiredField: the existing required-field scan finds
   fewer than twelve fields. *)
Definition missingRequiredFieldb (bytes : list byte) : bool :=
  match parentHeaderRequiredScan bytes with
  | RequiredMissing => true
  | RequiredPresent _ | RequiredInvalid => false
  end.

(* ParentHeaderTrailingBytes: the outer item's header plus payload length is
   less than the input length. *)
Definition trailingBytesb (bytes : list byte) : bool :=
  match candidateDecodeItem bytes with
  | candidateSuccess _ headerLength payloadLength =>
      headerLength + payloadLength <? Z.of_nat (List.length bytes)
  | candidateError => false
  end.

(* ParentHeaderSkippedFieldShape: the walk reaches field 0 (parent hash) or
   field 3 (state root), which the code skips and Sail decodes as a word,
   and the item there is a list. *)
Definition skippedFieldShapeb (bytes : list byte) : bool :=
  existsb (fun field =>
    (Nat.eqb (reachedFieldIndex field) parentHashField ||
     Nat.eqb (reachedFieldIndex field) stateRootField) &&
    match candidateDecodeItem (reachedFieldBytes field) with
    | candidateSuccess isList _ _ => isList
    | candidateError => false
    end) (parentHeaderWalkTrace bytes).

(* ParentHeaderBlobGasUnaligned: the candidate succeeds with blob gas used
   Some n and n is not a multiple of 2^17. *)
Definition blobGasUnalignedb (bytes : list byte) : bool :=
  match candidateParentHeader bytes with
  | candidateHeaderSuccess header =>
      match parentBlobGas header with
      | Some value => negb (value mod gasPerBlob =? 0)
      | None => false
      end
  | candidateHeaderError => false
  end.

(* RlpUintNonCanonical: the walk reaches an integer field (9, 10, 11, 15,
   17 or 18) whose item the code folds (a string of at most 8 bytes) and the
   payload starts with a zero byte. *)
(* The guards use [if], not [&&], so that vm_compute (call by value) never
   builds Z.to_nat of a wrapped payload length. *)
Definition uintNonCanonicalb (bytes : list byte) : bool :=
  existsb (fun field =>
    if parentHeaderFieldIsInteger (reachedFieldKind field) then
      match candidateDecodeItem (reachedFieldBytes field) with
      | candidateSuccess false headerLength payloadLength =>
          if payloadLength <=? 8 then
            match firstn (Z.to_nat payloadLength)
                    (skipn (Z.to_nat headerLength) (reachedFieldBytes field)) with
            | first :: _ => bv_unsigned first =? 0
            | [] => false
            end
          else false
      | candidateSuccess true _ _ | candidateError => false
      end
    else false) (parentHeaderWalkTrace bytes).

(* ParentHeaderUintOver8: the walk reaches field 15 (base fee, the only
   integer field Sail decodes wider than 64 bits) and its item is a string
   with a payload longer than 8 bytes. *)
Definition uintOver8b (bytes : list byte) : bool :=
  existsb (fun field =>
    Nat.eqb (reachedFieldIndex field) baseFeeField &&
    match candidateDecodeItem (reachedFieldBytes field) with
    | candidateSuccess false _ payloadLength => 8 <? payloadLength
    | candidateSuccess true _ _ | candidateError => false
    end) (parentHeaderWalkTrace bytes).

(* ParentHeaderUndecodedFieldRejected: the candidate rejects the item
   present at field 9, 10 or 11 (gas limit, gas used, timestamp). A missing
   field is ParentHeaderMissingRequiredField, not this class. *)
Definition undecodedFieldRejectedb (bytes : list byte) : bool :=
  match parentHeaderWalkEnd bytes with
  | walkRejectField index =>
      Nat.leb gasLimitField index && Nat.leb index timestampField
  | walkRejectOuter | walkMissingField _ | walkAccept _ => false
  end.

Definition parentHeaderBugTrigger (bug : KnownBug) (bytes : list byte) : bool :=
  match bug with
  | RlpLongLengthWrap => nestedWrapOccursb bytes
  | ParentHeaderMissingRequiredField => missingRequiredFieldb bytes
  | ParentHeaderTrailingBytes => trailingBytesb bytes
  | ParentHeaderSkippedFieldShape => skippedFieldShapeb bytes
  | ParentHeaderBlobGasUnaligned => blobGasUnalignedb bytes
  | RlpUintNonCanonical => uintNonCanonicalb bytes
  | ParentHeaderUintOver8 => uintOver8b bytes
  | ParentHeaderUndecodedFieldRejected => undecodedFieldRejectedb bytes
  end.

(* The classes an input triggers, in knownBugs order. *)
Definition parentHeaderTriggeredBugs (bytes : list byte) : list KnownBug :=
  List.filter (fun bug => parentHeaderBugTrigger bug bytes) knownBugs.

Lemma parentHeaderTriggeredBugs_spec (bytes : list byte) (bug : KnownBug) :
  List.In bug (parentHeaderTriggeredBugs bytes) <->
  List.In bug knownBugs /\ parentHeaderBugTrigger bug bytes = true.
Proof. apply filter_In. Qed.

Lemma missingRequiredFieldb_spec (bytes : list byte) :
  missingRequiredFieldb bytes = true <-> parentHeaderMissingRequiredField bytes.
Proof.
  unfold missingRequiredFieldb, parentHeaderMissingRequiredField.
  destruct (parentHeaderRequiredScan bytes); split; congruence.
Qed.

(* Witnesses. Each triggers its own class and no other. Byte lists are
   written as numbers 0..255. *)
Definition triggerWitnessBytes (values : list Z) : list byte :=
  map (Z_to_bv 8) values.

(* c9 bf ff ff ff ff ff ff ff ff: field 0 claims 2^64 - 1 payload bytes. *)
Definition wrapWitness : list byte := fittingOuterHeader.
(* c0: an empty header list. *)
Definition missingFieldWitness : list byte := triggerWitnessBytes [192].
(* W3 of return-tail: cf 80*15 00, one byte after the outer list. *)
Definition trailingBytesWitness : list byte :=
  triggerWitnessBytes (207 :: repeat 128 15 ++ [0]).
(* W1: cf c0 80*14, parent hash an empty list. *)
Definition skippedFieldShapeWitness : list byte :=
  triggerWitnessBytes (207 :: 192 :: repeat 128 14).
(* W2: d2 80*15 07 80 05, blob gas used 5. *)
Definition blobGasUnalignedWitness : list byte :=
  triggerWitnessBytes (210 :: repeat 128 15 ++ [7; 128; 5]).
(* W6: d2 80*15 82 00 07, base fee 00 07. *)
Definition uintNonCanonicalWitness : list byte :=
  triggerWitnessBytes (210 :: repeat 128 15 ++ [130; 0; 7]).
(* d2 80*15 82 00 01, base fee 00 01. *)
Definition uintNonCanonicalWitness2 : list byte :=
  triggerWitnessBytes (210 :: repeat 128 15 ++ [130; 0; 1]).
(* d0 80*15 00, base fee the single byte 00 (zero is 80 in canonical RLP). *)
Definition uintNonCanonicalWitness3 : list byte :=
  triggerWitnessBytes (208 :: repeat 128 15 ++ [0]).
(* W4: d9 80*15 89 01..09, base fee a 9-byte string. *)
Definition uintOver8Witness : list byte :=
  triggerWitnessBytes (217 :: repeat 128 15 ++ [137; 1; 2; 3; 4; 5; 6; 7; 8; 9]).
(* W5: cf 80*9 c0 80*5, gas limit an empty list. *)
Definition undecodedFieldWitness : list byte :=
  triggerWitnessBytes (207 :: repeat 128 9 ++ [192] ++ repeat 128 5).

Example wrapWitnessTriggersOnly :
  parentHeaderTriggeredBugs wrapWitness = [RlpLongLengthWrap].
Proof. vm_compute. reflexivity. Qed.
Example missingFieldWitnessTriggersOnly :
  parentHeaderTriggeredBugs missingFieldWitness = [ParentHeaderMissingRequiredField].
Proof. vm_compute. reflexivity. Qed.
Example trailingBytesWitnessTriggersOnly :
  parentHeaderTriggeredBugs trailingBytesWitness = [ParentHeaderTrailingBytes].
Proof. vm_compute. reflexivity. Qed.
Example skippedFieldShapeWitnessTriggersOnly :
  parentHeaderTriggeredBugs skippedFieldShapeWitness =
    [ParentHeaderSkippedFieldShape].
Proof. vm_compute. reflexivity. Qed.
Example blobGasUnalignedWitnessTriggersOnly :
  parentHeaderTriggeredBugs blobGasUnalignedWitness =
    [ParentHeaderBlobGasUnaligned].
Proof. vm_compute. reflexivity. Qed.
Example uintNonCanonicalWitnessTriggersOnly :
  parentHeaderTriggeredBugs uintNonCanonicalWitness = [RlpUintNonCanonical].
Proof. vm_compute. reflexivity. Qed.
Example uintNonCanonicalWitness2TriggersOnly :
  parentHeaderTriggeredBugs uintNonCanonicalWitness2 = [RlpUintNonCanonical].
Proof. vm_compute. reflexivity. Qed.
Example uintNonCanonicalWitness3TriggersOnly :
  parentHeaderTriggeredBugs uintNonCanonicalWitness3 = [RlpUintNonCanonical].
Proof. vm_compute. reflexivity. Qed.
Example uintOver8WitnessTriggersOnly :
  parentHeaderTriggeredBugs uintOver8Witness = [ParentHeaderUintOver8].
Proof. vm_compute. reflexivity. Qed.
Example undecodedFieldWitnessTriggersOnly :
  parentHeaderTriggeredBugs undecodedFieldWitness =
    [ParentHeaderUndecodedFieldRejected].
Proof. vm_compute. reflexivity. Qed.

(* The wrap witness is the existing nestedWrapOccurs example. *)
Lemma wrapWitnessNestedWrap : nestedWrapOccurs wrapWitness.
Proof. exact hostileNestedWrapOccurs. Qed.

(* W2 and W4, the two reviewer anchors of plan step 2.1. *)
Example blobGasUnalignedWitnessCandidate :
  candidateParentHeader blobGasUnalignedWitness =
    candidateHeaderSuccess {| parentGasLimit := 0; parentGasUsed := 0;
      parentTimestamp := 0; parentBaseFee := Some 7; parentBlobGas := Some 5;
      parentExcessBlobGas := None |}.
Proof. vm_compute. reflexivity. Qed.
Example uintOver8WitnessCandidate :
  candidateParentHeader uintOver8Witness = candidateHeaderError.
Proof. vm_compute. reflexivity. Qed.
