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
Require Import ZesuSsz.Contracts.ParentHeaderSailItems.

Import ListNotations.
Open Scope Z_scope.

(* Owner: contract fact. For each KnownBug class, a decidable condition on
   the input bytes of decodeParentHeader under which the binary's result
   (candidateParentHeader) may differ from Sail's. The meaning
   ParentHeaderMeaningModuloKnownBugs always requires the exact candidate
   result; a trigger only excuses a disagreement with Sail. The set below
   is the one the user approved on 2026-11-20 (plan step 2.4, M2: the
   divergence table of lane 2.4m2, rows D1 to D11 widen, O1 to O4 narrow,
   O5 and O6 kept). The Sail-side tests (sailShortUintCanonical,
   sailSkipItems, the profile limits) are ParentHeaderSailItems.v. *)

(* Positions in parentHeaderFieldSchedule (0-based field numbers of the
   header list). *)
Notation parentHashField := (0%nat) (only parsing).
Notation stateRootField := (3%nat) (only parsing).
Notation gasLimitField := (9%nat) (only parsing).
Notation gasUsedField := (10%nat) (only parsing).
Notation timestampField := (11%nat) (only parsing).
Notation baseFeeField := (15%nat) (only parsing).
Notation blobGasField := (17%nat) (only parsing).
Notation excessBlobGasField := (18%nat) (only parsing).
(* nextUint64 and the inlined integer reads fold at most 8 payload bytes. *)
Notation foldedPayloadLimit := 8 (only parsing).

(* The reached field is at one of the listed schedule positions. *)
Definition reachedFieldAt (field : ParentHeaderReachedField)
    (indices : list nat) : bool :=
  existsb (Nat.eqb (reachedFieldIndex field)) indices.

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
   field 3 (state root), which the code skips and Sail decodes as a word
   (rlp_decode_word), and the item there is one Sail rejects for a word: a
   list, or a string longer than RLP_WORD_LENGTH_LIMIT. *)
Definition skippedFieldShapeb (bytes : list byte) : bool :=
  existsb (fun field =>
    reachedFieldAt field [parentHashField; stateRootField] &&
    match candidateDecodeItem (reachedFieldBytes field) with
    | candidateSuccess isList _ payloadLength =>
        isList || (sailWordLengthLimit <? payloadLength)
    | candidateError => false
    end) (parentHeaderWalkTrace bytes).

(* ParentHeaderBlobGasUnaligned: the candidate succeeds with blob gas used
   Some n, and Sail's blob test fails: n is not a multiple of the gas per
   blob, or its blob count n / 2^17 is above the schedule maximum. *)
Definition blobGasUnalignedb (bytes : list byte) : bool :=
  match candidateParentHeader bytes with
  | candidateHeaderSuccess header =>
      match parentBlobGas header with
      | Some value =>
          negb (value mod sailGasPerBlob =? 0) ||
          (sailBlobMax <? value / sailGasPerBlob)
      | None => false
      end
  | candidateHeaderError => false
  end.

(* RlpUintNonCanonical: the walk reaches field 15, 17 or 18 (the integer
   fields Sail decodes with rlp_item_uint_canonical), the code folds its
   item (a string of at most 8 bytes), and Sail's canonical test fails: a
   leading zero byte, or a header that is not the short canonical form.
   The guards use [if], not [&&], so that vm_compute (call by value) never
   builds Z.to_nat of a wrapped payload length. *)
Definition uintNonCanonicalb (bytes : list byte) : bool :=
  existsb (fun field =>
    if reachedFieldAt field [baseFeeField; blobGasField; excessBlobGasField] then
      match candidateDecodeItem (reachedFieldBytes field) with
      | candidateSuccess false headerLength payloadLength =>
          if payloadLength <=? foldedPayloadLimit then
            negb (sailShortUintCanonical (reachedFieldBytes field) false
                    headerLength payloadLength)
          else false
      | candidateSuccess true _ _ | candidateError => false
      end
    else false) (parentHeaderWalkTrace bytes).

(* ParentHeaderUintOver8: the walk reaches field 15 (base fee, the only
   integer field Sail decodes wider than 64 bits, as a 256-bit word) and its
   item is a canonical string of 9 to 32 bytes, which Sail accepts and the
   code rejects. *)
Definition uintOver8b (bytes : list byte) : bool :=
  existsb (fun field =>
    if reachedFieldAt field [baseFeeField] then
      match candidateDecodeItem (reachedFieldBytes field) with
      | candidateSuccess false headerLength payloadLength =>
          if (foldedPayloadLimit <? payloadLength) &&
             (payloadLength <=? sailWordLengthLimit) then
            sailShortUintCanonical (reachedFieldBytes field) false
              headerLength payloadLength
          else false
      | candidateSuccess true _ _ | candidateError => false
      end
    else false) (parentHeaderWalkTrace bytes).

(* ParentHeaderUndecodedFieldRejected: the walk reaches field 9, 10 or 11
   (gas limit, gas used, timestamp), whose item decodes without a length
   wrap and is a list or a string longer than 8 bytes: the code rejects it,
   Sail skips it. A missing field is ParentHeaderMissingRequiredField; an
   item that does not decode is rejected by both. *)
Definition undecodedFieldRejectedb (bytes : list byte) : bool :=
  existsb (fun field =>
    reachedFieldAt field [gasLimitField; gasUsedField; timestampField] &&
    negb (candidateWrapb (reachedFieldBytes field)) &&
    match candidateDecodeItem (reachedFieldBytes field) with
    | candidateSuccess isList _ payloadLength =>
        isList || (foldedPayloadLimit <? payloadLength)
    | candidateError => false
    end) (parentHeaderWalkTrace bytes).

(* ParentHeaderExcessBlobGasAboveLimit: the candidate succeeds with excess
   blob gas Some n above the profile's excess blob gas limit. *)
Definition excessBlobGasAboveLimitb (bytes : list byte) : bool :=
  match candidateParentHeader bytes with
  | candidateHeaderSuccess header =>
      match parentExcessBlobGas header with
      | Some value => sailExcessBlobGasLimit <? value
      | None => false
      end
  | candidateHeaderError => false
  end.

(* ParentHeaderTrailingItemMalformed: the walk passes field 18 and the rest
   of the outer payload is not a sequence of items rlp_decode_item accepts.
   The guards use [if] for the same reason as uintNonCanonicalb. *)
Definition trailingItemMalformedb (bytes : list byte) : bool :=
  match candidateDecodeItem bytes with
  | candidateSuccess true headerLength payloadLength =>
      if (0 <? payloadLength) &&
         (headerLength + payloadLength <=? Z.of_nat (List.length bytes)) then
        match parentHeaderWalkRest parentHeaderFieldSchedule
                (itemPayload bytes headerLength payloadLength) [] with
        | Some rest => negb (sailSkipItems (List.length rest) rest)
        | None => false
        end
      else false
  | candidateSuccess false _ _ | candidateError => false
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
  | ParentHeaderExcessBlobGasAboveLimit => excessBlobGasAboveLimitb bytes
  | ParentHeaderTrailingItemMalformed => trailingItemMalformedb bytes
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

(* Witnesses. Each triggers its own class; all but wrapWitness trigger no
   other. Byte lists are written as numbers 0..255; 80*n is n empty
   strings (0x80). *)
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
(* D9: d7 80*18 84 b2 59 3f 01, excess blob gas 2992193281. *)
Definition excessBlobGasAboveLimitWitness : list byte :=
  triggerWitnessBytes (215 :: repeat 128 18 ++ [132; 178; 89; 63; 1]).
(* D10: d4 80*19 b8, a long-string header with no length byte after
   field 18. *)
Definition trailingItemMalformedWitness : list byte :=
  triggerWitnessBytes (212 :: repeat 128 19 ++ [184]).

(* wrapWitness also triggers ParentHeaderSkippedFieldShape: its field 0 is
   a string longer than 32 bytes (row O5: both reject; kept). *)
Example wrapWitnessTriggers :
  parentHeaderTriggeredBugs wrapWitness =
    [RlpLongLengthWrap; ParentHeaderSkippedFieldShape].
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
Example excessBlobGasAboveLimitWitnessTriggersOnly :
  parentHeaderTriggeredBugs excessBlobGasAboveLimitWitness =
    [ParentHeaderExcessBlobGasAboveLimit].
Proof. vm_compute. reflexivity. Qed.
Example trailingItemMalformedWitnessTriggersOnly :
  parentHeaderTriggeredBugs trailingItemMalformedWitness =
    [ParentHeaderTrailingItemMalformed].
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

(* The rows of the approved divergence table (lane 2.4m2, DIVERGENCES.md).
   Rows D1 to D11: the candidate accepts, Sail rejects, and exactly one
   class fires. Rows O1 to O4: the candidate and Sail agree and no class
   fires. The controls agree with Sail and fire nothing. Sail's verdicts
   on the class witnesses are Evidence/ParentHeaderCandidateVectors.v. *)
(* D1: ed a1 01*33 80*11, parent hash a 33-byte string. *)
Example rowD1_parentHash33 :
  parentHeaderTriggeredBugs
    (triggerWitnessBytes ([237; 161] ++ repeat 1 33 ++ repeat 128 11)) =
    [ParentHeaderSkippedFieldShape].
Proof. vm_compute. reflexivity. Qed.
(* Control of D1: ec a0 01*32 80*11, a 32-byte parent hash. *)
Example rowD1_control_parentHash32 :
  parentHeaderTriggeredBugs
    (triggerWitnessBytes ([236; 160] ++ repeat 1 32 ++ repeat 128 11)) = [].
Proof. vm_compute. reflexivity. Qed.
(* D2: ed 80 80 80 a1 01*33 80*8, state root a 33-byte string. *)
Example rowD2_stateRoot33 :
  parentHeaderTriggeredBugs
    (triggerWitnessBytes ([237; 128; 128; 128; 161] ++ repeat 1 33 ++ repeat 128 8)) =
    [ParentHeaderSkippedFieldShape].
Proof. vm_compute. reflexivity. Qed.
(* D3: d1 80*15 81 05, base fee 05 in long form. *)
Example rowD3_baseFee8105 :
  parentHeaderTriggeredBugs (triggerWitnessBytes ([209] ++ repeat 128 15 ++ [129; 5])) =
    [RlpUintNonCanonical].
Proof. vm_compute. reflexivity. Qed.
(* D4: d1 80*15 b8 00, base fee the empty string in long form. *)
Example rowD4_baseFeeB800 :
  parentHeaderTriggeredBugs (triggerWitnessBytes ([209] ++ repeat 128 15 ++ [184; 0])) =
    [RlpUintNonCanonical].
Proof. vm_compute. reflexivity. Qed.
(* D5: d4 80*18 81 05, excess blob gas 05 in long form. *)
Example rowD5_excess8105 :
  parentHeaderTriggeredBugs (triggerWitnessBytes ([212] ++ repeat 128 18 ++ [129; 5])) =
    [RlpUintNonCanonical].
Proof. vm_compute. reflexivity. Qed.
(* D6: d6 80*17 b8 03 02 00 00, blob gas used with a long header. *)
Example rowD6_blobB803 :
  parentHeaderTriggeredBugs
    (triggerWitnessBytes ([214] ++ repeat 128 17 ++ [184; 3; 2; 0; 0])) =
    [RlpUintNonCanonical].
Proof. vm_compute. reflexivity. Qed.
(* D7: d5 80*17 83 2c 00 00, blob gas used 22 * 2^17. *)
Example rowD7_blobAboveMax :
  parentHeaderTriggeredBugs
    (triggerWitnessBytes ([213] ++ repeat 128 17 ++ [131; 44; 0; 0])) =
    [ParentHeaderBlobGasUnaligned].
Proof. vm_compute. reflexivity. Qed.
(* Control of D7: d5 80*17 83 2a 00 00, blob gas used 21 * 2^17. *)
Example rowD7_control_blobAtMax :
  parentHeaderTriggeredBugs
    (triggerWitnessBytes ([213] ++ repeat 128 17 ++ [131; 42; 0; 0])) = [].
Proof. vm_compute. reflexivity. Qed.
(* D8: da 80*17 88 02 00*7, blob gas used 2^57 (count 2^40). *)
Example rowD8_blobCount2p40 :
  parentHeaderTriggeredBugs
    (triggerWitnessBytes ([218] ++ repeat 128 17 ++ [136; 2] ++ repeat 0 7)) =
    [ParentHeaderBlobGasUnaligned].
Proof. vm_compute. reflexivity. Qed.
(* D9: the class witness excessBlobGasAboveLimitWitness. *)
Example rowD9_excessAboveLimit :
  parentHeaderTriggeredBugs excessBlobGasAboveLimitWitness =
    [ParentHeaderExcessBlobGasAboveLimit].
Proof. vm_compute. reflexivity. Qed.
(* Control of D9: d7 80*18 84 b2 59 3f 00, excess blob gas at the limit. *)
Example rowD9_control_excessAtLimit :
  parentHeaderTriggeredBugs
    (triggerWitnessBytes ([215] ++ repeat 128 18 ++ [132; 178; 89; 63; 0])) = [].
Proof. vm_compute. reflexivity. Qed.
(* D10: the class witness trailingItemMalformedWitness. *)
Example rowD10_extraTruncatedHeader :
  parentHeaderTriggeredBugs trailingItemMalformedWitness =
    [ParentHeaderTrailingItemMalformed].
Proof. vm_compute. reflexivity. Qed.
(* D11: d4 80*19 81, an item after field 18 that runs past the payload. *)
Example rowD11_extraPastPayload :
  parentHeaderTriggeredBugs (triggerWitnessBytes ([212] ++ repeat 128 19 ++ [129])) =
    [ParentHeaderTrailingItemMalformed].
Proof. vm_compute. reflexivity. Qed.
(* Control of D10 and D11: d4 80*19 c0, a well-formed item after field 18. *)
Example rowD11_control_extraWellFormed :
  parentHeaderTriggeredBugs (triggerWitnessBytes ([212] ++ repeat 128 19 ++ [192])) = [].
Proof. vm_compute. reflexivity. Qed.
(* O1: ce 80*9 82 00 01 80 80, gas limit with a leading zero (Sail does not
   decode field 9). *)
Example rowO1_gasLimitLeadingZero :
  parentHeaderTriggeredBugs
    (triggerWitnessBytes ([206] ++ repeat 128 9 ++ [130; 0; 1; 128; 128])) = [].
Proof. vm_compute. reflexivity. Qed.
(* O2: ca 80*9 81, the gas limit item runs past the payload (both
   reject). *)
Example rowO2_gasLimitPastPayload :
  parentHeaderTriggeredBugs (triggerWitnessBytes ([202] ++ repeat 128 9 ++ [129])) = [].
Proof. vm_compute. reflexivity. Qed.
(* O3: f1 80*15 a1 01*33, base fee a 33-byte string (both reject). *)
Example rowO3_baseFee33 :
  parentHeaderTriggeredBugs
    (triggerWitnessBytes ([241] ++ repeat 128 15 ++ [161] ++ repeat 1 33)) = [].
Proof. vm_compute. reflexivity. Qed.
(* O4: d9 80*15 89 00 01..08, a non-canonical 9-byte base fee (both
   reject). *)
Example rowO4_baseFee9LeadingZero :
  parentHeaderTriggeredBugs
    (triggerWitnessBytes ([217] ++ repeat 128 15 ++ [137; 0; 1; 2; 3; 4; 5; 6; 7; 8])) = [].
Proof. vm_compute. reflexivity. Qed.
(* Review question 7: db 80 bf ff*8 00*8 80*9. The wrapped field 1 changes
   the verdict; only RlpLongLengthWrap fires. *)
Example rowQ7_wrapChangesVerdict :
  parentHeaderTriggeredBugs
    (triggerWitnessBytes ([219; 128; 191] ++ repeat 255 8 ++ repeat 0 8 ++ repeat 128 9)) =
    [RlpLongLengthWrap].
Proof. vm_compute. reflexivity. Qed.
