From Coq Require Import List ZArith String Lia.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord SailStdpp.Values.
Require Import EvmSail.evm_decoder_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Compliance.RlpInputBounds.

Import ListNotations.
Open Scope Z_scope.

(* This value projection covers all fields in PLAN_STOCK_LADDER 5.4.
   The supplied public key, sender, and signing hash are separate source
   obligations. Sail's authorization recovery is outside this boundary. *)

Definition sliceContents (backing : list byte) (slice : StatelessInputSlice)
    : list byte :=
  match slice with
  | existT len (existT off _) =>
      firstn (Z.to_nat len) (skipn (Z.to_nat off) backing)
  end.

Definition sliceIsBacked (backing : list byte) (slice : StatelessInputSlice)
    : Prop :=
  match slice with
  | existT len (existT off _) =>
      validInputSlice backing off len = true
  end.

Definition inputContents (backing : list byte)
    (slice : TransactionInputSlice) : list byte :=
  match slice with
  | existT len (existT off _) =>
      firstn (Z.to_nat len) (skipn (Z.to_nat off) backing)
  end.

Definition inputIsBacked (backing : list byte)
    (slice : TransactionInputSlice) : Prop :=
  match slice with
  | existT len (existT off _) =>
      validInputSlice backing off len = true
  end.

(* The encoded source views point to list contents, without the outer list
   prefix. This grammar makes each retained content byte and item boundary
   explicit. The long-form length bytes are minimal and big-endian. *)
Inductive RlpTree : Type :=
| RlpString (contents : list byte)
| RlpList (items : list RlpTree).

Definition minimalLengthBytes (lengthBytes : list byte) (payloadLength : nat)
    : Prop :=
  (1 <= List.length lengthBytes <= 8)%nat /\
  match lengthBytes with
  | [] => False
  | first :: _ => bv_unsigned first <> 0
  end /\
  bigEndian lengthBytes = Z.of_nat payloadLength.

Inductive CanonicalRlp : RlpTree -> list byte -> Prop :=
| rlpLiteral (b : byte) :
    bv_unsigned b < 128 ->
    CanonicalRlp (RlpString [b]) [b]
| rlpShortString (payload : list byte) :
    (List.length payload <= 55)%nat ->
    (match payload with
     | [b] => 128 <= bv_unsigned b
     | _ => True
     end) ->
    CanonicalRlp (RlpString payload)
      (mword_of_int (128 + Z.of_nat (List.length payload)) :: payload)
| rlpLongString (payload lengthBytes : list byte) :
    (56 <= List.length payload)%nat ->
    minimalLengthBytes lengthBytes (List.length payload) ->
    CanonicalRlp (RlpString payload)
      (mword_of_int (183 + Z.of_nat (List.length lengthBytes))
       :: lengthBytes ++ payload)
| rlpShortList (items : list RlpTree) (encodings : list (list byte)) :
    Forall2 CanonicalRlp items encodings ->
    (List.length (concat encodings) <= 55)%nat ->
    CanonicalRlp (RlpList items)
      (mword_of_int (192 + Z.of_nat (List.length (concat encodings)))
       :: concat encodings)
| rlpLongList (items : list RlpTree) (encodings : list (list byte))
    (lengthBytes : list byte) :
    Forall2 CanonicalRlp items encodings ->
    (56 <= List.length (concat encodings))%nat ->
    minimalLengthBytes lengthBytes (List.length (concat encodings)) ->
    CanonicalRlp (RlpList items)
      (mword_of_int (247 + Z.of_nat (List.length lengthBytes))
       :: lengthBytes ++ concat encodings).

Definition RlpListContents (items : list RlpTree)
    (encoded : list byte) : Prop :=
  exists encodings,
    Forall2 CanonicalRlp items encodings /\
    encoded = concat encodings.

Lemma emptyRlpListContents : RlpListContents [] [].
Proof. exists []; split; constructor. Qed.

Record ProjectedAccessEntry := {
  accessAddress : list byte;
  accessStorageKeys : list (list byte);
}.

Definition accessEntryTree (entry : ProjectedAccessEntry) : RlpTree :=
  RlpList [RlpString entry.(accessAddress);
           RlpList (map RlpString entry.(accessStorageKeys))].

Definition accessEntriesWellFormed (entries : list ProjectedAccessEntry) : Prop :=
  Forall (fun entry =>
    List.length entry.(accessAddress) = 20%nat /\
    Forall (fun key => List.length key = 32%nat)
      entry.(accessStorageKeys)) entries.

Definition totalStorageKeys (entries : list ProjectedAccessEntry) : nat :=
  fold_right (fun entry count =>
    List.length entry.(accessStorageKeys) + count)%nat 0%nat entries.

Definition accessListProjection (backing : list byte)
    (ref : AccessListRef) (entries : list ProjectedAccessEntry) : Prop :=
  sliceIsBacked backing ref.(AccessListRef_encoded) /\
  accessEntriesWellFormed entries /\
  RlpListContents (map accessEntryTree entries)
    (sliceContents backing ref.(AccessListRef_encoded)) /\
  ref.(AccessListRef_address_count).(transaction_item_count_value) =
    Z.of_nat (List.length entries) /\
  ref.(AccessListRef_slot_count).(transaction_item_count_value) =
    Z.of_nat (totalStorageKeys entries).

Definition blobHashesProjection {limit : Z} (backing : list byte)
    (ref : BlobHashesFields limit) (hashes : list (list byte)) : Prop :=
  sliceIsBacked backing ref.(BlobHashesFields_bytes) /\
  Forall (fun hash =>
    List.length hash = 32%nat /\
    match hash with
    | [] => False
    | version :: _ => bv_unsigned version = 1
    end) hashes /\
  sliceContents backing ref.(BlobHashesFields_bytes) =
    concat (map (fun hash => mword_of_int 160 :: hash) hashes) /\
  ref.(BlobHashesFields_count) =
    Z.of_nat (List.length hashes) /\
  Z.of_nat (List.length hashes) <= limit.

Definition canonicalIntegerBytes (value : Z) (payload : list byte)
    (maxBytes : nat) : Prop :=
  0 <= value /\
  (List.length payload <= maxBytes)%nat /\
  bigEndian payload = value /\
  match payload with
  | [] => value = 0
  | first :: _ => bv_unsigned first <> 0
  end.

Record ProjectedAuthorization := {
  authorizationChainId : Z;
  authorizationAddress : list byte;
  authorizationNonce : Z;
  authorizationV : Z;
  authorizationR : Z;
  authorizationS : Z;
}.

Definition authorizationTree (tuple : ProjectedAuthorization)
    (tree : RlpTree) : Prop :=
  exists chainBytes nonceBytes vBytes rBytes sBytes,
    canonicalIntegerBytes tuple.(authorizationChainId) chainBytes 32 /\
    List.length tuple.(authorizationAddress) = 20%nat /\
    canonicalIntegerBytes tuple.(authorizationNonce) nonceBytes 8 /\
    canonicalIntegerBytes tuple.(authorizationV) vBytes 8 /\
    canonicalIntegerBytes tuple.(authorizationR) rBytes 32 /\
    canonicalIntegerBytes tuple.(authorizationS) sBytes 32 /\
    tree = RlpList
      [RlpString chainBytes; RlpString tuple.(authorizationAddress);
       RlpString nonceBytes; RlpString vBytes;
       RlpString rBytes; RlpString sBytes].

Definition authorizationListProjection (backing : list byte)
    (ref : AuthorizationListRef)
    (tuples : list ProjectedAuthorization) : Prop :=
  match ref with
  | existT count fields =>
      sliceIsBacked backing fields.(AuthorizationListRefFields_encoded) /\
      fields.(AuthorizationListRefFields_count) = Z.of_nat (List.length tuples) /\
      count = Z.of_nat (List.length tuples) /\
      exists trees,
        Forall2 authorizationTree tuples trees /\
        RlpListContents trees
          (sliceContents backing fields.(AuthorizationListRefFields_encoded))
  end.

Record ProjectedTransaction := {
  projectedType : Z;
  projectedChainId : option Z;
  projectedNonce : Z;
  projectedGasPrice : Z;
  projectedPriorityFee : option Z;
  projectedGasLimit : Z;
  projectedTo : option (list byte);
  projectedValue : Z;
  projectedData : list byte;
  projectedAccessList : list ProjectedAccessEntry;
  projectedBlobHashes : list (list byte);
  projectedMaxBlobFee : Z;
  projectedAuthorizations : list ProjectedAuthorization;
  projectedV : Z;
  projectedR : Z;
  projectedS : Z;
}.

(* Zig decodes the raw legacy v. The cast to u64 at source line 345 is only
   defined inside this range. For v < 27 Zig leaves v=0 and chain_id=null. *)
Definition legacyRawV (raw : Z) (chainId : option Z) (parity : Z) : Prop :=
  0 <= raw < 2 ^ 256 /\
  if 35 <=? raw then
    let chain := (raw - 35) / 2 in
    chain < 2 ^ 64 /\
    chainId = Some chain /\ parity = (raw - 35) mod 2
  else if 27 <=? raw then
    chainId = None /\ parity = raw - 27
  else chainId = None /\ parity = 0.

Example legacyV27 : legacyRawV 27 None 0.
Proof. vm_compute. intuition discriminate. Qed.

Example legacyV36 : legacyRawV 36 (Some 0) 1.
Proof. vm_compute. intuition discriminate. Qed.

Definition chainAndVProjection {limit : Z}
    (sail : TransactionFields limit) (zig : ProjectedTransaction) : Prop :=
  let raw := sail.(TransactionFields_sig_v).(word_value) in
  if Z.eqb zig.(projectedType) 0 then
    sail.(TransactionFields_chain_id).(chain_identifier_value) = 0 /\
    legacyRawV raw zig.(projectedChainId) zig.(projectedV)
  else
    zig.(projectedChainId) =
      Some sail.(TransactionFields_chain_id).(chain_identifier_value) /\
    zig.(projectedV) = raw /\
    0 <= raw < 2 ^ 64.

Definition priorityFeeProjection {limit : Z}
    (sail : TransactionFields limit) (zig : ProjectedTransaction) : Prop :=
  if (Z.eqb zig.(projectedType) 0 ||
      Z.eqb zig.(projectedType) 1)%bool then
    zig.(projectedPriorityFee) = None /\
    sail.(TransactionFields_max_priority_fee).(word_value) =
      sail.(TransactionFields_max_fee).(word_value)
  else
    zig.(projectedPriorityFee) =
      Some sail.(TransactionFields_max_priority_fee).(word_value) /\
    0 <= sail.(TransactionFields_max_priority_fee).(word_value) < 2 ^ 128.

Definition destinationProjection {limit : Z}
    (sail : TransactionFields limit) (destination : option (list byte))
    : Prop :=
  match destination with
  | None => sail.(TransactionFields_is_create) = true
  | Some address =>
      sail.(TransactionFields_is_create) = false /\
      List.length address = 20%nat /\
      address = projT1 sail.(TransactionFields_recipient)
  end.

Definition transactionDefaults (zig : ProjectedTransaction) : Prop :=
  match zig.(projectedType) with
  | 0 =>
      zig.(projectedAccessList) = [] /\
      zig.(projectedBlobHashes) = [] /\
      zig.(projectedAuthorizations) = [] /\
      zig.(projectedMaxBlobFee) = 0
  | 1 | 2 =>
      zig.(projectedBlobHashes) = [] /\
      zig.(projectedAuthorizations) = [] /\
      zig.(projectedMaxBlobFee) = 0
  | 3 => zig.(projectedAuthorizations) = []
  | 4 =>
      zig.(projectedBlobHashes) = [] /\
      zig.(projectedMaxBlobFee) = 0
  | _ => False
  end.

Definition TransactionProjection {limit : Z} (backing : list byte)
    (rawBytes publicKeyBytes : list byte)
    (sail : TransactionFields limit) (zig : ProjectedTransaction) : Prop :=
  zig.(projectedType) = num_of_TxType sail.(TransactionFields_tx_type) /\
  0 <= zig.(projectedType) <= 4 /\
  transactionDefaults zig /\
  zig.(projectedNonce) = sail.(TransactionFields_nonce).(word_value) /\
  0 <= zig.(projectedNonce) < 2 ^ 64 /\
  chainAndVProjection sail zig /\
  zig.(projectedGasLimit) =
    sail.(TransactionFields_gas_limit).(transaction_gas_value) /\
  0 <= zig.(projectedGasLimit) < 2 ^ 64 /\
  destinationProjection sail zig.(projectedTo) /\
  zig.(projectedValue) = sail.(TransactionFields_value).(word_value) /\
  0 <= zig.(projectedValue) < 2 ^ 256 /\
  inputIsBacked backing sail.(TransactionFields_input_src) /\
  zig.(projectedData) =
    inputContents backing sail.(TransactionFields_input_src) /\
  accessListProjection backing sail.(TransactionFields_access_list)
    zig.(projectedAccessList) /\
  zig.(projectedGasPrice) =
    sail.(TransactionFields_max_fee).(word_value) /\
  0 <= zig.(projectedGasPrice) < 2 ^ 128 /\
  priorityFeeProjection sail zig /\
  zig.(projectedMaxBlobFee) =
    sail.(TransactionFields_max_blob_fee).(word_value) /\
  0 <= zig.(projectedMaxBlobFee) < 2 ^ 128 /\
  blobHashesProjection backing sail.(TransactionFields_blob_hashes)
    zig.(projectedBlobHashes) /\
  authorizationListProjection backing sail.(TransactionFields_authorizations)
    zig.(projectedAuthorizations) /\
  zig.(projectedR) = sail.(TransactionFields_sig_r).(word_value) /\
  zig.(projectedS) = sail.(TransactionFields_sig_s).(word_value) /\
  0 <= zig.(projectedR) < 2 ^ 256 /\
  0 <= zig.(projectedS) < 2 ^ 256 /\
  sliceIsBacked backing sail.(TransactionFields_raw) /\
  sliceContents backing sail.(TransactionFields_raw) = rawBytes /\
  sliceIsBacked backing sail.(TransactionFields_pubkey) /\
  sliceContents backing sail.(TransactionFields_pubkey) = publicKeyBytes.

(* No Zig Transaction field stores Sail's sender or signing_hash. Their
   computation belongs to the C4 host contract, not this value projection. *)
