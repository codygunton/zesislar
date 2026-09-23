From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import EvmSail.evm_decoder_types.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Compliance.Targets.
Require Import ZesuSsz.Contracts.Endpoints.

Import ListNotations.
Open Scope Z_scope.

(** These readers classify the SSZ input bytes.  Their offsets follow the
    pinned decoder snapshot and [src/stateless/stateless/ssz.zig] in the
    pinned Zesu source. *)
Fixpoint zesuReadLeAt
    (width : nat) (bytes : ByteString) (offset : nat) : option Z :=
  match width with
  | O => Some 0
  | S rest =>
      match nth_error bytes offset, zesuReadLeAt rest bytes (S offset) with
      | Some byte, Some value =>
          if (0 <=? byte) && (byte <? 256)
          then Some (byte + 256 * value)
          else None
      | _, _ => None
      end
  end.

Definition zesuReadU32At := zesuReadLeAt 4.
Definition zesuReadU64At := zesuReadLeAt 8.

Lemma zesuReadLeAt_app_left width (prefix suffix : ByteString) offset :
  (offset + width <= length prefix)%nat ->
  zesuReadLeAt width (prefix ++ suffix) offset =
    zesuReadLeAt width prefix offset.
Proof.
  revert offset.
  induction width as [|width IH]; intros offset Hbound; cbn.
  - reflexivity.
  - rewrite nth_error_app1 by lia.
    rewrite IH by lia.
    reflexivity.
Qed.

Lemma zesuReadLeAt_app_right width (prefix suffix : ByteString) offset :
  (length prefix <= offset)%nat ->
  zesuReadLeAt width (prefix ++ suffix) offset =
    zesuReadLeAt width suffix (offset - length prefix)%nat.
Proof.
  revert offset.
  induction width as [|width IH]; intros offset Hbound; cbn.
  - reflexivity.
  - rewrite nth_error_app2 by lia.
    rewrite IH by lia.
    replace (S offset - length prefix)%nat with
      (S (offset - length prefix))%nat by lia.
    reflexivity.
Qed.

(** A variable SSZ list stores four bytes per offset.  The first offset is
    the table length, so dividing it by four gives the item count. *)
Definition zesuVariableListCount
    (bytes : ByteString) (start span : nat) : option Z :=
  if Nat.eqb span 0 then Some 0 else
  match zesuReadU32At bytes start with
  | Some first =>
      if (Z.eqb (Z.modulo first 4) 0) &&
         (Z.leb 4 first) && (Z.leb first (Z.of_nat span))
      then Some (Z.div first 4)
      else None
  | None => None
  end.

Definition zesuBugPayload (input : ByteString) : ByteString :=
  match zesuReadU32At input 0 with
  | Some declared =>
      if Nat.eqb (length input) (4 + Z.to_nat declared)
      then skipn 4 input
      else input
  | None => input
  end.

Definition zesuReadOptionalU64
    (bytes : ByteString) (offset span : nat) : option (option Z) :=
  if Nat.leb 8 span then
    match zesuReadU64At bytes offset with
    | Some value => Some (Some value)
    | None => None
    end
  else Some None.

Record ZesuBugLayout : Type := {
  bugChainId : Z;
  bugRequestFixedLength : Z;
  bugPayloadFixedLength : Z;
  bugBlockNumber : Z;
  bugTimestamp : Z;
  bugActivationBlock : option Z;
  bugActivationTimestamp : option Z;
  bugExtraDataBytes : nat;
  bugPublicKeyBytes : nat;
  bugVersionedHashBytes : nat;
  bugWithdrawalBytes : option nat;
  bugTransactionCount : option Z;
  bugWitnessHeaderCount : option Z
}.

(** The endpoint can only return [DecodeSuccess] after its decoder validates
    all container ordering conditions.  This function therefore extracts only
    the fields that distinguish the seven reviewed divergence domains. *)
Definition zesuBugLayout (input : ByteString) : option ZesuBugLayout :=
  let bytes := zesuBugPayload input in
  match zesuReadU32At bytes 2,
        zesuReadU32At bytes 6,
        zesuReadU32At bytes 10,
        zesuReadU32At bytes 14 with
  | Some nprOffset, Some witnessOffset, Some chainOffset, Some keysOffset =>
      let nprStart := (2 + Z.to_nat nprOffset)%nat in
      let chainStart := (2 + Z.to_nat chainOffset)%nat in
      let keysStart := (2 + Z.to_nat keysOffset)%nat in
      match zesuReadU32At bytes nprStart,
            zesuReadU32At bytes (nprStart + 4),
            zesuReadU32At bytes (nprStart + 40),
            zesuReadU64At bytes chainStart,
            zesuReadU32At bytes (chainStart + 8) with
      | Some payloadOffset, Some hashesOffset, Some requestsOffset,
        Some chainId, Some activeForkOffset =>
          let payloadStart := (nprStart + Z.to_nat payloadOffset)%nat in
          let hashesStart := (nprStart + Z.to_nat hashesOffset)%nat in
          let requestsStart := (nprStart + Z.to_nat requestsOffset)%nat in
          let activeForkStart :=
            (chainStart + Z.to_nat activeForkOffset)%nat in
          match zesuReadU32At bytes requestsStart,
            zesuReadU32At bytes (payloadStart + 436),
            zesuReadU32At bytes (payloadStart + 504),
            zesuReadU64At bytes (payloadStart + 404),
                zesuReadU64At bytes (payloadStart + 428),
                zesuReadU32At bytes activeForkStart with
          | Some requestFixedLength, Some payloadFixedLength,
            Some transactionsOffset, Some blockNumber, Some timestamp,
            Some activationOffset =>
              let activationStart :=
                (activeForkStart + Z.to_nat activationOffset)%nat in
              let transactionsStart :=
                (payloadStart + Z.to_nat transactionsOffset)%nat in
              match zesuReadU32At bytes activationStart,
                    zesuReadU32At bytes (activationStart + 4) with
              | Some blockOffset, Some timestampOffset =>
                  let blockStart :=
                    (activationStart + Z.to_nat blockOffset)%nat in
                  let timestampStart :=
                    (activationStart + Z.to_nat timestampOffset)%nat in
                  match zesuReadOptionalU64 bytes blockStart
                          (Z.to_nat timestampOffset - Z.to_nat blockOffset),
                        zesuReadOptionalU64 bytes timestampStart
                          (keysStart - timestampStart) with
                  | Some activationBlock, Some activationTimestamp =>
                      Some {| bugChainId := chainId;
                              bugRequestFixedLength := requestFixedLength;
                              bugPayloadFixedLength := payloadFixedLength;
                              bugBlockNumber := blockNumber;
                              bugTimestamp := timestamp;
                              bugActivationBlock := activationBlock;
                              bugActivationTimestamp := activationTimestamp;
                              bugExtraDataBytes :=
                                Z.to_nat transactionsOffset -
                                  Z.to_nat payloadFixedLength;
                              bugPublicKeyBytes := length bytes - keysStart;
                              bugVersionedHashBytes :=
                                requestsStart - hashesStart;
                              bugWithdrawalBytes :=
                                match zesuReadU32At bytes (payloadStart + 508) with
                                | Some withdrawalsOffset =>
                                    if Z.eqb payloadFixedLength 528 then
                                      Some (hashesStart - payloadStart -
                                        Z.to_nat withdrawalsOffset)%nat
                                    else
                                      match zesuReadU32At bytes (payloadStart + 528) with
                                      | Some accessListOffset =>
                                          Some (Z.to_nat accessListOffset -
                                            Z.to_nat withdrawalsOffset)%nat
                                      | None => None
                                      end
                                | None => None
                                end;
                              bugTransactionCount :=
                                match zesuReadU32At bytes (payloadStart + 508) with
                                | Some withdrawalsOffset =>
                                    zesuVariableListCount bytes transactionsStart
                                      (Z.to_nat withdrawalsOffset -
                                        Z.to_nat transactionsOffset)%nat
                                | None => None
                                end;
                              bugWitnessHeaderCount :=
                                match zesuReadU32At bytes
                                    (2 + Z.to_nat witnessOffset + 8) with
                                | Some headersOffset =>
                                    let headersStart :=
                                      (2 + Z.to_nat witnessOffset +
                                        Z.to_nat headersOffset)%nat in
                                    zesuVariableListCount bytes headersStart
                                      (chainStart - headersStart)%nat
                                | None => None
                                end |}
                  | _, _ => None
                  end
              | _, _ => None
              end
          | _, _, _, _, _, _ => None
          end
      | _, _, _, _, _ => None
      end
  | _, _, _, _ => None
  end.

Definition zesuDecodedChainId (decoded : StatelessInput) : Z :=
  chain_identifier_value
    (ChainConfig_chain_id (StatelessInput_chain_config decoded)).

(** Zesu changes an encoded chain identifier of zero to one.  EVM-Sail
    preserves the encoded value. *)
Definition chainIdZeroNormalizationApplies
    (input : ByteString) (actual : DecodeOutcome) : Prop :=
  match zesuBugLayout input, actual with
  | Some layout, DecodeSuccess decoded =>
      bugChainId layout = 0 /\ zesuDecodedChainId decoded = 1
  | _, _ => False
  end.

(** The legacy request container has three offsets and a 12-byte fixed area.
    The reference decoder requires five offsets and a 20-byte fixed area. *)
Definition legacyRequestTableArityApplies
    (input : ByteString) (actual : DecodeOutcome) : Prop :=
  match zesuBugLayout input, actual with
  | Some layout, DecodeSuccess _ => bugRequestFixedLength layout = 12
  | _, _ => False
  end.

(** Zesu accepts the 528-byte V3 payload.  The reference snapshot requires
    the 540-byte V4 payload. *)
Definition legacyPayloadSizeApplies
    (input : ByteString) (actual : DecodeOutcome) : Prop :=
  match zesuBugLayout input, actual with
  | Some layout, DecodeSuccess _ => bugPayloadFixedLength layout = 528
  | _, _ => False
  end.

(** Zesu records a future activation during decoding.  The reference decoder
    rejects an activation after the payload block number or timestamp. *)
Definition futureForkActivationApplies
    (input : ByteString) (actual : DecodeOutcome) : Prop :=
  match zesuBugLayout input, actual with
  | Some layout, DecodeSuccess _ =>
      (exists activation,
          bugActivationBlock layout = Some activation /\
          bugBlockNumber layout < activation) \/
      (exists activation,
          bugActivationTimestamp layout = Some activation /\
          bugTimestamp layout < activation)
  | _, _ => False
  end.

(** Zesu accepts extra data beyond 32 bytes.  The reference bound is 32. *)
Definition extraDataLengthApplies
    (input : ByteString) (actual : DecodeOutcome) : Prop :=
  match zesuBugLayout input, actual with
  | Some layout, DecodeSuccess _ => (32 < bugExtraDataBytes layout)%nat
  | _, _ => False
  end.

(** Zesu checks the 65-byte packing but not the reference limit of 32768
    public keys. *)
Definition publicKeyCountApplies
    (input : ByteString) (actual : DecodeOutcome) : Prop :=
  match zesuBugLayout input, actual with
  | Some layout, DecodeSuccess _ =>
      Nat.modulo (bugPublicKeyBytes layout) 65 = 0%nat /\
      (32768 * 65 < Z.of_nat (bugPublicKeyBytes layout))%Z
  | _, _ => False
  end.

(** Zesu checks the 32-byte packing but not the reference limit of 4096
    versioned hashes. *)
Definition versionedHashCountApplies
    (input : ByteString) (actual : DecodeOutcome) : Prop :=
  match zesuBugLayout input, actual with
  | Some layout, DecodeSuccess _ =>
      Nat.modulo (bugVersionedHashBytes layout) 32 = 0%nat /\
      (4096 * 32 < Z.of_nat (bugVersionedHashBytes layout))%Z
  | _, _ => False
  end.

(** The reference accepts at most 16 fixed-width, 44-byte withdrawals. *)
Definition withdrawalCountApplies
    (input : ByteString) (actual : DecodeOutcome) : Prop :=
  match zesuBugLayout input, actual with
  | Some layout, DecodeSuccess _ =>
      exists bytes, bugWithdrawalBytes layout = Some bytes /\
        Nat.modulo bytes 44 = 0%nat /\
        (16 * 44 < bytes)%nat
  | _, _ => False
  end.

(** The reference accepts at most 2^20 transaction offsets. *)
Definition transactionCountApplies
    (input : ByteString) (actual : DecodeOutcome) : Prop :=
  match zesuBugLayout input, actual with
  | Some layout, DecodeSuccess _ =>
      exists count, bugTransactionCount layout = Some count /\
        1048576 < count
  | _, _ => False
  end.

(** The reference accepts at most 2^8 witness-header offsets. *)
Definition witnessHeaderCountApplies
    (input : ByteString) (actual : DecodeOutcome) : Prop :=
  match zesuBugLayout input, actual with
  | Some layout, DecodeSuccess _ =>
      exists count, bugWitnessHeaderCount layout = Some count /\
        256 < count
  | _, _ => False
  end.

Definition zesuBugApplies : BugApplies :=
  fun bug =>
    match bug with
    | ChainIdZeroNormalization => chainIdZeroNormalizationApplies
    | LegacyRequestTableArity => legacyRequestTableArityApplies
    | LegacyPayloadSize => legacyPayloadSizeApplies
    | FutureForkActivation => futureForkActivationApplies
    | ExtraDataLength => extraDataLengthApplies
    | PublicKeyCount => publicKeyCountApplies
    | VersionedHashCount => versionedHashCountApplies
    | WithdrawalCount => withdrawalCountApplies
    | TransactionCount => transactionCountApplies
    | WitnessHeaderCount => witnessHeaderCountApplies
    end.

(** Compliance compares complete decode outcomes. *)
Definition zesuEquivalent : OutcomeRelation := eq.

Fixpoint zesuEncodeLe (width : nat) (value : Z) : ByteString :=
  match width with
  | O => []
  | S rest =>
      Z.modulo value 256 :: zesuEncodeLe rest (Z.div value 256)
  end.

(** These byte inputs expose one count above each reference bound.
    They witness the raw count fields only.  They do not establish that the
    pinned Zesu decoder returns [DecodeSuccess] for these inputs. *)
Definition zesuCountPayload
    (transactions withdrawals : ByteString) : ByteString :=
  let withdrawalOffset := (540 + length transactions)%nat in
  let accessOffset := (withdrawalOffset + length withdrawals)%nat in
  repeat 0 436 ++ zesuEncodeLe 4 540 ++ repeat 0 64 ++
  zesuEncodeLe 4 540 ++
  zesuEncodeLe 4 (Z.of_nat withdrawalOffset) ++ repeat 0 16 ++
  zesuEncodeLe 4 (Z.of_nat accessOffset) ++ repeat 0 8 ++
  transactions ++ withdrawals.

Definition zesuCountWitnessInput
    (transactions withdrawals headers : ByteString) : ByteString :=
  let payload := zesuCountPayload transactions withdrawals in
  let request :=
    zesuEncodeLe 4 44 ++
    zesuEncodeLe 4 (Z.of_nat (44 + length payload)%nat) ++ repeat 0 32 ++
    zesuEncodeLe 4 (Z.of_nat (76 + length payload)%nat) ++
    payload ++ repeat 0 32 ++ concat (repeat (zesuEncodeLe 4 20) 5) in
  let witness :=
    zesuEncodeLe 4 12 ++ zesuEncodeLe 4 12 ++
    zesuEncodeLe 4 12 ++ headers in
  let witnessOffset := (16 + length request)%nat in
  let chainOffset := (witnessOffset + length witness)%nat in
  [15; 1] ++ zesuEncodeLe 4 16 ++
  zesuEncodeLe 4 (Z.of_nat witnessOffset) ++
  zesuEncodeLe 4 (Z.of_nat chainOffset) ++
  zesuEncodeLe 4 (Z.of_nat (chainOffset + 40)%nat) ++
  request ++ witness ++
  zesuEncodeLe 8 1 ++ zesuEncodeLe 4 12 ++
  zesuEncodeLe 4 4 ++ zesuEncodeLe 4 8 ++ zesuEncodeLe 4 16 ++
  zesuEncodeLe 8 0 ++ zesuEncodeLe 8 0.

Definition withdrawalCountWitnessInput : ByteString :=
  zesuCountWitnessInput [] (repeat 0 (17 * 44)%nat) [].

Definition transactionCountWitnessBytes : ByteString :=
  zesuEncodeLe 4 4194308 ++ repeat 0 4194304.

(* Literal container offsets keep the four-megabyte list symbolic. *)
Definition transactionCountWitnessPrefix : ByteString :=
  [15; 1] ++ zesuEncodeLe 4 16 ++
  zesuEncodeLe 4 4194960 ++ zesuEncodeLe 4 4194972 ++
  zesuEncodeLe 4 4195012 ++
  zesuEncodeLe 4 44 ++ zesuEncodeLe 4 4194892 ++ repeat 0 32 ++
  zesuEncodeLe 4 4194924 ++
  repeat 0 436 ++ zesuEncodeLe 4 540 ++ repeat 0 64 ++
  zesuEncodeLe 4 540 ++ zesuEncodeLe 4 4194848 ++
  repeat 0 16 ++ zesuEncodeLe 4 4194848 ++ repeat 0 8.

Definition transactionCountWitnessSuffix : ByteString :=
  repeat 0 32 ++
  concat (repeat (zesuEncodeLe 4 20) 5) ++
  zesuEncodeLe 4 12 ++ zesuEncodeLe 4 12 ++ zesuEncodeLe 4 12 ++
  zesuEncodeLe 8 1 ++ zesuEncodeLe 4 12 ++
  zesuEncodeLe 4 4 ++ zesuEncodeLe 4 8 ++ zesuEncodeLe 4 16 ++
  zesuEncodeLe 8 0 ++ zesuEncodeLe 8 0.

Definition transactionCountWitnessInput : ByteString :=
  transactionCountWitnessPrefix ++
    (transactionCountWitnessBytes ++ transactionCountWitnessSuffix).

Definition witnessHeaderCountWitnessBytes : ByteString :=
  zesuEncodeLe 4 1028 ++ repeat 0 1024.

Definition witnessHeaderCountWitnessInput : ByteString :=
  zesuCountWitnessInput [] [] witnessHeaderCountWitnessBytes.

(** The V3 extra-data bytes look like a V4 access-list offset, but V3 uses
    the end of the payload as the withdrawal end. *)
Definition v3WithdrawalSentinelPayload : ByteString :=
  repeat 0 436 ++ zesuEncodeLe 4 528 ++ repeat 0 64 ++
  zesuEncodeLe 4 532 ++ zesuEncodeLe 4 532 ++ repeat 0 16 ++
  zesuEncodeLe 4 1280.

Definition v3WithdrawalSentinelInput : ByteString :=
  let payload := v3WithdrawalSentinelPayload in
  let request :=
    zesuEncodeLe 4 44 ++
    zesuEncodeLe 4 (Z.of_nat (44 + length payload)%nat) ++ repeat 0 32 ++
    zesuEncodeLe 4 (Z.of_nat (76 + length payload)%nat) ++
    payload ++ repeat 0 32 ++ concat (repeat (zesuEncodeLe 4 20) 5) in
  let witness :=
    zesuEncodeLe 4 12 ++ zesuEncodeLe 4 12 ++ zesuEncodeLe 4 12 in
  let witnessOffset := (16 + length request)%nat in
  let chainOffset := (witnessOffset + length witness)%nat in
  [15; 1] ++ zesuEncodeLe 4 16 ++
  zesuEncodeLe 4 (Z.of_nat witnessOffset) ++
  zesuEncodeLe 4 (Z.of_nat chainOffset) ++
  zesuEncodeLe 4 (Z.of_nat (chainOffset + 40)%nat) ++
  request ++ witness ++
  zesuEncodeLe 8 1 ++ zesuEncodeLe 4 12 ++
  zesuEncodeLe 4 4 ++ zesuEncodeLe 4 8 ++ zesuEncodeLe 4 16 ++
  zesuEncodeLe 8 0 ++ zesuEncodeLe 8 0.

Lemma withdrawalCountWitnessSpan :
  (16 * 44 < length (repeat 0 (17 * 44)%nat))%nat.
Proof. rewrite repeat_length. lia. Qed.

Lemma transactionCountWitnessLength :
  length transactionCountWitnessBytes = 4194308%nat.
Proof.
  unfold transactionCountWitnessBytes.
  rewrite app_length, repeat_length.
  reflexivity.
Qed.

Lemma transactionCountWitnessPrefixLength :
  length transactionCountWitnessPrefix = 602%nat.
Proof.
  unfold transactionCountWitnessPrefix.
  repeat rewrite app_length.
  repeat rewrite repeat_length.
  reflexivity.
Qed.

Lemma transactionCountWitnessField :
  zesuVariableListCount transactionCountWitnessBytes 0
    (length transactionCountWitnessBytes) = Some 1048577.
Proof.
  rewrite transactionCountWitnessLength.
  unfold zesuVariableListCount.
  replace (Nat.eqb 4194308 0) with false by reflexivity.
  replace (zesuReadU32At transactionCountWitnessBytes 0)
    with (Some 4194308) by reflexivity.
  replace (Z.eqb (Z.modulo 4194308 4) 0) with true by reflexivity.
  replace (Z.leb 4 4194308) with true by reflexivity.
  replace (Z.leb 4194308 (Z.of_nat 4194308)) with true
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma witnessHeaderCountWitnessField :
  zesuVariableListCount witnessHeaderCountWitnessBytes 0
    (length witnessHeaderCountWitnessBytes) = Some 257.
Proof.
  unfold witnessHeaderCountWitnessBytes.
  rewrite app_length, repeat_length.
  reflexivity.
Qed.

Lemma withdrawalCountWitnessLayout :
  exists layout,
    zesuBugLayout withdrawalCountWitnessInput = Some layout /\
    bugWithdrawalBytes layout = Some 748%nat.
Proof. native_compute. eexists; split; reflexivity. Qed.

Lemma witnessHeaderCountWitnessLayout :
  exists layout,
    zesuBugLayout witnessHeaderCountWitnessInput = Some layout /\
    bugWitnessHeaderCount layout = Some 257.
Proof. native_compute. eexists; split; reflexivity. Qed.

Lemma v3WithdrawalSentinelLayout :
  exists layout,
    zesuBugLayout v3WithdrawalSentinelInput = Some layout /\
    bugWithdrawalBytes layout = Some 0%nat.
Proof. native_compute. eexists; split; reflexivity. Qed.

Lemma v3WithdrawalSentinelRejectsCount decoded :
  ~ withdrawalCountApplies v3WithdrawalSentinelInput
      (DecodeSuccess decoded).
Proof.
  unfold withdrawalCountApplies.
  destruct v3WithdrawalSentinelLayout as [layout [Hlayout Hbytes]].
  rewrite Hlayout.
  intros [bytes [Hcount [_ Hlarge]]].
  rewrite Hbytes in Hcount.
  inversion Hcount; lia.
Qed.

Lemma transactionCountWitnessPayloadOffsets :
  zesuReadU32At transactionCountWitnessInput 566 = Some 540 /\
  zesuReadU32At transactionCountWitnessInput 570 = Some 4194848.
Proof.
  unfold transactionCountWitnessInput, zesuReadU32At.
  split.
  - rewrite zesuReadLeAt_app_left
      by (rewrite transactionCountWitnessPrefixLength; lia).
    reflexivity.
  - rewrite zesuReadLeAt_app_left
      by (rewrite transactionCountWitnessPrefixLength; lia).
    reflexivity.
Qed.

Lemma transactionCountWitnessInputFirstOffset :
  zesuReadU32At transactionCountWitnessInput 602 = Some 4194308.
Proof.
  unfold transactionCountWitnessInput, zesuReadU32At.
  rewrite zesuReadLeAt_app_right
    by (rewrite transactionCountWitnessPrefixLength; lia).
  rewrite transactionCountWitnessPrefixLength.
  replace (602 - 602)%nat with 0%nat by lia.
  rewrite (zesuReadLeAt_app_left 4 transactionCountWitnessBytes
    transactionCountWitnessSuffix 0)
    by (rewrite transactionCountWitnessLength;
        apply Nat.leb_le; vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma transactionCountWitnessInputCount :
  zesuVariableListCount transactionCountWitnessInput 602 4194308 =
    Some 1048577.
Proof.
  unfold zesuVariableListCount.
  replace (Nat.eqb 4194308 0) with false by reflexivity.
  rewrite transactionCountWitnessInputFirstOffset.
  replace (Z.eqb (Z.modulo 4194308 4) 0) with true by reflexivity.
  replace (Z.leb 4 4194308) with true by reflexivity.
  replace (Z.leb 4194308 (Z.of_nat 4194308)) with true
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Definition zesuNonBugPayload : ByteString :=
  repeat 0 436 ++ zesuEncodeLe 4 540 ++ repeat 0 64 ++
  zesuEncodeLe 4 540 ++ zesuEncodeLe 4 540 ++ repeat 0 16 ++
  zesuEncodeLe 4 540 ++ repeat 0 8.

Definition zesuNonBugInput (fork : Z) : ByteString :=
  [fork; 1] ++
  zesuEncodeLe 4 16 ++ zesuEncodeLe 4 652 ++
  zesuEncodeLe 4 664 ++ zesuEncodeLe 4 704 ++
  zesuEncodeLe 4 44 ++ zesuEncodeLe 4 584 ++ repeat 0 32 ++
  zesuEncodeLe 4 616 ++ zesuNonBugPayload ++ repeat 0 32 ++
  concat (repeat (zesuEncodeLe 4 20) 5) ++
  concat (repeat (zesuEncodeLe 4 12) 3) ++
  zesuEncodeLe 8 1 ++ zesuEncodeLe 4 12 ++ zesuEncodeLe 4 4 ++
  zesuEncodeLe 4 8 ++ zesuEncodeLe 4 16 ++
  zesuEncodeLe 8 0 ++ zesuEncodeLe 8 0.

Definition chainIdNonVacuityInput := zesuNonBugInput 15.
Definition requestArityNonVacuityInput := zesuNonBugInput 16.
Definition payloadSizeNonVacuityInput := zesuNonBugInput 17.
Definition forkActivationNonVacuityInput := zesuNonBugInput 18.
Definition extraDataNonVacuityInput := zesuNonBugInput 19.
Definition publicKeyNonVacuityInput := zesuNonBugInput 20.
Definition versionedHashNonVacuityInput := zesuNonBugInput 21.

Definition zesuExpectedNonBugLayout : ZesuBugLayout :=
  {| bugChainId := 1;
     bugRequestFixedLength := 20;
     bugPayloadFixedLength := 540;
     bugBlockNumber := 0;
     bugTimestamp := 0;
     bugActivationBlock := Some 0;
     bugActivationTimestamp := Some 0;
     bugExtraDataBytes := 0;
     bugPublicKeyBytes := 0;
     bugVersionedHashBytes := 32;
     bugWithdrawalBytes := Some 0%nat;
     bugTransactionCount := Some 0;
     bugWitnessHeaderCount := Some 0 |}.

Lemma chainIdNonVacuityLayout :
  zesuBugLayout chainIdNonVacuityInput = Some zesuExpectedNonBugLayout.
Proof. native_compute. reflexivity. Qed.

Lemma requestArityNonVacuityLayout :
  zesuBugLayout requestArityNonVacuityInput = Some zesuExpectedNonBugLayout.
Proof. native_compute. reflexivity. Qed.

Lemma payloadSizeNonVacuityLayout :
  zesuBugLayout payloadSizeNonVacuityInput = Some zesuExpectedNonBugLayout.
Proof. native_compute. reflexivity. Qed.

Lemma forkActivationNonVacuityLayout :
  zesuBugLayout forkActivationNonVacuityInput = Some zesuExpectedNonBugLayout.
Proof. native_compute. reflexivity. Qed.

Lemma extraDataNonVacuityLayout :
  zesuBugLayout extraDataNonVacuityInput = Some zesuExpectedNonBugLayout.
Proof. native_compute. reflexivity. Qed.

Lemma publicKeyNonVacuityLayout :
  zesuBugLayout publicKeyNonVacuityInput = Some zesuExpectedNonBugLayout.
Proof. native_compute. reflexivity. Qed.

Lemma versionedHashNonVacuityLayout :
  zesuBugLayout versionedHashNonVacuityInput = Some zesuExpectedNonBugLayout.
Proof. native_compute. reflexivity. Qed.

Lemma chainIdZeroNormalizationNonVacuous actual :
  ~ chainIdZeroNormalizationApplies chainIdNonVacuityInput actual.
Proof.
  unfold chainIdZeroNormalizationApplies.
  rewrite chainIdNonVacuityLayout. destruct actual; cbn; lia.
Qed.

Lemma legacyRequestTableArityNonVacuous actual :
  ~ legacyRequestTableArityApplies requestArityNonVacuityInput actual.
Proof.
  unfold legacyRequestTableArityApplies.
  rewrite requestArityNonVacuityLayout. destruct actual; cbn; lia.
Qed.

Lemma legacyPayloadSizeNonVacuous actual :
  ~ legacyPayloadSizeApplies payloadSizeNonVacuityInput actual.
Proof.
  unfold legacyPayloadSizeApplies.
  rewrite payloadSizeNonVacuityLayout. destruct actual; cbn; lia.
Qed.

Lemma futureForkActivationNonVacuous actual :
  ~ futureForkActivationApplies forkActivationNonVacuityInput actual.
Proof.
  unfold futureForkActivationApplies.
  rewrite forkActivationNonVacuityLayout.
  destruct actual as [decoded|]; cbn.
  - intros [[activation [Heq Hfuture]]|[activation [Heq Hfuture]]];
      inversion Heq; subst activation; exact (Z.lt_irrefl 0 Hfuture).
  - tauto.
Qed.

Lemma extraDataLengthNonVacuous actual :
  ~ extraDataLengthApplies extraDataNonVacuityInput actual.
Proof.
  unfold extraDataLengthApplies.
  rewrite extraDataNonVacuityLayout. destruct actual; cbn; lia.
Qed.

Lemma publicKeyCountNonVacuous actual :
  ~ publicKeyCountApplies publicKeyNonVacuityInput actual.
Proof.
  unfold publicKeyCountApplies.
  rewrite publicKeyNonVacuityLayout. destruct actual; cbn; lia.
Qed.

Lemma versionedHashCountNonVacuous actual :
  ~ versionedHashCountApplies versionedHashNonVacuityInput actual.
Proof.
  unfold versionedHashCountApplies.
  rewrite versionedHashNonVacuityLayout. destruct actual; cbn; lia.
Qed.
