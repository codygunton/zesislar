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
  bugVersionedHashBytes : nat
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
                                requestsStart - hashesStart |}
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

(** This reader extracts an offset-table count after the Zesu size checks.
    A successful endpoint outcome supplies the remaining element checks. *)
Definition zesuVariableListCount
    (bytes : ByteString) (start : nat) (span : Z) : option Z :=
  if span =? 0 then Some 0 else
  if 4 <=? span then
    match zesuReadU32At bytes start with
    | Some first =>
        if (0 <? first) && (first <=? span) &&
           (Z.modulo first 4 =? 0)
        then Some (Z.div first 4)
        else None
    | None => None
    end
  else None.

Record ZesuListCountLayout : Type := {
  bugWithdrawalBytes : nat;
  bugTransactionCount : Z;
  bugWitnessHeaderCount : Z
}.

(** Keep the seven original layout fields and predicates unchanged. *)
Definition zesuListCountLayout (input : ByteString) : option ZesuListCountLayout :=
  let bytes := zesuBugPayload input in
  match zesuReadU32At bytes 2, zesuReadU32At bytes 6,
        zesuReadU32At bytes 10 with
  | Some nprOffset, Some witnessOffset, Some chainOffset =>
      let nprStart := (2 + Z.to_nat nprOffset)%nat in
      let witnessStart := (2 + Z.to_nat witnessOffset)%nat in
      let chainStart := (2 + Z.to_nat chainOffset)%nat in
      match zesuReadU32At bytes nprStart,
            zesuReadU32At bytes (nprStart + 4),
            zesuReadU32At bytes (witnessStart + 8) with
      | Some payloadOffset, Some hashesOffset, Some headersOffset =>
          let payloadStart := (nprStart + Z.to_nat payloadOffset)%nat in
          let payloadEnd := (nprStart + Z.to_nat hashesOffset)%nat in
          let headersStart := (witnessStart + Z.to_nat headersOffset)%nat in
          match zesuReadU32At bytes (payloadStart + 436),
                zesuReadU32At bytes (payloadStart + 504),
                zesuReadU32At bytes (payloadStart + 508) with
          | Some fixedLength, Some transactionsOffset, Some withdrawalsOffset =>
              match if fixedLength =? 540
                    then zesuReadU32At bytes (payloadStart + 528)
                    else if fixedLength =? 528
                         then Some (Z.of_nat (payloadEnd - payloadStart))
                         else None with
              | Some accessListOffset =>
                  if (fixedLength <=? transactionsOffset) &&
                     (transactionsOffset <=? withdrawalsOffset) &&
                     (withdrawalsOffset <=? accessListOffset) &&
                     (accessListOffset <=? Z.of_nat (payloadEnd - payloadStart)) &&
                     Nat.leb headersStart chainStart &&
                     Nat.leb chainStart (length bytes)
                  then
                    match zesuVariableListCount bytes
                            (payloadStart + Z.to_nat transactionsOffset)
                            (withdrawalsOffset - transactionsOffset),
                          zesuVariableListCount bytes headersStart
                            (Z.of_nat (chainStart - headersStart)) with
                    | Some transactions, Some headers =>
                        Some {| bugWithdrawalBytes :=
                                  Z.to_nat (accessListOffset - withdrawalsOffset);
                                bugTransactionCount := transactions;
                                bugWitnessHeaderCount := headers |}
                    | _, _ => None
                    end
                  else None
              | None => None
              end
          | _, _, _ => None
          end
      | _, _, _ => None
      end
  | _, _, _ => None
  end.

(** Zesu checks 44-byte packing.  The reference permits at most 16 withdrawals. *)
Definition withdrawalCountApplies
    (input : ByteString) (actual : DecodeOutcome) : Prop :=
  match zesuListCountLayout input, actual with
  | Some layout, DecodeSuccess _ =>
      Nat.modulo (bugWithdrawalBytes layout) 44 = 0%nat /\
      (16 * 44 < Z.of_nat (bugWithdrawalBytes layout))%Z
  | _, _ => False
  end.

(** Zesu checks the offset table and RLP items.  The reference permits at most
    1048576 transactions. *)
Definition transactionCountApplies
    (input : ByteString) (actual : DecodeOutcome) : Prop :=
  match zesuListCountLayout input, actual with
  | Some layout, DecodeSuccess _ => 1048576 < bugTransactionCount layout
  | _, _ => False
  end.

(** Zesu checks the offset table.  The reference permits at most 256 headers. *)
Definition witnessHeaderCountApplies
    (input : ByteString) (actual : DecodeOutcome) : Prop :=
  match zesuListCountLayout input, actual with
  | Some layout, DecodeSuccess _ => 256 < bugWitnessHeaderCount layout
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
     bugVersionedHashBytes := 32 |}.

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
