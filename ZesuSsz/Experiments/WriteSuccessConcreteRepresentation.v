From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.opsem.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessParserLemmas.

Import ListNotations.
Open Scope Z_scope.

Fixpoint writeSuccessLayoutLe (width : nat) (value : Z) : ByteString :=
  match width with
  | O => []
  | S width => value mod 256 :: writeSuccessLayoutLe width (value / 256)
  end.

Definition writeSuccessMemoryBytes
    (memory : mem_map) (address : Z) (bytes : ByteString) : Prop :=
  read_mem_list memory address (N.of_nat (length bytes)) =
    Some (map (Z_to_bv 8) bytes).

Definition writeSuccessMemoryInteger
    (memory : mem_map) (address : Z) (width : nat) (value : Z) : Prop :=
  writeSuccessMemoryBytes memory address (writeSuccessLayoutLe width value).

Definition writeSuccessMemorySlice
    (memory : mem_map) (owner : Z) (offset : Z)
  (bytes : ByteString) : Prop :=
  exists pointer,
    0 <= pointer < 2 ^ 64 /\
    writeSuccessMemoryInteger memory (owner + offset) 8 pointer /\
    writeSuccessMemoryInteger memory (owner + offset + 8) 8
      (Z.of_nat (length bytes)) /\
    writeSuccessMemoryBytes memory pointer bytes.

Definition writeSuccessMemoryOptionalU64
    (memory : mem_map) (owner : Z) (offset : Z)
    (value : option Z) : Prop :=
  match value with
  | None => writeSuccessMemoryInteger memory (owner + offset + 8) 1 0
  | Some item =>
      writeSuccessMemoryInteger memory (owner + offset) 8 item /\
      writeSuccessMemoryInteger memory (owner + offset + 8) 1 1
  end.

Definition writeSuccessMemoryOptionalBytes
    (memory : mem_map) (owner : Z) (offset : Z)
    (value : option ByteString) : Prop :=
  match value with
  | None => writeSuccessMemoryInteger memory (owner + offset) 8 0
  | Some bytes =>
      exists pointer,
        0 <= pointer < 2 ^ 64 /\
        writeSuccessMemoryInteger memory (owner + offset) 8 pointer /\
        writeSuccessMemoryInteger memory (owner + offset + 8) 8
          (Z.of_nat (length bytes)) /\
        writeSuccessMemoryBytes memory pointer bytes /\ pointer <> 0
  end.

Definition writeSuccessMemoryFixedList
    (memory : mem_map) (owner : Z) (offset stride : Z)
  (items : list ByteString) : Prop :=
  exists pointer,
    0 <= pointer < 2 ^ 64 /\
    writeSuccessMemoryInteger memory (owner + offset) 8 pointer /\
    writeSuccessMemoryInteger memory (owner + offset + 8) 8
      (Z.of_nat (length items)) /\
    forall index item,
      nth_error items index = Some item ->
      writeSuccessMemoryBytes memory
        (pointer + stride * Z.of_nat index) item.

Definition writeSuccessMemoryByteLists
    (memory : mem_map) (owner : Z) (offset : Z)
  (items : list ByteString) : Prop :=
  exists pointer,
    0 <= pointer < 2 ^ 64 /\
    writeSuccessMemoryInteger memory (owner + offset) 8 pointer /\
    writeSuccessMemoryInteger memory (owner + offset + 8) 8
      (Z.of_nat (length items)) /\
    forall index item,
      nth_error items index = Some item ->
      writeSuccessMemorySlice memory
        (pointer + 16 * Z.of_nat index) 0 item.

Definition writeSuccessAccessEntryMemory
    (memory : mem_map) (address : Z)
    (entry : WriteSuccessAccessEntryObservation) : Prop :=
  writeSuccessMemoryBytes memory (address + 16)
    (observationAccessAddress entry) /\
  writeSuccessMemoryFixedList memory address 0 32
    (observationStorageKeys entry).

Definition writeSuccessAccessListMemory
    (memory : mem_map) (owner : Z) (offset : Z)
  (entries : list WriteSuccessAccessEntryObservation) : Prop :=
  exists pointer,
    0 <= pointer < 2 ^ 64 /\
    writeSuccessMemoryInteger memory (owner + offset) 8 pointer /\
    writeSuccessMemoryInteger memory (owner + offset + 8) 8
      (Z.of_nat (length entries)) /\
    forall index entry,
      nth_error entries index = Some entry ->
      writeSuccessAccessEntryMemory memory
        (pointer + 40 * Z.of_nat index) entry.

Definition writeSuccessAuthorizationMemory
    (memory : mem_map) (address : Z)
    (authorization : WriteSuccessAuthorizationObservation) : Prop :=
  writeSuccessMemoryInteger memory address 32
    (observationAuthorizationChainId authorization) /\
  writeSuccessMemoryInteger memory (address + 32) 32
    (observationAuthorizationR authorization) /\
  writeSuccessMemoryInteger memory (address + 64) 32
    (observationAuthorizationS authorization) /\
  writeSuccessMemoryInteger memory (address + 96) 8
    (observationAuthorizationNonce authorization) /\
  writeSuccessMemoryInteger memory (address + 104) 8
    (observationAuthorizationV authorization) /\
  writeSuccessMemoryBytes memory (address + 112)
    (observationAuthorizationAddress authorization).

Definition writeSuccessAuthorizationListMemory
    (memory : mem_map) (owner : Z) (offset : Z)
  (items : list WriteSuccessAuthorizationObservation) : Prop :=
  exists pointer,
    0 <= pointer < 2 ^ 64 /\
    writeSuccessMemoryInteger memory (owner + offset) 8 pointer /\
    writeSuccessMemoryInteger memory (owner + offset + 8) 8
      (Z.of_nat (length items)) /\
    forall index item,
      nth_error items index = Some item ->
      writeSuccessAuthorizationMemory memory
        (pointer + 144 * Z.of_nat index) item.

Definition writeSuccessTransactionMemory
    (memory : mem_map) (address : Z)
    (transaction : WriteSuccessTransactionObservation) : Prop :=
  writeSuccessMemoryInteger memory (address + 264) 1
    (observationTransactionType transaction) /\
  writeSuccessMemoryOptionalU64 memory address 160
    (observationTransactionChainId transaction) /\
  writeSuccessMemoryInteger memory (address + 176) 8
    (observationTransactionNonce transaction) /\
  writeSuccessMemoryInteger memory address 16
    (observationTransactionGasPrice transaction) /\
  (match observationTransactionPriorityFee transaction with
   | None => writeSuccessMemoryInteger memory (address + 32) 1 0
   | Some value =>
       writeSuccessMemoryInteger memory (address + 16) 16 value /\
       writeSuccessMemoryInteger memory (address + 32) 1 1
   end) /\
  writeSuccessMemoryInteger memory (address + 184) 8
    (observationTransactionGasLimit transaction) /\
  (match observationTransactionTo transaction with
   | None => writeSuccessMemoryInteger memory (address + 285) 1 0
   | Some value =>
       writeSuccessMemoryBytes memory (address + 265) value /\
       writeSuccessMemoryInteger memory (address + 285) 1 1
   end) /\
  writeSuccessMemoryInteger memory (address + 48) 32
    (observationTransactionValue transaction) /\
  writeSuccessMemorySlice memory address 192
    (observationTransactionData transaction) /\
  writeSuccessAccessListMemory memory address 208
    (observationTransactionAccessList transaction) /\
  writeSuccessMemoryFixedList memory address 224 32
    (observationTransactionBlobHashes transaction) /\
  writeSuccessMemoryInteger memory (address + 80) 16
    (observationTransactionMaxBlobFee transaction) /\
  writeSuccessAuthorizationListMemory memory address 240
    (observationTransactionAuthorizations transaction) /\
  writeSuccessMemoryInteger memory (address + 256) 8
    (observationTransactionV transaction) /\
  writeSuccessMemoryInteger memory (address + 96) 32
    (observationTransactionR transaction) /\
  writeSuccessMemoryInteger memory (address + 128) 32
    (observationTransactionS transaction).

Definition writeSuccessTransactionListMemory
    (memory : mem_map) (owner : Z) (offset : Z)
  (items : list WriteSuccessTransactionObservation) : Prop :=
  exists pointer,
    0 <= pointer < 2 ^ 64 /\
    writeSuccessMemoryInteger memory (owner + offset) 8 pointer /\
    writeSuccessMemoryInteger memory (owner + offset + 8) 8
      (Z.of_nat (length items)) /\
    forall index item,
      nth_error items index = Some item ->
      writeSuccessTransactionMemory memory
        (pointer + 288 * Z.of_nat index) item.

Definition writeSuccessWithdrawalMemory
    (memory : mem_map) (address : Z)
    (withdrawal : WriteSuccessWithdrawalObservation) : Prop :=
  writeSuccessMemoryInteger memory address 8
    (observationWithdrawalIndex withdrawal) /\
  writeSuccessMemoryInteger memory (address + 8) 8
    (observationWithdrawalValidatorIndex withdrawal) /\
  writeSuccessMemoryInteger memory (address + 16) 8
    (observationWithdrawalAmount withdrawal) /\
  writeSuccessMemoryBytes memory (address + 24)
    (observationWithdrawalAddress withdrawal).

Definition writeSuccessWithdrawalListMemory
    (memory : mem_map) (owner : Z) (offset : Z)
  (items : list WriteSuccessWithdrawalObservation) : Prop :=
  exists pointer,
    0 <= pointer < 2 ^ 64 /\
    writeSuccessMemoryInteger memory (owner + offset) 8 pointer /\
    writeSuccessMemoryInteger memory (owner + offset + 8) 8
      (Z.of_nat (length items)) /\
    forall index item,
      nth_error items index = Some item ->
      writeSuccessWithdrawalMemory memory
        (pointer + 48 * Z.of_nat index) item.

(** These offsets come from the pinned ELF DWARF types.  The predicate covers
    the 848-byte top value and every reachable payload. *)
Definition writeSuccessConcreteRepresentation
    (decoded : WriteSuccessObservation) (memory : mem_map)
    (address : Z) : Prop :=
  writeSuccessObservationValid decoded /\
  (exists top, length top = 848%nat /\
    read_mem_list memory address 848%N = Some top) /\
  writeSuccessMemoryInteger memory address 8
    (observationBlockNumber decoded) /\
  writeSuccessMemoryInteger memory (address + 8) 8
    (observationGasLimit decoded) /\
  writeSuccessMemoryInteger memory (address + 16) 8
    (observationGasUsed decoded) /\
  writeSuccessMemoryInteger memory (address + 24) 8
    (observationTimestamp decoded) /\
  writeSuccessMemorySlice memory address 32
    (observationExtraData decoded) /\
  writeSuccessMemoryInteger memory (address + 48) 8
    (observationBaseFee decoded) /\
  writeSuccessTransactionListMemory memory address 56
    (observationTransactions decoded) /\
  writeSuccessMemoryByteLists memory address 72
    (observationRawTransactions decoded) /\
  writeSuccessWithdrawalListMemory memory address 88
    (observationWithdrawals decoded) /\
  writeSuccessMemoryInteger memory (address + 104) 8
    (observationBlobGasUsed decoded) /\
  writeSuccessMemoryInteger memory (address + 112) 8
    (observationExcessBlobGas decoded) /\
  writeSuccessMemoryOptionalU64 memory address 120
    (observationSlotNumber decoded) /\
  writeSuccessMemorySlice memory address 136
    (observationBlockAccessList decoded) /\
  writeSuccessMemoryBytes memory (address + 152)
    (observationParentHash decoded) /\
  writeSuccessMemoryBytes memory (address + 184)
    (observationFeeRecipient decoded) /\
  writeSuccessMemoryBytes memory (address + 204)
    (observationStateRoot decoded) /\
  writeSuccessMemoryBytes memory (address + 236)
    (observationReceiptsRoot decoded) /\
  writeSuccessMemoryBytes memory (address + 268)
    (observationLogsBloom decoded) /\
  writeSuccessMemoryBytes memory (address + 524)
    (observationPrevRandao decoded) /\
  writeSuccessMemoryBytes memory (address + 556)
    (observationBlockHash decoded) /\
  writeSuccessMemoryFixedList memory address 592 32
    (observationVersionedHashes decoded) /\
  writeSuccessMemorySlice memory address 608
    (observationDeposits decoded) /\
  writeSuccessMemorySlice memory address 624
    (observationWithdrawalRequests decoded) /\
  writeSuccessMemorySlice memory address 640
    (observationConsolidations decoded) /\
  writeSuccessMemorySlice memory address 656
    (observationBuilderDeposits decoded) /\
  writeSuccessMemorySlice memory address 672
    (observationBuilderExits decoded) /\
  writeSuccessMemoryBytes memory (address + 688)
    (observationParentBeaconRoot decoded) /\
  writeSuccessMemoryByteLists memory address 720
    (observationWitnessNodes decoded) /\
  writeSuccessMemoryByteLists memory address 736
    (observationWitnessCodes decoded) /\
  writeSuccessMemoryByteLists memory address 752
    (observationWitnessHeaders decoded) /\
  writeSuccessMemoryInteger memory (address + 768) 8
    (observationChainId decoded) /\
  writeSuccessMemoryOptionalBytes memory address 776
    (observationForkName decoded) /\
  writeSuccessMemoryInteger memory (address + 792) 8
    (observationActiveForkIndex decoded) /\
  writeSuccessMemoryOptionalU64 memory address 800
    (observationActivationBlock decoded) /\
  writeSuccessMemoryOptionalU64 memory address 816
    (observationActivationTimestamp decoded) /\
  writeSuccessMemoryByteLists memory address 832
    (observationPublicKeys decoded).

Lemma writeSuccessRepresentationBaseFee decoded memory address :
  writeSuccessConcreteRepresentation decoded memory address ->
  writeSuccessMemoryInteger memory (address + 48) 8
    (observationBaseFee decoded).
Proof. unfold writeSuccessConcreteRepresentation. tauto. Qed.

Lemma writeSuccessRepresentationExtraData decoded memory address :
  writeSuccessConcreteRepresentation decoded memory address ->
  writeSuccessMemorySlice memory address 32
    (observationExtraData decoded).
Proof. unfold writeSuccessConcreteRepresentation. tauto. Qed.

Lemma writeSuccessObservationExtraDataValid decoded :
  writeSuccessObservationValid decoded ->
  writeSuccessVariableBytesValid (observationExtraData decoded).
Proof. unfold writeSuccessObservationValid. tauto. Qed.

Lemma writeSuccessMemoryBytesInjective memory address first second :
  length first = length second ->
  Forall writeSuccessByte first ->
  Forall writeSuccessByte second ->
  writeSuccessMemoryBytes memory address first ->
  writeSuccessMemoryBytes memory address second ->
  first = second.
Proof.
  intros Hlength Hfirst Hsecond HreadFirst HreadSecond.
  unfold writeSuccessMemoryBytes in *.
  rewrite Hlength in HreadFirst.
  rewrite HreadFirst in HreadSecond. inversion HreadSecond.
  assert (Hmap : forall bytes,
      Forall writeSuccessByte bytes ->
      map bv_unsigned (map (Z_to_bv 8) bytes) = bytes).
  { intros bytes Hbytes. induction Hbytes as [|byte bytes Hbyte Hbytes IH].
    - reflexivity.
    - simpl. rewrite Z_to_bv_unsigned. rewrite bv_wrap_small.
      + rewrite IH. reflexivity.
      + exact Hbyte. }
  rewrite <- (Hmap first Hfirst), <- (Hmap second Hsecond), H0. reflexivity.
Qed.

Lemma writeSuccessLayoutLeEq width value :
  writeSuccessLayoutLe width value = writeSuccessEncodeLe width value.
Proof.
  revert value. induction width; intros value; simpl; [reflexivity |].
  rewrite IHwidth. reflexivity.
Qed.

Lemma writeSuccessLayoutLeInjective64 first second :
  writeSuccessUnsignedValid 8 first ->
  writeSuccessUnsignedValid 8 second ->
  writeSuccessLayoutLe 8 first = writeSuccessLayoutLe 8 second ->
  first = second.
Proof.
  intros Hfirst Hsecond Hequal.
  rewrite !writeSuccessLayoutLeEq in Hequal.
  rewrite <- (writeSuccessDecodeLeEncodeLe 8 first Hfirst).
  rewrite <- (writeSuccessDecodeLeEncodeLe 8 second Hsecond).
  rewrite Hequal. reflexivity.
Qed.

Lemma writeSuccessMemoryInteger64Injective memory address first second :
  writeSuccessUnsignedValid 8 first ->
  writeSuccessUnsignedValid 8 second ->
  writeSuccessMemoryInteger memory address 8 first ->
  writeSuccessMemoryInteger memory address 8 second ->
  first = second.
Proof.
  intros HvalidFirst HvalidSecond HreadFirst HreadSecond.
  apply writeSuccessLayoutLeInjective64; try assumption.
  unfold writeSuccessMemoryInteger in *.
  eapply writeSuccessMemoryBytesInjective.
  - rewrite !writeSuccessLayoutLeEq. rewrite !writeSuccessEncodeLeLength.
    reflexivity.
  - rewrite writeSuccessLayoutLeEq.
    apply writeSuccessEncodeLeBytes. exact (proj1 HvalidFirst).
  - rewrite writeSuccessLayoutLeEq.
    apply writeSuccessEncodeLeBytes. exact (proj1 HvalidSecond).
  - exact HreadFirst.
  - exact HreadSecond.
Qed.

Lemma writeSuccessRepresentationBaseFeeUnique first second memory address :
  writeSuccessConcreteRepresentation first memory address ->
  writeSuccessConcreteRepresentation second memory address ->
  observationBaseFee first <> observationBaseFee second ->
  False.
Proof.
  intros Hfirst Hsecond Hneq.
  pose proof (writeSuccessRepresentationBaseFee _ _ _ Hfirst) as HreadFirst.
  pose proof (writeSuccessRepresentationBaseFee _ _ _ Hsecond) as HreadSecond.
  assert (HvalidFirst :
    writeSuccessUnsignedValid 8 (observationBaseFee first)).
  { unfold writeSuccessConcreteRepresentation,
      writeSuccessObservationValid in Hfirst. tauto. }
  assert (HvalidSecond :
    writeSuccessUnsignedValid 8 (observationBaseFee second)).
  { unfold writeSuccessConcreteRepresentation,
      writeSuccessObservationValid in Hsecond. tauto. }
  apply Hneq. eapply writeSuccessMemoryInteger64Injective; eassumption.
Qed.

Lemma writeSuccessRepresentationExtraDataUnique first second memory address :
  writeSuccessConcreteRepresentation first memory address ->
  writeSuccessConcreteRepresentation second memory address ->
  observationExtraData first <> observationExtraData second ->
  False.
Proof.
  intros Hfirst Hsecond Hneq.
  pose proof (writeSuccessRepresentationExtraData _ _ _ Hfirst)
    as (pointerFirst & HpointerFirst & HptrFirst & HlenFirst & HbytesFirst).
  pose proof (writeSuccessRepresentationExtraData _ _ _ Hsecond)
    as (pointerSecond & HpointerSecond & HptrSecond & HlenSecond & HbytesSecond).
  assert (Hpointer : pointerFirst = pointerSecond).
  { eapply writeSuccessMemoryInteger64Injective; try eassumption;
      unfold writeSuccessUnsignedValid; cbn; tauto. }
  subst pointerSecond.
  assert (Hlength : length (observationExtraData first) =
      length (observationExtraData second)).
  { apply Nat2Z.inj.
    eapply writeSuccessMemoryInteger64Injective; try eassumption.
    - unfold writeSuccessUnsignedValid. cbn.
      unfold writeSuccessConcreteRepresentation in Hfirst.
      pose proof (writeSuccessObservationExtraDataValid _ (proj1 Hfirst))
        as Hvalid.
      unfold writeSuccessVariableBytesValid, writeSuccessLengthValid in Hvalid.
      lia.
    - unfold writeSuccessUnsignedValid. cbn.
      unfold writeSuccessConcreteRepresentation in Hsecond.
      pose proof (writeSuccessObservationExtraDataValid _ (proj1 Hsecond))
        as Hvalid.
      unfold writeSuccessVariableBytesValid, writeSuccessLengthValid in Hvalid.
      lia. }
  apply Hneq.
  eapply writeSuccessMemoryBytesInjective.
  - exact Hlength.
  - unfold writeSuccessConcreteRepresentation in Hfirst.
    pose proof (writeSuccessObservationExtraDataValid _ (proj1 Hfirst))
      as Hvalid.
    exact (proj2 Hvalid).
  - unfold writeSuccessConcreteRepresentation in Hsecond.
    pose proof (writeSuccessObservationExtraDataValid _ (proj1 Hsecond))
      as Hvalid.
    exact (proj2 Hvalid).
  - exact HbytesFirst.
  - exact HbytesSecond.
Qed.

Print Assumptions writeSuccessRepresentationBaseFee.
Print Assumptions writeSuccessRepresentationExtraData.
Print Assumptions writeSuccessRepresentationBaseFeeUnique.
Print Assumptions writeSuccessRepresentationExtraDataUnique.
