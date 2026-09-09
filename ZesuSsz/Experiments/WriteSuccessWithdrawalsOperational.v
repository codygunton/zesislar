From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessParserLemmas.
Require Import ZesuSsz.Experiments.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.

Import ListNotations.
Open Scope Z_scope.

Definition WriteSuccessWithdrawalsRecord : Type :=
  (seq_label * mem_map)%type.

Definition WriteSuccessWithdrawalsConcreteState : Type :=
  (IslaState * list WriteSuccessWithdrawalsRecord)%type.

Definition writeSuccessWithdrawalsConcretePc
    (state : WriteSuccessWithdrawalsConcreteState) : option Z :=
  match state.1.1.(seq_regs) !! state.1.1.(seq_pc_reg) with
  | Some (RVal_Bits value) => Some (bvn_unsigned value)
  | _ => None
  end.

Fixpoint writeSuccessWithdrawalsRecordedPayloads
    (log : list WriteSuccessWithdrawalsRecord) :
    option (list (list (bv 8))) :=
  match log with
  | [] => Some []
  | (SWriteMem pointerPort data, memory) ::
      (SWriteMem sizePort size, _) :: rest =>
      if bool_decide
          (bv_unsigned pointerPort = 0x2401a0c0 /\
           bv_unsigned sizePort = 0x2401a0c8) then
        match read_mem_list memory (bvn_unsigned data)
            (Z.to_N (bvn_unsigned size)),
          writeSuccessWithdrawalsRecordedPayloads rest with
        | Some payload, Some payloads => Some (payload :: payloads)
        | _, _ => None
        end
      else None
  | _ => None
  end.

Definition writeSuccessWithdrawalIntegerBytes (value : Z) : list (bv 8) :=
  map (Z_to_bv 8) (writeSuccessEncodeU64 value).

Definition writeSuccessWithdrawalAddressBytes
    (withdrawal : WriteSuccessWithdrawalObservation) : list (bv 8) :=
  map (Z_to_bv 8) (observationWithdrawalAddress withdrawal).

Definition writeSuccessWithdrawalFragments
    (withdrawal : WriteSuccessWithdrawalObservation) : list (list (bv 8)) :=
  [writeSuccessWithdrawalIntegerBytes (observationWithdrawalIndex withdrawal);
   writeSuccessWithdrawalIntegerBytes
     (observationWithdrawalValidatorIndex withdrawal);
   writeSuccessWithdrawalAddressBytes withdrawal;
   writeSuccessWithdrawalIntegerBytes (observationWithdrawalAmount withdrawal)].

Definition writeSuccessWithdrawalDescriptors (sp : bv 64) :
    list WriteOutputDescriptor :=
  [((sp - BV 64 16)%bv, BV 64 8);
   ((sp - BV 64 16)%bv, BV 64 8);
   ((sp + BV 64 1768)%bv, BV 64 20);
   ((sp - BV 64 16)%bv, BV 64 8)].

Definition writeSuccessWithdrawalIterationRecords
    (sp : bv 64) (withdrawal : WriteSuccessWithdrawalObservation)
    (records : list WriteSuccessWithdrawalsRecord) : Prop :=
  map fst records =
    writeOutputDescriptorsEvents (writeSuccessWithdrawalDescriptors sp) /\
  writeSuccessWithdrawalsRecordedPayloads records =
    Some (writeSuccessWithdrawalFragments withdrawal).

Definition writeSuccessWithdrawalsObservedBytes
    (records : list WriteSuccessWithdrawalsRecord) : option ByteString :=
  match writeSuccessWithdrawalsRecordedPayloads records with
  | Some payloads => Some (writeSuccessPublicBytes (concat payloads))
  | None => None
  end.

Definition writeSuccessWithdrawalRawBytes
    (withdrawal : WriteSuccessWithdrawalObservation)
    (padding : list (bv 8)) : list (bv 8) :=
  writeSuccessWithdrawalIntegerBytes (observationWithdrawalIndex withdrawal) ++
  writeSuccessWithdrawalIntegerBytes
    (observationWithdrawalValidatorIndex withdrawal) ++
  writeSuccessWithdrawalIntegerBytes (observationWithdrawalAmount withdrawal) ++
  writeSuccessWithdrawalAddressBytes withdrawal ++ padding.

Lemma writeSuccessWithdrawalIntegerBytesLength value :
  length (writeSuccessWithdrawalIntegerBytes value) = 8%nat.
Proof.
  unfold writeSuccessWithdrawalIntegerBytes.
  rewrite map_length writeSuccessEncodeLeLength. reflexivity.
Qed.

Lemma writeSuccessWithdrawalAddressBytesLength withdrawal :
  writeSuccessWithdrawalObservationValid withdrawal ->
  length (writeSuccessWithdrawalAddressBytes withdrawal) = 20%nat.
Proof.
  intros (_ & _ & Haddress & _).
  destruct Haddress as [Hlength _].
  unfold writeSuccessWithdrawalAddressBytes.
  by rewrite map_length Hlength.
Qed.

Lemma writeSuccessWithdrawalMemoryReads memory address withdrawal :
  writeSuccessWithdrawalObservationValid withdrawal ->
  writeSuccessWithdrawalMemory memory address withdrawal ->
  read_mem_list memory address 8%N =
    Some (writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalIndex withdrawal)) /\
  read_mem_list memory (address + 8) 8%N =
    Some (writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalValidatorIndex withdrawal)) /\
  read_mem_list memory (address + 16) 8%N =
    Some (writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalAmount withdrawal)) /\
  read_mem_list memory (address + 24) 20%N =
    Some (writeSuccessWithdrawalAddressBytes withdrawal).
Proof.
  intros (_ & _ & [HaddressLength _] & _)
    (Hindex & Hvalidator & Hamount & Haddress).
  unfold writeSuccessMemoryInteger, writeSuccessMemoryBytes in *.
  unfold writeSuccessWithdrawalIntegerBytes,
    writeSuccessWithdrawalAddressBytes.
  rewrite !writeSuccessLayoutLeEq in Hindex, Hvalidator, Hamount.
  rewrite !writeSuccessEncodeLeLength in Hindex, Hvalidator, Hamount.
  rewrite HaddressLength in Haddress.
  repeat split.
  - exact Hindex.
  - exact Hvalidator.
  - exact Hamount.
  - exact Haddress.
Qed.

Lemma read_mem_list_result_unique memory address length first second :
  read_mem_list memory address length = Some first ->
  read_mem_list memory address length = Some second ->
  first = second.
Proof. congruence. Qed.

Lemma writeSuccessWithdrawalRawBytesFromMemory memory address withdrawal raw :
  writeSuccessWithdrawalObservationValid withdrawal ->
  writeSuccessWithdrawalMemory memory address withdrawal ->
  read_mem_list memory address 48%N = Some raw ->
  exists padding,
    length padding = 4%nat /\
    raw = writeSuccessWithdrawalRawBytes withdrawal padding.
Proof.
  intros Hvalid Hmemory Hraw.
  pose proof (writeSuccessWithdrawalMemoryReads _ _ _ Hvalid Hmemory) as
    (Hindex & Hvalidator & Hamount & Haddress).
  destruct (read_mem_list_split memory address 8 40 raw Hraw) as
    (indexBytes & afterIndex & HrawSplit & HindexLength & HafterIndexLength &
      HindexRead & HafterIndexRead).
  have HindexBytes : indexBytes = writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalIndex withdrawal).
  { eapply read_mem_list_result_unique; eassumption. }
  destruct (read_mem_list_split memory (address + 8) 8 32 afterIndex
      HafterIndexRead) as
    (validatorBytes & afterValidator & HvalidatorSplit & HvalidatorLength &
      HafterValidatorLength & HvalidatorRead & HafterValidatorRead).
  have HvalidatorBytes : validatorBytes = writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalValidatorIndex withdrawal).
  { eapply read_mem_list_result_unique; eassumption. }
  replace (address + 8 + Z.of_nat 8) with (address + 16) in
    HafterValidatorRead by lia.
  destruct (read_mem_list_split memory (address + 16) 8 24 afterValidator
      HafterValidatorRead) as
    (amountBytes & afterAmount & HamountSplit & HamountLength &
      HafterAmountLength & HamountRead & HafterAmountRead).
  have HamountBytes : amountBytes = writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalAmount withdrawal).
  { eapply read_mem_list_result_unique; eassumption. }
  replace (address + 16 + Z.of_nat 8) with (address + 24) in
    HafterAmountRead by lia.
  destruct (read_mem_list_split memory (address + 24) 20 4 afterAmount
      HafterAmountRead) as
    (addressBytes & padding & HaddressSplit & HaddressLength & HpaddingLength &
      HaddressRead & HpaddingRead).
  have HaddressBytes : addressBytes = writeSuccessWithdrawalAddressBytes withdrawal.
  { eapply read_mem_list_result_unique; eassumption. }
  exists padding. split; first exact HpaddingLength.
  unfold writeSuccessWithdrawalRawBytes.
  rewrite HrawSplit HvalidatorSplit HamountSplit HaddressSplit.
  rewrite HindexBytes HvalidatorBytes HamountBytes HaddressBytes.
  repeat rewrite app_assoc. reflexivity.
Qed.

Lemma writeSuccessWithdrawalRawBytesLength withdrawal padding :
  writeSuccessWithdrawalObservationValid withdrawal ->
  length padding = 4%nat ->
  length (writeSuccessWithdrawalRawBytes withdrawal padding) = 48%nat.
Proof.
  intros Hvalid Hpadding.
  unfold writeSuccessWithdrawalRawBytes.
  rewrite !app_length !writeSuccessWithdrawalIntegerBytesLength.
  rewrite writeSuccessWithdrawalAddressBytesLength; assumption || lia.
Qed.

Lemma writeSuccessPublicBytesZToBv bytes :
  Forall writeSuccessByte bytes ->
  writeSuccessPublicBytes (map (Z_to_bv 8) bytes) = bytes.
Proof.
  intros Hbytes. induction Hbytes as [|byte bytes Hbyte Hbytes IH];
    first reflexivity.
  unfold writeSuccessPublicBytes in *. cbn.
  rewrite Z_to_bv_unsigned bv_wrap_small; [by rewrite IH | exact Hbyte].
Qed.

Lemma writeSuccessWithdrawalFragmentsEncode withdrawal :
  writeSuccessWithdrawalObservationValid withdrawal ->
  writeSuccessPublicBytes (concat (writeSuccessWithdrawalFragments withdrawal)) =
    writeSuccessEncodeWithdrawal withdrawal.
Proof.
  intros (Hindex & Hvalidator & Haddress & Hamount).
  unfold writeSuccessWithdrawalFragments, writeSuccessEncodeWithdrawal.
  cbn [concat]. rewrite !writeSuccessPublicBytes_app.
  unfold writeSuccessWithdrawalIntegerBytes,
    writeSuccessWithdrawalAddressBytes.
  rewrite !writeSuccessPublicBytesZToBv.
  - reflexivity.
  - apply writeSuccessEncodeLeBytes. exact (proj1 Hamount).
  - exact (proj2 Haddress).
  - apply writeSuccessEncodeLeBytes. exact (proj1 Hvalidator).
  - apply writeSuccessEncodeLeBytes. exact (proj1 Hindex).
Qed.

Lemma writeSuccessWithdrawalIterationRecordsEncode sp withdrawal records :
  writeSuccessWithdrawalObservationValid withdrawal ->
  writeSuccessWithdrawalIterationRecords sp withdrawal records ->
  writeSuccessWithdrawalsObservedBytes records =
    Some (writeSuccessEncodeWithdrawal withdrawal).
Proof.
  intros Hvalid [_ Hpayloads].
  unfold writeSuccessWithdrawalsObservedBytes. rewrite Hpayloads.
  rewrite writeSuccessWithdrawalFragmentsEncode; [reflexivity | exact Hvalid].
Qed.

Lemma writeSuccessZToBvAddOperational n left right :
  (Z_to_bv n left + Z_to_bv n right)%bv = Z_to_bv n (left + right).
Proof.
  apply bv_eq. rewrite bv_add_unsigned !Z_to_bv_unsigned.
  bv_wrap_simplify_solve.
Qed.

Lemma writeSuccessWithdrawalsCounterDecrementOperational remaining :
  (Z_to_bv 64 (S (S remaining)) +
    BV 64 18446744073709551615)%bv =
  Z_to_bv 64 (S remaining).
Proof.
  replace (BV 64 18446744073709551615) with (Z_to_bv 64 (-1)) by
    (apply bv_eq; vm_compute; reflexivity).
  rewrite writeSuccessZToBvAddOperational. f_equal. lia.
Qed.

Lemma writeSuccessWithdrawalsPointerAdvanceOperational pointer base processed :
  bv_unsigned pointer = base + 48 * Z.of_nat processed ->
  bv_unsigned pointer + 48 < 2 ^ 64 ->
  bv_unsigned (pointer + BV 64 48)%bv =
    base + 48 * Z.of_nat (S processed).
Proof.
  intros Hpointer Hrange.
  rewrite bv_add_unsigned bv_unsigned_BV. cbn.
  unfold bv_wrap, bv_modulus. cbn.
  rewrite Z.mod_small; [rewrite Hpointer Nat2Z.inj_succ; lia |].
  pose proof (bv_unsigned_in_range 64 pointer). unfold bv_modulus in *.
  cbn in *. lia.
Qed.

Lemma writeSuccessWithdrawalsSuffixAdvance {A} (current suffix : list A) :
  length current = 48%nat ->
  skipn 48 (current ++ suffix) = suffix.
Proof.
  intros Hlength. rewrite skipn_app Hlength Nat.sub_diag.
  cbn. rewrite skipn_all2; [reflexivity | lia].
Qed.

Lemma writeSuccessRepresentationWithdrawalAt decoded memory address index
    withdrawal :
  writeSuccessConcreteRepresentation decoded memory address ->
  nth_error (observationWithdrawals decoded) index = Some withdrawal ->
  writeSuccessWithdrawalObservationValid withdrawal /\
  exists pointer,
    0 <= pointer < 2 ^ 64 /\
    writeSuccessMemoryInteger memory (address + 88) 8 pointer /\
    writeSuccessMemoryInteger memory (address + 88 + 8) 8
      (Z.of_nat (length (observationWithdrawals decoded))) /\
    writeSuccessWithdrawalMemory memory
      (pointer + 48 * Z.of_nat index) withdrawal.
Proof.
  intros Hrepresentation Hnth.
  have HobservationValid : writeSuccessObservationValid decoded.
  { unfold writeSuccessConcreteRepresentation in Hrepresentation. tauto. }
  have HwithdrawalsValid : writeSuccessListValid
      writeSuccessWithdrawalObservationValid (observationWithdrawals decoded).
  { unfold writeSuccessObservationValid in HobservationValid. tauto. }
  have HwithdrawalValid : writeSuccessWithdrawalObservationValid withdrawal.
  { destruct HwithdrawalsValid as [_ Hforall].
    revert index Hnth. induction Hforall as [|item items Hitem Hitems IH];
      intros [|index] Hnth; cbn in Hnth; try discriminate.
    - inversion Hnth. subst. exact Hitem.
    - eapply IH. exact Hnth. }
  split; first exact HwithdrawalValid.
  have HwithdrawalMemory : writeSuccessWithdrawalListMemory memory address 88
      (observationWithdrawals decoded).
  { unfold writeSuccessConcreteRepresentation in Hrepresentation. tauto. }
  unfold writeSuccessWithdrawalListMemory in HwithdrawalMemory.
  destruct HwithdrawalMemory as
    (pointer & Hpointer & HpointerRead & HlengthRead & Hitems).
  exists pointer. split; first exact Hpointer.
  split; first exact HpointerRead.
  split; first exact HlengthRead.
  exact (Hitems index withdrawal Hnth).
Qed.

Definition writeSuccessWithdrawalsProtectedRegisters : list string :=
  ["x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27"].

Definition writeSuccessWithdrawalsRegisterFrame
    (registers frame : reg_map) : Prop :=
  Forall (fun register => registers !! register = frame !! register)
    writeSuccessWithdrawalsProtectedRegisters.

Definition writeSuccessWithdrawalsMemoryFrame
    (sp : bv 64) (memory frame : mem_map) : Prop :=
  dom memory = dom frame /\
  forall address,
    ~ (bv_unsigned sp - 16 <= bv_unsigned address < bv_unsigned sp) ->
    ~ (bv_unsigned sp + 1744 <= bv_unsigned address <
       bv_unsigned sp + 1792) ->
    memory !! address = frame !! address.

Definition writeSuccessMemoryRangeFrame
    (start : Z) (rangeLength : nat) (memory frame : mem_map) : Prop :=
  dom memory = dom frame /\
  forall address,
    ~ (start <= bv_unsigned address < start + Z.of_nat rangeLength) ->
    memory !! address = frame !! address.

Lemma writeSuccessMemoryRangeFrameWrite memory frame address bytes :
  writeSuccessMemoryRangeFrame address (length bytes) memory frame ->
  islaMemoryRange address (length bytes) ->
  (forall location,
    address <= location < address + Z.of_nat (length bytes) ->
    is_Some (memory !! Z_to_bv 64 location)) ->
  writeSuccessMemoryRangeFrame address (length bytes)
    (write_mem_list memory (Z_to_bv 64 address) bytes) frame.
Proof.
  intros [Hdom Hframe] Hrange Hbacked. split.
  - rewrite write_mem_list_dom; assumption.
  - intros key Houtside.
    have HkeyOutside :
        bv_unsigned key < address \/
        address + Z.of_nat (length bytes) <= bv_unsigned key.
    { unfold islaMemoryRange in Hrange.
      destruct (Z_lt_ge_dec (bv_unsigned key) address); [by left | right].
      lia. }
    have Hlookup := write_mem_list_lookup_outside memory address bytes
      (bv_unsigned key) Hrange (bv_unsigned_in_range 64 key) HkeyOutside.
    rewrite Z_to_bv_bv_unsigned in Hlookup.
    rewrite Hlookup. apply Hframe. exact Houtside.
Qed.

Lemma writeSuccessMemcpyMemoryUpdate memory source destination bytes :
  read_mem_list memory source (N.of_nat (length bytes)) = Some bytes ->
  islaMemoryRange destination (length bytes) ->
  islaMemoryRangesDisjoint destination (length bytes)
    source (length bytes) ->
  (forall location,
    destination <= location < destination + Z.of_nat (length bytes) ->
    is_Some (memory !! Z_to_bv 64 location)) ->
  let after := write_mem_list memory (Z_to_bv 64 destination) bytes in
  read_mem_list after destination (N.of_nat (length bytes)) = Some bytes /\
  read_mem_list after source (N.of_nat (length bytes)) = Some bytes /\
  dom after = dom memory.
Proof.
  intros Hsource HdestinationRange Hdisjoint Hbacked. cbn.
  repeat split.
  - apply read_mem_list_written. exact HdestinationRange.
  - eapply read_mem_list_write_mem_list_disjoint; eassumption.
  - apply write_mem_list_dom; assumption.
Qed.

Definition Inv_memcpy
    (destination source returnAddress : bv 64) (bytes destinationBefore : list (bv 8))
    (memoryFrame : mem_map) (priorLog : list WriteSuccessWithdrawalsRecord)
    (state : WriteSuccessWithdrawalsConcreteState) : Prop :=
  IslaInstructionBoundary state.1 /\
  writeSuccessWithdrawalsConcretePc state = Some 0x101d4 /\
  state.1.1.(seq_regs) !! "x1" = Some (RVal_Bits returnAddress) /\
  state.1.1.(seq_regs) !! "x10" = Some (RVal_Bits destination) /\
  state.1.1.(seq_regs) !! "x11" = Some (RVal_Bits source) /\
  state.1.1.(seq_regs) !! "x12" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (length bytes)))) /\
  writeSuccessWithdrawalsInstructionTable state.1.2 /\
  writeSuccessTraceAssumptions state.1 /\
  read_mem_list state.1.2.(seq_mem) (bv_unsigned source)
    (N.of_nat (length bytes)) = Some bytes /\
  read_mem_list state.1.2.(seq_mem) (bv_unsigned destination)
    (N.of_nat (length bytes)) = Some destinationBefore /\
  islaMemoryRange (bv_unsigned destination) (length bytes) /\
  islaMemoryRangesDisjoint (bv_unsigned destination) (length bytes)
    (bv_unsigned source) (length bytes) /\
  (forall location,
    bv_unsigned destination <= location <
      bv_unsigned destination + Z.of_nat (length bytes) ->
    is_Some (state.1.2.(seq_mem) !! Z_to_bv 64 location)) /\
  writeSuccessMemoryRangeFrame (bv_unsigned destination) (length bytes)
    state.1.2.(seq_mem) memoryFrame /\
  state.2 = priorLog.

Definition block_memcpy_statement : Prop :=
  forall destination source returnAddress bytes destinationBefore memoryFrame
      priorLog state,
    Inv_memcpy destination source returnAddress bytes destinationBefore
      memoryFrame priorLog state ->
    exists segments after,
      IslaInstructionRun (7 * length bytes + 3) state.1 segments after.1 /\
      writeSuccessWithdrawalsConcretePc after = Some (bv_unsigned returnAddress) /\
      read_mem_list after.1.2.(seq_mem) (bv_unsigned destination)
        (N.of_nat (length bytes)) = Some bytes /\
      read_mem_list after.1.2.(seq_mem) (bv_unsigned source)
        (N.of_nat (length bytes)) = Some bytes /\
      writeSuccessMemoryRangeFrame (bv_unsigned destination) (length bytes)
        after.1.2.(seq_mem) memoryFrame /\
      after.2 = priorLog.

Definition writeSuccessOutputRecords
    (data size : bv 64) (bytes : list (bv 8))
    (records : list WriteSuccessWithdrawalsRecord) : Prop :=
  map fst records = writeOutputDescriptorEvents (data, size) /\
  writeSuccessWithdrawalsRecordedPayloads records = Some [bytes].

Definition Inv_write_output
    (data size returnAddress : bv 64) (bytes : list (bv 8))
    (priorLog : list WriteSuccessWithdrawalsRecord)
    (state : WriteSuccessWithdrawalsConcreteState) : Prop :=
  IslaInstructionBoundary state.1 /\
  writeSuccessWithdrawalsConcretePc state = Some 0x10190 /\
  state.1.1.(seq_regs) !! "x1" = Some (RVal_Bits returnAddress) /\
  state.1.1.(seq_regs) !! "x10" = Some (RVal_Bits data) /\
  state.1.1.(seq_regs) !! "x11" = Some (RVal_Bits size) /\
  bv_unsigned size = Z.of_nat (length bytes) /\
  read_mem_list state.1.2.(seq_mem) (bv_unsigned data)
    (N.of_nat (length bytes)) = Some bytes /\
  writeSuccessWithdrawalsInstructionTable state.1.2 /\
  writeSuccessTraceAssumptions state.1 /\
  set_Forall
    (fun address =>
      ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom state.1.2.(seq_mem)) /\
  state.2 = priorLog.

Definition block_write_output_statement : Prop :=
  forall data size returnAddress bytes priorLog state,
    Inv_write_output data size returnAddress bytes priorLog state ->
    exists segments after records,
      IslaInstructionRun 5 state.1 segments after.1 /\
      writeSuccessWithdrawalsConcretePc after = Some (bv_unsigned returnAddress) /\
      after.2 = priorLog ++ records /\
      writeSuccessOutputRecords data size bytes records.

Definition Inv_encoder_int
    (value sp returnAddress : bv 64) (scratch : list (bv 8))
    (memoryFrame : mem_map) (priorLog : list WriteSuccessWithdrawalsRecord)
    (state : WriteSuccessWithdrawalsConcreteState) : Prop :=
  IslaInstructionBoundary state.1 /\
  writeSuccessWithdrawalsConcretePc state = Some 0x15d10 /\
  state.1.1.(seq_regs) !! "x1" = Some (RVal_Bits returnAddress) /\
  state.1.1.(seq_regs) !! "x2" = Some (RVal_Bits sp) /\
  state.1.1.(seq_regs) !! "x10" = Some (RVal_Bits value) /\
  read_mem_list state.1.2.(seq_mem) (bv_unsigned sp - 16) 16%N = Some scratch /\
  islaMemoryRange (bv_unsigned sp - 16) 16 /\
  (forall location,
    bv_unsigned sp - 16 <= location < bv_unsigned sp ->
    is_Some (state.1.2.(seq_mem) !! Z_to_bv 64 location)) /\
  writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
    state.1.2.(seq_mem) memoryFrame /\
  writeSuccessWithdrawalsInstructionTable state.1.2 /\
  writeSuccessTraceAssumptions state.1 /\
  set_Forall
    (fun address =>
      ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom state.1.2.(seq_mem)) /\
  state.2 = priorLog.

Definition block_encoder_int_statement : Prop :=
  forall value sp returnAddress scratch memoryFrame priorLog state,
    Inv_encoder_int value sp returnAddress scratch memoryFrame priorLog state ->
    exists segments after records,
      IslaInstructionRun 15 state.1 segments after.1 /\
      writeSuccessWithdrawalsConcretePc after = Some (bv_unsigned returnAddress) /\
      read_mem_list after.1.2.(seq_mem) (bv_unsigned sp - 16) 8%N =
        Some (bv_to_little_endian 8 8 (bv_unsigned value)) /\
      writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
        after.1.2.(seq_mem) memoryFrame /\
      after.2 = priorLog ++ records /\
      writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8)
        (bv_to_little_endian 8 8 (bv_unsigned value)) records.

Definition Inv_1568c
    (args : WriteSuccessArgs WriteSuccessObservation)
    (sp : bv 64) (base : Z) (total : nat)
    (allBytes scratch encoderScratch : list (bv 8))
    (registerFrame : reg_map) (memoryFrame : mem_map)
    (priorLog : list WriteSuccessWithdrawalsRecord)
    (state : WriteSuccessWithdrawalsConcreteState) : Prop :=
  IslaInstructionBoundary state.1 /\
  writeSuccessWithdrawalsConcretePc state = Some 0x1568c /\
  state.1.1.(seq_regs) !! "x2" = Some (RVal_Bits sp) /\
  state.1.1.(seq_regs) !! "x8" = Some (RVal_Bits (Z_to_bv 64 base)) /\
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat total))) /\
  writeSuccessWithdrawalsRegisterFrame state.1.1.(seq_regs) registerFrame /\
  writeSuccessWithdrawalsMemoryFrame sp state.1.2.(seq_mem) memoryFrame /\
  writeSuccessWithdrawalsInstructionTable state.1.2 /\
  writeSuccessTraceAssumptions state.1 /\
  writeSuccessConcreteRepresentation
    (successDecoded WriteSuccessObservation args) state.1.2.(seq_mem)
    (successDecodedAddress WriteSuccessObservation args) /\
  total = length (observationWithdrawals
    (successDecoded WriteSuccessObservation args)) /\
  length allBytes = (48 * total)%nat /\
  read_mem_list state.1.2.(seq_mem) base
    (N.of_nat (length allBytes)) = Some allBytes /\
  read_mem_list state.1.2.(seq_mem) (bv_unsigned sp + 1744) 48%N = Some scratch /\
  read_mem_list state.1.2.(seq_mem) (bv_unsigned sp - 16) 16%N =
    Some encoderScratch /\
  bv_unsigned sp = successStackPointer WriteSuccessObservation args - 2000 /\
  bv_unsigned sp `mod` 16 = 0 /\
  0x20000000 <= bv_unsigned sp - 16 /\
  bv_unsigned sp + 1792 < 0x40000000 /\
  0x20000000 <= base /\
  base + Z.of_nat (length allBytes) < 0x40000000 /\
  islaMemoryRangesDisjoint base (length allBytes)
    (bv_unsigned sp - 16) 16 /\
  islaMemoryRangesDisjoint base (length allBytes)
    (bv_unsigned sp + 1744) 48 /\
  set_Forall
    (fun address =>
      ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom state.1.2.(seq_mem)) /\
  state.2 = priorLog.

Definition Inv_15694
    (args : WriteSuccessArgs WriteSuccessObservation)
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat)
    (withdrawal : WriteSuccessWithdrawalObservation)
    (allBytes prefix current suffix scratch encoderScratch : list (bv 8))
    (registerFrame : reg_map) (memoryFrame : mem_map)
    (priorLog : list WriteSuccessWithdrawalsRecord)
    (state : WriteSuccessWithdrawalsConcreteState) : Prop :=
  IslaInstructionBoundary state.1 /\
  state.1.1.(seq_pc_reg) = "PC" /\
  writeSuccessWithdrawalsConcretePc state = Some 0x15694 /\
  (exists oldX1, state.1.1.(seq_regs) !! "x1" = Some oldX1) /\
  state.1.1.(seq_regs) !! "x2" = Some (RVal_Bits sp) /\
  (exists oldX10, state.1.1.(seq_regs) !! "x10" = Some oldX10) /\
  (exists oldX11, state.1.1.(seq_regs) !! "x11" = Some oldX11) /\
  (exists oldX12, state.1.1.(seq_regs) !! "x12" = Some oldX12) /\
  (exists oldX15, state.1.1.(seq_regs) !! "x15" = Some oldX15) /\
  state.1.1.(seq_regs) !! "x8" = Some (RVal_Bits pointer) /\
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) /\
  state.1.1.(seq_regs) !! "x18" =
    Some (RVal_Bits (sp + BV 64 1768)%bv) /\
  writeSuccessWithdrawalsRegisterFrame state.1.1.(seq_regs) registerFrame /\
  writeSuccessWithdrawalsMemoryFrame sp state.1.2.(seq_mem) memoryFrame /\
  writeSuccessWithdrawalsInstructionTable state.1.2 /\
  writeSuccessTraceAssumptions state.1 /\
  writeSuccessConcreteRepresentation
    (successDecoded WriteSuccessObservation args) state.1.2.(seq_mem)
    (successDecodedAddress WriteSuccessObservation args) /\
  total = length (observationWithdrawals
    (successDecoded WriteSuccessObservation args)) /\
  total = (processed + S remaining)%nat /\
  nth_error (observationWithdrawals
    (successDecoded WriteSuccessObservation args)) processed = Some withdrawal /\
  allBytes = prefix ++ current ++ suffix /\
  length prefix = (48 * processed)%nat /\
  length current = 48%nat /\
  length suffix = (48 * remaining)%nat /\
  bv_unsigned sp = successStackPointer WriteSuccessObservation args - 2000 /\
  bv_unsigned sp `mod` 16 = 0 /\
  0x20000000 <= bv_unsigned sp - 16 /\
  bv_unsigned sp + 1792 < 0x40000000 /\
  0x20000000 <= base /\
  base + Z.of_nat (length allBytes) < 0x40000000 /\
  bv_unsigned pointer = base + 48 * Z.of_nat processed /\
  read_mem_list state.1.2.(seq_mem) base
    (N.of_nat (length allBytes)) = Some allBytes /\
  read_mem_list state.1.2.(seq_mem) (bv_unsigned pointer) 48%N = Some current /\
  writeSuccessWithdrawalMemory state.1.2.(seq_mem)
    (bv_unsigned pointer) withdrawal /\
  read_mem_list state.1.2.(seq_mem) (bv_unsigned sp + 1744) 48%N = Some scratch /\
  read_mem_list state.1.2.(seq_mem) (bv_unsigned sp - 16) 16%N =
    Some encoderScratch /\
  islaMemoryRangesDisjoint (bv_unsigned pointer) 48
    (bv_unsigned sp + 1744) 48 /\
  islaMemoryRangesDisjoint base (length allBytes)
    (bv_unsigned sp - 16) 16 /\
  islaMemoryRangesDisjoint base (length allBytes)
    (bv_unsigned sp + 1744) 48 /\
  set_Forall
    (fun address =>
      ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom state.1.2.(seq_mem)) /\
  state.2 = priorLog.

Definition Inv_156e8
    (args : WriteSuccessArgs WriteSuccessObservation)
    (sp pointer : bv 64) (base : Z) (total : nat)
    (allBytes : list (bv 8)) (registerFrame : reg_map)
    (memoryFrame : mem_map) (log : list WriteSuccessWithdrawalsRecord)
    (state : WriteSuccessWithdrawalsConcreteState) : Prop :=
  IslaInstructionBoundary state.1 /\
  writeSuccessWithdrawalsConcretePc state = Some 0x156e8 /\
  state.1.1.(seq_regs) !! "x2" = Some (RVal_Bits sp) /\
  state.1.1.(seq_regs) !! "x8" = Some (RVal_Bits pointer) /\
  state.1.1.(seq_regs) !! "x9" = Some (RVal_Bits (BV 64 0)) /\
  bv_unsigned pointer = base + 48 * Z.of_nat total /\
  writeSuccessWithdrawalsRegisterFrame state.1.1.(seq_regs) registerFrame /\
  writeSuccessWithdrawalsMemoryFrame sp state.1.2.(seq_mem) memoryFrame /\
  writeSuccessWithdrawalsInstructionTable state.1.2 /\
  writeSuccessTraceAssumptions state.1 /\
  writeSuccessConcreteRepresentation
    (successDecoded WriteSuccessObservation args) state.1.2.(seq_mem)
    (successDecodedAddress WriteSuccessObservation args) /\
  read_mem_list state.1.2.(seq_mem) base
    (N.of_nat (length allBytes)) = Some allBytes /\
  state.2 = log.

Definition block_1568c_guard_statement : Prop :=
  forall args sp base total allBytes scratch encoderScratch registerFrame
      memoryFrame priorLog state,
    Inv_1568c args sp base total allBytes scratch encoderScratch registerFrame
      memoryFrame priorLog state ->
    exists segments after,
      IslaInstructionRun 2 state.1 segments after.1 /\
      after.2 = priorLog /\
      match total with
      | O =>
          Inv_156e8 args sp (Z_to_bv 64 base) base 0 allBytes registerFrame
            memoryFrame priorLog after
      | S remaining =>
          exists withdrawal current suffix,
            nth_error (observationWithdrawals
              (successDecoded WriteSuccessObservation args)) 0 =
              Some withdrawal /\
            allBytes = current ++ suffix /\
            length current = 48%nat /\
            Inv_15694 args sp (Z_to_bv 64 base) base total 0 remaining
              withdrawal allBytes [] current suffix scratch encoderScratch
              registerFrame memoryFrame priorLog after
      end.

Lemma Inv_15694_current_shape args sp pointer base total processed remaining
    withdrawal allBytes prefix current suffix scratch encoderScratch
    registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  exists padding,
    length padding = 4%nat /\
    current = writeSuccessWithdrawalRawBytes withdrawal padding.
Proof.
  unfold Inv_15694. intros Hinv.
  have Hrepresentation : writeSuccessConcreteRepresentation
      (successDecoded WriteSuccessObservation args) state.1.2.(seq_mem)
      (successDecodedAddress WriteSuccessObservation args) by tauto.
  have Hnth : nth_error (observationWithdrawals
      (successDecoded WriteSuccessObservation args)) processed =
      Some withdrawal by tauto.
  have HcurrentRead : read_mem_list state.1.2.(seq_mem)
      (bv_unsigned pointer) 48%N = Some current by tauto.
  have HwithdrawalMemory : writeSuccessWithdrawalMemory state.1.2.(seq_mem)
      (bv_unsigned pointer) withdrawal by tauto.
  pose proof (writeSuccessRepresentationWithdrawalAt _ _ _ _ _
    Hrepresentation Hnth) as [Hvalid _].
  eapply writeSuccessWithdrawalRawBytesFromMemory; eassumption.
Qed.

(** This proposition is the binding nonfinal iteration interface. Its run
    evidence must come from the A2 segment proofs and the A3 coverage proofs. *)
Definition block_15694_iteration_statement : Prop :=
  forall args sp pointer base total processed r withdrawal nextWithdrawal
      allBytes prefix current nextCurrent nextSuffix scratch encoderScratch
      registerFrame memoryFrame priorLog state,
    Inv_15694 args sp pointer base total processed (S r) withdrawal
      allBytes prefix current (nextCurrent ++ nextSuffix) scratch encoderScratch
      registerFrame memoryFrame priorLog state ->
    nth_error (observationWithdrawals
      (successDecoded WriteSuccessObservation args)) (S processed) =
      Some nextWithdrawal ->
    length nextCurrent = 48%nat ->
    exists segments after records padding encoderAfter,
      IslaInstructionRun 410 state.1 segments after.1 /\
      after.2 = priorLog ++ records /\
      writeSuccessWithdrawalIterationRecords sp withdrawal records /\
      length padding = 4%nat /\
      current = writeSuccessWithdrawalRawBytes withdrawal padding /\
      read_mem_list after.1.2.(seq_mem) (bv_unsigned sp + 1744) 48%N =
        Some current /\
      Inv_15694 args sp (pointer + BV 64 48)%bv base total (S processed) r
        nextWithdrawal allBytes (prefix ++ current) nextCurrent nextSuffix
        current encoderAfter registerFrame memoryFrame
        (priorLog ++ records) after.

(** The last iteration reaches the post-loop boundary. *)
Definition block_15694_last_iteration_statement : Prop :=
  forall args sp pointer base total processed withdrawal allBytes prefix current
      scratch encoderScratch registerFrame memoryFrame priorLog state,
    Inv_15694 args sp pointer base total processed 0 withdrawal
      allBytes prefix current [] scratch encoderScratch registerFrame
      memoryFrame priorLog state ->
    exists segments after records padding,
      IslaInstructionRun 410 state.1 segments after.1 /\
      after.2 = priorLog ++ records /\
      writeSuccessWithdrawalIterationRecords sp withdrawal records /\
      length padding = 4%nat /\
      current = writeSuccessWithdrawalRawBytes withdrawal padding /\
      read_mem_list after.1.2.(seq_mem) (bv_unsigned sp + 1744) 48%N =
        Some current /\
      Inv_156e8 args sp (pointer + BV 64 48)%bv base total allBytes
        registerFrame memoryFrame (priorLog ++ records) after.

Print Assumptions writeSuccessWithdrawalIntegerBytesLength.
Print Assumptions writeSuccessWithdrawalAddressBytesLength.
Print Assumptions writeSuccessWithdrawalMemoryReads.
Print Assumptions read_mem_list_result_unique.
Print Assumptions writeSuccessWithdrawalRawBytesFromMemory.
Print Assumptions writeSuccessWithdrawalRawBytesLength.
Print Assumptions writeSuccessPublicBytesZToBv.
Print Assumptions writeSuccessWithdrawalFragmentsEncode.
Print Assumptions writeSuccessWithdrawalIterationRecordsEncode.
Print Assumptions writeSuccessZToBvAddOperational.
Print Assumptions writeSuccessWithdrawalsCounterDecrementOperational.
Print Assumptions writeSuccessWithdrawalsPointerAdvanceOperational.
Print Assumptions writeSuccessWithdrawalsSuffixAdvance.
Print Assumptions writeSuccessRepresentationWithdrawalAt.
Print Assumptions writeSuccessMemoryRangeFrameWrite.
Print Assumptions writeSuccessMemcpyMemoryUpdate.
Print Assumptions Inv_15694_current_shape.
